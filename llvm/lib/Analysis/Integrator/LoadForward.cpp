
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

//// Type definitions: the LF walker, its 2 derivatives, and PartialValueBuffer, a helper used by normal LF.

class LoadForwardWalker : public BackwardIAWalker {

  Value* LoadedPtr;
  uint64_t LoadSize;
  IntegrationAttempt* SourceCtx;
  AliasAnalysis* AA;
  TargetData* TD;

  ValCtx LoadPtrBase;
  int64_t LoadPtrOffset;

public:


  LoadForwardWalker(Instruction* Start, Value* Ptr, uint64_t Size, IntegrationAttempt* IA, AliasAnalysis* _AA, TargetData* _TD) 
    : BackwardIAWalker(Start, IA, true), LoadedPtr(Ptr), LoadSize(Size), SourceCtx(IA), AA(_AA), TD(_TD) {

    LoadPtrBase = GetBaseWithConstantOffset(LoadedPtr, IA, LoadPtrOffset);

  }
  virtual WalkInstructionResult walkInstruction(Instruction*, IntegrationAttempt*, void*);
  virtual bool shouldEnterCall(CallInst*, IntegrationAttempt*);
  virtual bool blockedByUnexpandedCall(CallInst*, IntegrationAttempt*);
  virtual WalkInstructionResult handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R) = 0;

};

class NormalLoadForwardWalker : public LoadForwardWalker {

public:

  PartialVal& inputPV;
  PartialVal resultPV;
  ValCtx FailureVC;
  std::string FailureCode;

  NormalLoadForwardWalker(Instruction* Start, Value* Ptr, uint64_t Size, IntegrationAttempt* IA, AliasAnalysis* _AA, TargetData* _TD, PartialVal& iPV) : LoadForwardWalker(Start, Ptr, Size, IA, _AA, _TD), inputPV(iPV) { }

  virtual WalkInstructionResult handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R);
  virtual void reachedTop();
  virtual bool mayAscendFromContext(IntegrationAttempt* IA);

};

class PBLoadForwardWalker : public LoadForwardWalker {

  bool OptimisticMode;
  const Type* originalType;

public:

  PointerBase Result;
  std::vector<std::string> OverdefReasons;
  std::vector<ValCtx> PredStores;

  PBLoadForwardWalker(Instruction* Start, Value* Ptr, uint64_t Size, IntegrationAttempt* IA, bool OM, const Type* OT, AliasAnalysis* _AA, TargetData* _TD) : LoadForwardWalker(Start, Ptr, Size, IA, _AA, _TD), OptimisticMode(OM), originalType(OT) { }

  virtual WalkInstructionResult handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R);
  void addPBDefn(PointerBase& NewPB);
  void setPBOverdef(std::string reason);
  virtual void reachedTop();
  virtual bool mayAscendFromContext(IntegrationAttempt* IA);

};

//// Implement generic LF

bool LoadForwardWalker::shouldEnterCall(CallInst* CI, IntegrationAttempt* IA) {

  switch(AA->getModRefInfo(CI, LoadedPtr, LoadSize, IA, SourceCtx, true)) {

  case AliasAnalysis::NoModRef:
  case AliasAnalysis::Ref:
    return false;
  default:
    return true;
  }

}

WalkInstructionResult LoadForwardWalker::walkInstruction(Instruction* I, IntegrationAttempt* IA, void*) {

  Value* Ptr;
  uint64_t PtrSize;

  WalkCtxs.insert(IA);

  if (StoreInst *SI = dyn_cast<StoreInst>(I)) {

    Ptr = SI->getPointerOperand();
    PtrSize = AA->getTypeStoreSize(SI->getOperand(0)->getType());
    // Fall through to alias analysis

  }
  else if (isa<AllocaInst>(I) || (isa<CallInst>(I) && extractMallocCall(I))) {
    
    if(LoadPtrBase == make_vc(I, IA)) {
      return handleAlias(I, IA, AliasAnalysis::MustAlias);
    }
    else
      return WIRContinue;

  }
  else if(MemIntrinsic* MI = dyn_cast<MemIntrinsic>(I)) {

    Ptr = MI->getDest();
    ConstantInt* CI = dyn_cast_or_null<ConstantInt>(IA->getConstReplacement(MI->getLength()));
    PtrSize = CI ? CI->getLimitedValue() : AliasAnalysis::UnknownSize;
    // Fall through to alias analysis

  }
  else if(CallInst* CI = dyn_cast<CallInst>(I)) {

    Function* CalledF;

    if(RealFile* RF = IA->tryGetReadFile(CI)) {
      
      Ptr = CI->getArgOperand(1);
      PtrSize = RF->readSize;
      // Fall through to alias analysis

    }
    else if(Function* CalledF = IA->getCalledFunction(CI)) {

      if(CalledF->getName() == "llvm.va_start" || CalledF->getName() == "llvm.va_copy") {

	Ptr = CI->getArgOperand(0);
	PtrSize = 24;

      }
      else {

	return WIRContinue;

      }

    }
    else {

      return WIRContinue;

    }

  }
  else {

    return WIRContinue;

  }

  AliasAnalysis::AliasResult R = AA->aliasHypothetical(make_vc(LoadedPtr, SourceCtx), LoadSize, make_vc(Ptr, IA), PtrSize, true);
  if(R == AliasAnalysis::NoAlias)
    return WIRContinue;

  return handleAlias(I, IA, R);

}

//// Implement guts of PartialVal:

PartialVal::initByteArray(uint64_t nbytes) {

  type = PVByteArray;

  uint64_t nqwords = (nbytes + 7) / 8;
  partialBuf = new uint64_t[nqwords];

  if(!partialValidBuf) {

    partialValidBuf = new bool[nbytes];
    for(uint64_t i = 0; i < nbytes; ++i)
      partialValidBuf[i] = false;

  }

  partialBufBytes = nbytes;
  loadFinished = false;

}

PartialVal::PartialVal(uint64_t nbytes) {

  initByteArray(nbytes);

}

PartialVal::operator=(const PartialVal& Other) {

  type = Other.type;
  isVarargTainted = Other.isVarargTainted;
  TotalVC = Other.TotalVC;
  C = Other.C;
  ReadOffset = Other.ReadOffset;
  
  if(Other.partialBuf) {

    partialBuf = new uint64_t[(Other.partialBufBytes + 7) / 8];
    memcpy(partialBuf, Other.partialBuf, Other.partialBufBytes);

  }

  if(Other.partialValidBuf) {

    partialValidBuf = new bool[Other.partialBufBytes];
    memcpy(partialValidBuf, Other.partialValidBuf, Other.partialBufBytes);
    
  }

  partialBufBytes = Other.partialBufBytes;
  loadFinished = Other.loadFinished;

}

PartialBuf::PartialBuf(const PartialBuf& Other) {

  (*this) = Other;

}

PartialVal::~PartialVal() {

  if(partialBuf)
    delete[] partialBuf;
  if(partialValidBuf)
    delete[] partialValidBuf;

}

bool* PartialVal::getValidArray(uint64_t nbytes) {

  if(!partialValidBuf)
    partialValidBuf = new bool[nbytes];

  return partialValidBuf;

}

static uint64_t markPaddingBytes(bool* pvb, const Type* Ty, TargetData* TD) {

  uint64_t marked = 0;

  if(const StructType* STy = dyn_cast<StructType>(Ty)) {
    
    const StructLayout* SL = TD->getStructLayout(STy);
    if(!SL) {
      LPDEBUG("Couldn't get struct layout for type " << *STy << "\n");
      return 0;
    }

    uint64_t EIdx = 0;
    for(StructType::element_iterator EI = STy->element_begin(), EE = STy->element_end(); EI != EE; ++EI, ++EIdx) {

      marked += markPaddingBytes(&(pvb[SL->getElementOffset(EIdx)]), *EI);
      uint64_t ThisEStart = SL->getElementOffset(EIdx);
      uint64_t ESize = (TD->getTypeSizeInBits(*EI) + 7) / 8;
      uint64_t NextEStart = (EIdx + 1 == STy->getNumElements()) ? SL->getSizeInBytes() : SL->getElementOffset(EIdx + 1);
      for(uint64_t i = ThisEStart + ESize; i < NextEStart; ++i, ++marked) {
	
	pvb[i] = true;

      }

    }

  }
  else if(const ArrayType* ATy = dyn_cast<ArrayType>(Ty)) {

    uint64_t ECount = ATy->getNumElements();
    const Type* EType = ATy->getElementType();
    uint64_t ESize = (TD->getTypeSizeInBits(EType) + 7) / 8;

    uint64_t Offset = 0;
    for(uint64_t i = 0; i < ECount; ++i, Offset += ESize) {

      marked += markPaddingBytes(&(pvb[Offset]), EType);

    }

  }

  return marked;

}

bool PartialVal::isComplete() {

  return isTotal() || isPartial() || loadFinished;

}

void PartialVal::convertToBytes(uint64_t size) {

  PartialVal conv(size);
  conv.combineWith(*this);

  (*this) = conv;

}

bool PartialVal::combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t LoadSize, TargetData* TD, std::string& error) {

 if(isEmpty()) {

   if(FirstDef == 0 && (FirstNotDef - FirstDef == LoadSize)) {

     *this = Other;
     return true;

   }
   else {

     // Transition to bytewise load forwarding: this value can't satisfy
     // the entire requirement. Turn into a PVByteArray and fall through.
     initByteArray(LoadSize);

   }

 }

 assert(isByteArray());

 if(Other.isTotal()) {

   Constant* TotalC = dyn_cast<Constant>(PV.TotalVC.first);
   if(!TotalC) {
     //LPDEBUG("Unable to use total definition " << itcache(PV.TotalVC) << " because it is not constant but we need to perform byte operations on it\n");
     error = "PP2";
     return false;
   }
   Other.C = TotalC;
   Other.ReadOffset = 0;
   Other.Type = PVPartial;

 }

 DEBUG(dbgs() << "This store can satisfy bytes (" << Other.FirstDef << "-" << Other.FirstNotDef << "] of the source load\n");

 // Store defined some of the bytes we need! Grab those, then perhaps complete the load.

 unsigned char* tempBuf;

 if(Other.isPartial()) {

   tempBuf = (unsigned char*)alloca(Other.FirstNotDef - Other.FirstDef);
   // ReadDataFromGlobal assumes a zero-initialised buffer!
   memset(tempBuf, 0, FirstNotDef - FirstDef);

   if(!ReadDataFromGlobal(Other.C, Other.ReadOffset, tempBuf, Other.FirstNotDef - Other.FirstDef, *TD)) {
     LPDEBUG("ReadDataFromGlobal failed; perhaps the source " << *(Other.C) << " can't be bitcast?\n");
     error = "RDFG";
     return false;
   }

 }
 else {

   tempBuf = (unsigned char*)Other.partialBuf;

 }

 else {

   // Avoid rewriting bytes which have already been defined
   for(uint64_t i = 0; i < (FirstNotDef - FirstDef); ++i) {
     if(partialBufValid[FirstDef + i]) {
       continue;
     }
     else {
       partialBuf[FirstDef + i] = tempBuf[i];
     }
   }

 }

 loadFinished = true;
 // Meaning of the predicate: stop at the boundary, or bail out if there's no more setting to do
 // and there's no hope we've finished.
 for(uint64_t i = 0; i < LoadSize && (loadFinished || i < Other.FirstNotDef); ++i) {

   if(i >= Other.FirstDef && i < Other.FirstNotDef) {
     partialBufValid[i] = true;
   }
   else {
     if(!partialBufValid[i]) {
       loadFinished = false;
     }
   }

 }

 return true;

}

//// Implement Normal LF:

bool NormalLoadForwardWalker::addPartialVal(PartialVal& PV, std::string& error, Instruction* I, IntegrationAttempt* IA, uint64_t FirstDef, uint64_t FirstNotDef) {

  PartialVal valSoFar(inputPV);
  if(!valSoFar.combineWith(PV, FirstDef, FirstNotDef, LoadSize, error))
    return false;

  if(!valSoFar.isComplete()) {

    valSoFar = IA->tryForwardLoadSubquery(I, LoadedPtr, SourceCtx, LoadSize, valSoFar);
    if(valSoFar.isEmpty()) {

      error = "PartSQ";
      return false;

    }

  }

  if((!resultPV.isEmpty()) && (resultPV != valSoFar)) {
      
    error = "Clash";
    return false;

  }
  else {

    resultPV = valSoFar;

  }

}

bool NormalLoadForwardWalker::getMIOrReadValue(Instruction* I, IntegrationAttempt* IA, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, bool* validBytes, PartialVal& NewPV, std::string& error) {

  if (MemIntrinsic *DepMI = dyn_cast<MemIntrinsic>(I)) {

    if(MemSetInst* MSI = dyn_cast<MemSetInst>(I))
      return IA->getMemsetPV(MSI, FirstNotDef - FirstDef, NewPV, error);
    else
      return IA->getMemcpyPV(cast<MemTransferInst>(I), FirstDef, FirstNotDef, ReadOffset, LoadSize, validBytes, NewPV, error);

  }
  else {

    CallInst* CI = cast<CallInst>(I);
    Function* F = IA->getCalledFunction(CI);
    if(F->getName() == "read") {
      
      return IA->getReadPV(CI, FirstNotDef - FirstDef, ReadOffset, NewPV, error);

    }
    else if(F->getName() == "llvm.va_start") {

      return IA->getVaStartPV(CI, ReadOffset, NewPV, error);

    }
    else {

      assert(F->getName() == "llvm.va_copy");
      return IA->getVaCopyPV(CI, FirstDef, FirstNotDef, ReadOffset, LoadSize, validBytes, NewPV, error);

    }

  }

}

#define NLFWFail(Code) do { FailureCode = Code; FailureVC = make_vc(I, IA); return WIRStopWholeWalk; } while(0);

WalkInstructionResult NormalLoadForwardWalker::handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R) { 

  PartialVal NewPV;
  uint64_t FirstDef, FirstNotDef, ReadOffset;
  
  if(R == AliasAnalysis::MustAlias) {

    FirstDef = 0; FirstNotDef = LoadSize; ReadOffset = 0;

    if(StoreInst* SI = dyn_cast<StoreInst>(SI)) {

      ValCtx NewVC = IA->getReplacement(SI->getOperand(0));
      if(NewVC != make_vc(SI, IA))
	NewPV = PartialVal::getTotal(NewVC);
      else {

	// Defined by store with no value
	NLFWFail("DNS");

      }

    }
    else if(isa<AllocaInst>(I) || (isa<CallInst>(I) && extractMallocCall(I))) {

      NewPV = PartialVal::getTotal(Constant::getNullValue(I->getType()));

    }
    else {

      std::string error;
      if(!IA->getMIOrReadValue(I, 0, std::min(LoadSize, PtrSize), 0, LoadSize, NewPV, error)) {

	// Memcpy, memset or read failed
	NLFWFail(error);

      }
      // Else fall through

    }

  }
  else {
    
    // MayAlias

    int64_t WriteOffset;
    ValCtx WriteBase = GetBaseWithConstantOffset(Ptr, IA, WriteOffset);
    if(IA->GetDefinedRange(LoadPtrBase, LoadPtrOffset, LoadSize,
			   WriteBase, WriteOffset, PtrSize,
			   FirstDef, FirstNotDef, ReadOffset)) {

      if(StoreInst* SI = dyn_cast<StoreInst>(SI)) {

	Constant* StoreC = IA->getConstReplacement(SI->getValueOperand());
	if(!StoreC) {

	  // Partial defn by store of non-const
	  NLFWFail("NCS");

	}
	else {

	  NewPV = PartialVal::getPartial(StoreC, ReadOffset);

	}

      }
      else {

	std::string error;
	if(!getMIOrReadValue(I, IA, FirstDef, FirstNotDef, ReadOffset, LoadSize, NewPV, error)) {
	
	  // Memset, memcpy or read failed
	  NLFWFail(error);

	}
	// Else fall through
	
      }

    }
    else {

      // We don't know enough about one or other pointer, must assume this write
      // trashes the entire value.
      NLFWFail("C");

    }

  }

  std::string error;
  if(!addPartialVal(NewPV, error, I, IA, FirstDef, FirstNotDef)) {
    // Couldn't perform some implicit cast, or encountered a conflict
    NLFWFail(error);
  }

  return WIRStopThisPath;

}

bool NormalLoadForwardWalker::blockedByUnexpandedCall(CallInst* CI, IntegrationAttempt* IA) {

  FailureCode = "UEC";
  FailureVC = make_vc(CI, IA);
  return true;

}

bool NormalLoadForwardWalker::reachedTop() {

  if(GlobalVariable* GV = dyn_cast<GlobalVariable>(LoadPtrBase.first)) {
	    
    if(GV->hasDefinitiveInitializer()) {

      LPDEBUG("Load using global initialiser " << itcache(*(GV->getInitializer())) << "\n");

      Constant* GVC = GV->getInitializer();
      uint64_t GVCSize = (TD->getTypeSizeInBits(GVC->getType()) + 7) / 8;
      uint64_t FirstNotDef = std::min(GVCSize - LoadPtrOffset, LoadSize);
      LPDEBUG("Read offset is " << LoadPtrOffset << "\n");
      if(!addPartialVal(PartialVal::getPartial(0, FirstNotDef, GVC, LoadPtrOffset))) {

	FailureVC = make_vc(GV, 0);
	FailureCode = "Top";
      
      }
      else {

	return true;

      }

    }

  }

  return false;

}

bool NormalLoadForwardWalker::mayAscendFromContext(IntegrationAttempt* IA) {

  if(IA == LoadPtrBase.second) {
    
    FailureVC = make_vc(IA->getEntryInstruction(), IA);
    FailureCode = "Scope";
    return false;

  }
    
  return true;

}

//// Implement PBLF:

void PBLoadForwardWalker::addPBDefn(PointerBase& NewPB) {
  bool WasOverdef = Result.Overdef;
  Result.merge(NewPB);
  if(Result.Overdef && (!WasOverdef) && (!NewPB.Overdef))
    OverdefReasons.push_back("Fan-in");
}

void PBLoadForwardWalker::setPBOverdef(std::string reason) {
  OverdefReasons.push_back(reason);
  Result = PointerBase::getOverdef();
}

bool PBLoadForwardWalker::PBIsViable() {
  return PBOptimistic || ((!PB.Overdef) && PB.Values.size() > 0);
}

WalkInstructionResult PBLoadForwardWalker::handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R) {

  // If we're in the optimistic phase, ignore anything but the following:
  // * Defining stores with an associated PB
  // * Defining alloca instructions
  // Unexpanded calls are also significant but these are caught by blockedByUnexpandedCall.

  if(isa<StoreInst>(I)) {

    PredStores.push_back(make_vc(I, IA));

  }

  if(OptimisticMode) {

    bool ignore = true;

    if(R == AliasAnalysis::MustAlias) {
      if(isa<AllocaInst>(I))
	ignore = false;
      else if(StoreInst* SI = dyn_cast<StoreInst>(I)) {
	PointerBase ResPB;
	if(IA->getPointerBase(SI->getOperand(0), ResPB, SI) || !IA->isUnresolved(SI->getOperand(0)))
	  ignore = false;
      }
    }
      
    if(ignore)
      return WIRContinue;

  }

  if(R == AliasAnalysis::MustAlias) {

    if(StoreInst* SI = dyn_cast<StoreInst>(I)) {
      PointerBase NewPB;
      if(IA->getPointerBase(SI->getOperand(0), NewPB, SI)) {
	prout << "Add PB ";
	printPB(prout, NewPB);
	prout << "\n";
	// Actually addPBDefn will do the merge anyhow, but we annotate the LFA with a reason.
	if(NewPB.Overdef) {
	  std::string RStr;
	  raw_string_ostream RSO(RStr);
	  RSO << "DO " << IA->itcache(make_vc(I, IA), true);
	  RSO.flush();
	  setPBOverdef(RStr);
	}
	else {
	  addPBDefn(NewPB);
	}
      }
      else {
	// Try to find a concrete definition, since the concrete defns path is more advanced.
	// Remember the PB sets only take constants or identified underlying objects.
	ValCtx Repl = IA->getReplacement(SI->getOperand(0));
	ValCtx ReplUO;
	if(Repl.second)
	  ReplUO = Repl.second->getUltimateUnderlyingObject(Repl.first);
	else
	  ReplUO = Repl;
	if(isa<Constant>(ReplUO.first) || isGlobalIdentifiedObject(ReplUO)) {
	  PointerBase PB = PointerBase::get(ReplUO);
	  prout << "Add PB ";
	  printPB(prout, PB);
	  prout << "\n";
	  addPBDefn(PB);
	}
	else {
	  prout << "Overdef (1) on " << itcache(Repl) << " / " << itcache(ReplUO) << "\n";
	  std::string RStr;
	  raw_string_ostream RSO(RStr);
	  RSO << "DN " << itcache(make_vc(I, IA), true);
	  RSO.flush();
	  setPBOverdef(RStr);
	}
      }
    }
    else if(AllocaInst* AI = dyn_cast<AllocaInst>(I)) {

      // Allocas have no defined initial value, so just assume null.
      PointerBase NewPB = PointerBase::get(const_vc(Constant::getNullValue(AI->getType())));
      addPBDefn(NewPB);

    }
    else {
      prout << "Overdef (2) on " << itcache(*(I)) << "\n";
      std::string RStr;
      raw_string_ostream RSO(RStr);
      RSO << "DNS " << itcache(make_vc(I, IA), true);
      RSO.flush();
      setPBOverdef(RStr);
    }

  }
  else {

    // MayAlias

    Instruction* Inst = I;
    std::string RStr;
    raw_string_ostream RSO(RStr);
    RSO << "C " << itcache(make_vc(Inst, IA), true);
    RSO.flush();
    setPBOverdef(RStr);

  }

  if(Result.Overdef)
    return WIRStopWholeWalk;
  else
    return WIRStopThisPath;
  
}

bool PBLoadForwardWalker::reachedTop() {

  if(GlobalVariable* GV = dyn_cast<GlobalVariable>(LoadPtrBase.first)) {
	    
    if(GV->hasDefinitiveInitializer()) {
	
      Constant* GVC = GV->getInitializer();
      uint64_t GVCSize = (TD->getTypeSizeInBits(GVC->getType()) + 7) / 8;
      uint64_t FirstNotDef = std::min(GVCSize - LoadPtrOffset, LoadSize);
      if(FirstNotDef == LoadSize) {

	ValCtx FieldVC = extractAggregateMemberAt(GVC, LoadPtrOffset, originalType, LoadSize, TD);
	if(FieldVC != VCNull) {
	  
	  assert(isa<Constant>(FieldVC.first));
	  PointerBase NewPB = PointerBase::get(FieldVC);
	  addPBDefn(NewPB);
	  return true;
	  
	}

      }

    }
    
  }

  setPBOverdef("Reached top");

  return false;

}

bool PBLoadForwardWalker::blockedByUnexpandedCall(CallInst* CI, IntegrationAttempt* IA) {

  std::string RStr;
  raw_string_ostream RSO(RStr);
  RSO << "UEC " << IA->itcache(make_vc(CI, IA), true);
  RSO.flush();  
  setPBOverdef(RStr);
  return true;

}

bool PBLoadForwardWalker::mayAscendFromContext(IntegrationAttempt* IA) {

  if(IA == LoadPtrBase.second) {
    
    setPBOverdef("Scope");
    return false;

  }
    
  return true;

}

//// Conventional LF interface:

ValCtx IntegrationAttempt::getWalkerResult(LoadForwardWalker& Walker, const Type* TargetType) {

  PartialVal& PV = Walker.resultPV;

  // Try to use an entire value:
  if(PV.isTotal()) {

    ValCtx Res = PV.TotalVC;
    const Type* sourceType = Res.first->getType();
    if(Res.isVaArg() || allowTotalDefnImplicitCast(sourceType, TargetType)) {
      return Res;
    }
    else if(allowTotalDefnImplicitPtrToInt(sourceType, TargetType, TD)) {
      LPDEBUG("Accepting " << itcache(Res) << " implicit ptrtoint to " << *(sourceType) << "\n");
      Res = getAsPtrAsInt(Res, TargetType);
      return Res;
    }

  }

  // Otherwise try to use a sub-value:
  if(PV.isTotal() || PV.isPartial()) {

    // Try to salvage a total definition from a partial if this is a load clobbered by a store
    // of a larger aggregate type. This is to permit pointers and other non-constant forwardable values
    // to be moved about. In future ValCtx needs to get richer to become a recursive type like
    // ConstantStruct et al.

    // Note that because you can't write an LLVM struct literal featuring a non-constant,
    // the only kinds of pointers this permits to be moved around are globals, since they are constant pointers.
    Constant* SalvageC = PV.isTotal() ? dyn_cast<Constant>(PV.TotalVC.first) : PV.C;
    uint64_t LoadSize = (TD->getTypeSizeInBits(TargetType) + 7) / 8;

    if(SalvageC && (PV.isTotal() || (PV.FirstDef == 0 && PV.FirstNotDef == LoadSize))) {

      uint64_t Offset = PV.isTotal() ? 0 : PV.ReadOffset;
      return extractAggregateMemberAt(SalvageC, Offset, targetType, LoadSize, TD);

    }

  }

  if(containsPointerTypes(TargetType))
    return VCNull;

  // Finally build it from bytes.
  PV.convertToBytes(LoadSize);
  assert(PV.isByteArray());

  return const_vc(constFromBytes(PV.partialBuf, TargetType, TD));

}

bool IntegrationAttempt::tryResolveLoadFromConstant(LoadInst* LoadI, ValCtx& Result) {

  // A special case: loading from a symbolic vararg:

  ValCtx LPtr = getReplacement(LoadI->getPointerOperand());
  LPtr = make_vc(LPtr.first->stripPointerCasts(), LPtr.second, LPtr.offset, LPtr.va_arg);

  if(LPtr.isVaArg() && LPtr.getVaArgType() != ValCtx::va_baseptr) {
    
    LPtr.second->getVarArg(LPtr.va_arg, Result);
    LPDEBUG("va_arg " << itcache(LPtr) << " " << LPtr.va_arg << " yielded " << itcache(Result) << "\n");
    
    if(Result.first && Result.first->getType() != LoadI->getType()) {
      if(!(Result.first->getType()->isPointerTy() && LoadI->getType()->isPointerTy()))
	Result = VCNull;
    }

    // Is this va_arg read out of bounds or wrong type?
    if(Result == VCNull)
      return true;

    if(!shouldForwardValue(Result))
      Result = VCNull;

    return true;

  }

  int64_t Offset = 0;
  ValCtx Base = GetBaseWithConstantOffset(LoadI->getPointerOperand(), this, Offset);

  if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(Base.first)) {
    if(GV->isConstant()) {

      uint64_t LoadSize = (TD->getTypeSizeInBits(LoadI->getType()) + 7) / 8;
      const Type* FromType = GV->getInitializer()->getType();
      uint64_t FromSize = (TD->getTypeSizeInBits(FromType) + 7) / 8;

      if(Offset < 0 || Offset + LoadSize > FromSize) {
	Result = VCNull;
	return true;
      }

      Result = extractAggregateMemberAt(GV->getInitializer(), Offset, LoadI->getType(), LoadSize, TD);
      if(Result != VCNull)
	return true;

      int64_t CSize = TD->getTypeAllocSize(GV->getInitializer()->getType());
      if(CSize < Offset) {

	LPDEBUG("Can't forward from constant: read from global out of range\n");
	Result = VCNull;
	return true;

      }

      unsigned char* buf = (unsigned char*)alloca(LoadSize);
      memset(buf, 0, LoadSize);
      if(ReadDataFromGlobal(GV->getInitializer(), Offset, buf, LoadSize, *TD)) {

	Result = const_vc(constFromBytes(buf, LoadI->getType(), TD));
	return true;

      }
      else {

	LPDEBUG("ReadDataFromGlobal failed\n");
	Result = VCNull;
	return true;

      }

    }
  }

  // Check whether pursuing alises is pointless -- this is true if we're certain that the ultimate underlying object is a constant.
  // If it is, our attempt above was likely foiled only by uncertainty about the specific bit of the constant (e.g. index within a const string)
  // and the only way the situation will improve is if those offsets become clear.
  // Note this isn't as redundant as it looks, since GUUO doesn't give up when it hits an uncertain GEP,
  // unlike GBWCO above.

  ValCtx Ultimate = getUltimateUnderlyingObject(LoadI->getPointerOperand());

  if(GlobalVariable* GV = dyn_cast<GlobalVariable>(Ultimate.first)) {

    if(GV->isConstant()) {
      LPDEBUG("Load cannot presently be resolved, but is rooted on a constant global. Abandoning search\n");
      Result = VCNull;
      return true;
    }

  }

  return false;

}

PartialVal IntegrationAttempt::tryForwardLoadSubquery(Instruction* StartInst, Value* LoadPtr, Integrationattempt* LoadCtx, uint64_t LoadSize, PartialValueBuf& ResolvedSoFar) {

  NormalLoadForwardWalker Walker(StartInst, LoadPtr, LoadSize, LoadCtx, AA, TD, &ResolvedSoFar, true);
  Walker.walk();
  return Walker.ResultPartialBuf;

}

ValCtx IntegrationAttempt::tryForwardLoad(Instruction* StartInst, Value* LoadPtr, const Type* TargetType, uint64_t LoadSize) {

  bool mayBuildFromBytes = !containsPointerTypes(TargetType);

  NormalLoadForwardWalker Walker(StartInst, LoadPtr, LoadSize, this, AA, TD, 0, mayBuildFromBytes);

  bool* validBytes = Walker.getValidBuf();
  markPaddingBytes(TargetType, validBytes, TD);

  Walker.walk();

  if(Walker.FailureVC != VCNull)
    return VCNull;

  ValCtx Res = getWalkerResult(Walker, TargetType);

  if(Res != VCNull && !shouldForwardValue(Res))
    return VCNull;

  return Res;

}

PartialVal IntegrationAttempt::tryForwardLoadTypeless(Instruction* StartInst, Value* LoadPtr, uint64_t LoadSize, bool* alreadyValidBytes) {

  NormalLoadForwardWalker Walker(StartInst, LoadPtr, LoadSize, this, AA, TD);
  bool* validBytes = Walker.getValidBuf();
  memcpy(validBytes, alreadyValidBytes, sizeof(bool) * LoadSize);

  Walker.walk();

  if(Walker.FailureVC != VCNull)
    return PVNull;

  return Walker.ResultPV;

}

ValCtx IntegrationAttempt::tryForwardLoad(LoadInst* LI) {

  ValCtx ConstResult;
  if(tryResolveLoadFromConstant(LoadI, ConstResult))
    return ConstResult;

  return tryForwardLoad(LI, LI->getPointerOperand(), AA->getTypeStoreSize(LI->getOperand(0)->getType()), LI->getType());

}

//// PBLF Interface

std::string IntegrationAttempt::describePBWalker(PBLoadForwardWalker& Walker) {
  
  std::string out;
  raw_string_ostream RSO(out);
  
  if(Walker.Result.Overdef) {
    for(unsigned i = 0; i < Walker.OverdefReasons.size(); ++i) {
      if(i != 0)
	RSO << ", ";
      RSO << Walker.OverdefReasons[i];
    }
  }  
  else if(Walker.Result.Values.size() == 0) {
    
    RSO << "No defn";
    
  }
  else {
    
    printPB(RSO, Walker.Result, true);
    
  }
    
  return out;
    
}
  
// Do load forwarding, possibly in optimistic mode: this means that
// stores that def but which have no associated PB are optimistically assumed
// to be compatible with anything, the same as the mergepoint logic above
// when finalise is false. When finalise = true this is just like normal load
// forwarding operating in PB mode.
bool IntegrationAttempt::tryForwardLoadPB(LoadInst* LI, bool finalise, PointerBase& NewPB) {

  PBLoadForwardWalker Walker(LI, LI->getOperand(0), AA->getTypeStoreSize(LI->getOperand(0)->getType()),
			     this, !finalise, LI->getType(), AA, TD);

  bool verbose = false;

  if(verbose) {

    errs() << "=== START LFA for " << itcache(*LI) << "\n";

    IntegrationAttempt* PrintCtx = this;
    while(PrintCtx) {
      errs() << PrintCtx->getShortHeader() << ", ";
      PrintCtx = PrintCtx->parent;
    }
    errs() << "\n";

  }

  struct timespec start;
  clock_gettime(CLOCK_REALTIME, &start);

  Walker.walk();

  struct timespec end;
  clock_gettime(CLOCK_REALTIME, &end);
  
  if(time_diff(start, end) > 0.1) {
    errs() << "TFLPB took " << time_diff(start, end) << " (ctxs: " << Attempt.TraversedCtxs.size() << ")\n";
    /*
    for(unsigned i = 0; i < Attempt.TraversedCtxs.size(); ++i) {

      errs() << Attempt.TraversedCtxs[i]->getShortHeader() << "\n";

    }
    */
  }

  for(std::vector<ValCtx>::iterator it = Walker.PredStores.begin(), it2 = Walker.PredStores.end(); it != it2; ++it) {

    // Register our dependency on various instructions:
    if(!it->second)
      continue;

    if(StoreInst* SI = dyn_cast<StoreInst>(it->first)) {
      
      it->second->addMemWriterEffect(SI, LI, this);
      
    }

  }

  if(verbose)
    errs() << "=== END LFA\n";

  if(!finalise)
    optimisticForwardStatus[LI] = describePBWalker(Walker);
  else
    pessimisticForwardStatus[LI] = describePBWalker(Walker);
    
  if(Walker.Result.Values.size() == 0 && !Walker.Result.Overdef)
    return false;

  NewPB = Walker.Result;
  return true;

}
