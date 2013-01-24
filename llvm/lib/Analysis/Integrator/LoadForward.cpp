
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

//// Type definitions: the LF walker, and its 2 derivatives for normal and PB LF.

namespace llvm {

class LoadForwardWalker : public BackwardIAWalker {

protected:

  ValCtx LoadedPtr;
  uint64_t LoadSize;
  AliasAnalysis* AA;
  TargetData* TD;

  ValCtx LoadPtrBase;
  int64_t LoadPtrOffset;

public:


  LoadForwardWalker(Instruction* Start, IntegrationAttempt* StartIA, ValCtx Ptr, uint64_t Size, AliasAnalysis* _AA, TargetData* _TD) 
    : BackwardIAWalker(Start, StartIA, true), LoadedPtr(Ptr), LoadSize(Size), AA(_AA), TD(_TD) {

    LoadPtrOffset = 0;
    LoadPtrBase = GetBaseWithConstantOffset(Ptr.first, Ptr.second, LoadPtrOffset);

  }
  virtual WalkInstructionResult walkInstruction(Instruction*, IntegrationAttempt*, void*);
  virtual bool shouldEnterCall(CallInst*, IntegrationAttempt*);
  virtual WalkInstructionResult handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R, Value* Ptr, uint64_t PtrSize) = 0;

};

class NormalLoadForwardWalker : public LoadForwardWalker {

public:

  PartialVal& inputPV;
  PartialVal resultPV;
  ValCtx FailureVC;
  std::string FailureCode;

  NormalLoadForwardWalker(Instruction* Start, IntegrationAttempt* StartIA, ValCtx Ptr, uint64_t Size, AliasAnalysis* _AA, TargetData* _TD, PartialVal& iPV) : LoadForwardWalker(Start, StartIA, Ptr, Size, _AA, _TD), inputPV(iPV), resultPV(PVNull), FailureVC(VCNull) { }

  virtual WalkInstructionResult handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R, Value* Ptr, uint64_t PtrSize);
  virtual bool reachedTop();
  virtual bool mayAscendFromContext(IntegrationAttempt* IA);
  bool addPartialVal(PartialVal& PV, std::string& error, Instruction* I, IntegrationAttempt* IA, uint64_t FirstDef, uint64_t FirstNotDef, bool maySubquery);
  bool getMIOrReadValue(Instruction* I, IntegrationAttempt* IA, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, PartialVal& NewPV, std::string& error);
  virtual bool blockedByUnexpandedCall(CallInst*, IntegrationAttempt*);
  bool* getValidBuf();

};

class PBLoadForwardWalker : public LoadForwardWalker {

  bool OptimisticMode;
  const Type* originalType;

public:

  PointerBase Result;
  std::vector<std::string> OverdefReasons;
  std::vector<ValCtx> PredStores;

  PBLoadForwardWalker(Instruction* Start, IntegrationAttempt* StartIA, ValCtx Ptr, uint64_t Size, bool OM, const Type* OT, AliasAnalysis* _AA, TargetData* _TD) : LoadForwardWalker(Start, StartIA, Ptr, Size, _AA, _TD), OptimisticMode(OM), originalType(OT) { }

  virtual WalkInstructionResult handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R, Value* Ptr, uint64_t PtrSize);
  void addPBDefn(PointerBase& NewPB);
  void setPBOverdef(std::string reason);
  virtual bool reachedTop();
  virtual bool mayAscendFromContext(IntegrationAttempt* IA);
  virtual bool blockedByUnexpandedCall(CallInst*, IntegrationAttempt*);

};

}

//// Implement generic LF

bool LoadForwardWalker::shouldEnterCall(CallInst* CI, IntegrationAttempt* IA) {

  switch(AA->getModRefInfo(CI, LoadedPtr.first, LoadSize, IA, LoadedPtr.second, true)) {

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

  if (StoreInst *SI = dyn_cast<StoreInst>(I)) {

    Ptr = SI->getPointerOperand();
    PtrSize = AA->getTypeStoreSize(SI->getOperand(0)->getType());
    // Fall through to alias analysis

  }
  else if (isa<AllocaInst>(I) || (isa<CallInst>(I) && extractMallocCall(I))) {
    
    if(LoadPtrBase == make_vc(I, IA)) {
      return handleAlias(I, IA, AliasAnalysis::MustAlias, I, LoadSize);
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

    if(ReadFile* RF = IA->tryGetReadFile(CI)) {
      
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

  AliasAnalysis::AliasResult R = AA->aliasHypothetical(LoadedPtr, LoadSize, make_vc(Ptr, IA), PtrSize, true);
  if(R == AliasAnalysis::NoAlias)
    return WIRContinue;

  return handleAlias(I, IA, R, Ptr, PtrSize);

}

//// Implement guts of PartialVal:

void PartialVal::initByteArray(uint64_t nbytes) {

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

PartialVal::PartialVal(uint64_t nbytes) : isVarargTainted(false), TotalVC(VCNull), C(0), ReadOffset(0), partialValidBuf(0)  {

  initByteArray(nbytes);

}

PartialVal& PartialVal::operator=(const PartialVal& Other) {

  if(partialBuf) {
    delete[] partialBuf;
    partialBuf = 0;
  }
  if(partialValidBuf) {
    delete[] partialValidBuf;
    partialValidBuf = 0;
  }

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

  return *this;

}

PartialVal::PartialVal(const PartialVal& Other) {

  partialBuf = 0;
  partialValidBuf = 0;
  (*this) = Other;

}

PartialVal::~PartialVal() {

  if(partialBuf) {
    delete[] partialBuf;
  }
  if(partialValidBuf) {
    delete[] partialValidBuf;
  }

}

bool* PartialVal::getValidArray(uint64_t nbytes) {

  if(!partialValidBuf) {
    partialValidBuf = new bool[nbytes];
  }

  return partialValidBuf;

}

static uint64_t markPaddingBytes(bool* pvb, const Type* Ty, TargetData* TD) {

  uint64_t marked = 0;

  if(const StructType* STy = dyn_cast<StructType>(Ty)) {
    
    const StructLayout* SL = TD->getStructLayout(STy);
    if(!SL) {
      DEBUG(dbgs() << "Couldn't get struct layout for type " << *STy << "\n");
      return 0;
    }

    uint64_t EIdx = 0;
    for(StructType::element_iterator EI = STy->element_begin(), EE = STy->element_end(); EI != EE; ++EI, ++EIdx) {

      marked += markPaddingBytes(&(pvb[SL->getElementOffset(EIdx)]), *EI, TD);
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

      marked += markPaddingBytes(&(pvb[Offset]), EType, TD);

    }

  }

  return marked;

}

bool PartialVal::isComplete() {

  return isTotal() || isPartial() || loadFinished;

}

bool PartialVal::convertToBytes(uint64_t size, TargetData* TD, std::string& error) {

  if(isByteArray())
    return true;

  PartialVal conv(size);
  if(!conv.combineWith(*this, 0, size, size, TD, error))
    return false;

  (*this) = conv;

  return true;

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

   Constant* TotalC = dyn_cast<Constant>(Other.TotalVC.first);
   if(!TotalC) {
     //LPDEBUG("Unable to use total definition " << itcache(PV.TotalVC) << " because it is not constant but we need to perform byte operations on it\n");
     error = "PP2";
     return false;
   }
   Other.C = TotalC;
   Other.ReadOffset = 0;
   Other.type = PVPartial;

 }

 DEBUG(dbgs() << "This store can satisfy bytes (" << FirstDef << "-" << FirstNotDef << "] of the source load\n");

 // Store defined some of the bytes we need! Grab those, then perhaps complete the load.

 unsigned char* tempBuf;

 if(Other.isPartial()) {

   tempBuf = (unsigned char*)alloca(FirstNotDef - FirstDef);
   // ReadDataFromGlobal assumes a zero-initialised buffer!
   memset(tempBuf, 0, FirstNotDef - FirstDef);

   if(!ReadDataFromGlobal(Other.C, Other.ReadOffset, tempBuf, FirstNotDef - FirstDef, *TD)) {
     DEBUG(dbgs() << "ReadDataFromGlobal failed; perhaps the source " << *(Other.C) << " can't be bitcast?\n");
     error = "RDFG";
     return false;
   }

 }
 else {

   tempBuf = (unsigned char*)Other.partialBuf;

 }

 assert(FirstDef < partialBufBytes);
 assert(FirstNotDef <= partialBufBytes);

 // Avoid rewriting bytes which have already been defined
 for(uint64_t i = 0; i < (FirstNotDef - FirstDef); ++i) {
   if(partialValidBuf[FirstDef + i]) {
     continue;
   }
   else {
     ((unsigned char*)partialBuf)[FirstDef + i] = tempBuf[i]; 
   }
 }

 loadFinished = true;
 // Meaning of the predicate: stop at the boundary, or bail out if there's no more setting to do
 // and there's no hope we've finished.
 for(uint64_t i = 0; i < LoadSize && (loadFinished || i < FirstNotDef); ++i) {

   if(i >= FirstDef && i < FirstNotDef) {
     partialValidBuf[i] = true;
   }
   else {
     if(!partialValidBuf[i]) {
       loadFinished = false;
     }
   }

 }

 return true;

}

//// Implement Normal LF:

bool llvm::containsPointerTypes(const Type* Ty) {

  if(Ty->isPointerTy())
    return true;

  for(Type::subtype_iterator it = Ty->subtype_begin(), it2 = Ty->subtype_end(); it != it2; ++it) {

    if(containsPointerTypes(*it))
      return true;

  }

  return false;

}

bool NormalLoadForwardWalker::addPartialVal(PartialVal& PV, std::string& error, Instruction* I, IntegrationAttempt* IA, uint64_t FirstDef, uint64_t FirstNotDef, bool maySubquery) {

  PartialVal valSoFar(inputPV);
  if(!valSoFar.combineWith(PV, FirstDef, FirstNotDef, LoadSize, TD, error))
    return false;

  if(!valSoFar.isComplete()) {

    if(maySubquery) {

      valSoFar = IA->tryForwardLoadSubquery(I, LoadedPtr, LoadSize, valSoFar, error);
      if(valSoFar.isEmpty()) {

	return false;

      }

    }
    else {

      error = "Reached top";
      return false;

    }

  }

  if((!resultPV.isEmpty()) && (resultPV != valSoFar)) {
      
    error = "Clash";
    return false;

  }
  else {

    resultPV = valSoFar;
    return true;

  }

}

bool NormalLoadForwardWalker::getMIOrReadValue(Instruction* I, IntegrationAttempt* IA, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, PartialVal& NewPV, std::string& error) {

  if (MemIntrinsic *DepMI = dyn_cast<MemIntrinsic>(I)) {

    if(MemSetInst* MSI = dyn_cast<MemSetInst>(DepMI))
      return IA->getMemsetPV(MSI, FirstNotDef - FirstDef, NewPV, error);
    else {
      bool* validBytes = inputPV.isByteArray() ? inputPV.partialValidBuf : 0;
      return IA->getMemcpyPV(cast<MemTransferInst>(DepMI), FirstDef, FirstNotDef, ReadOffset, LoadSize, validBytes, NewPV, error);
    }

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
      bool* validBytes = inputPV.isByteArray() ? inputPV.partialValidBuf : 0;
      return IA->getVaCopyPV(CI, FirstDef, FirstNotDef, ReadOffset, LoadSize, validBytes, NewPV, error);

    }

  }

}

#define NLFWFail(Code) do { FailureCode = Code; FailureVC = make_vc(I, IA); return WIRStopWholeWalk; } while(0);

WalkInstructionResult NormalLoadForwardWalker::handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R, Value* Ptr, uint64_t PtrSize) { 

  PartialVal NewPV;
  uint64_t FirstDef, FirstNotDef, ReadOffset;
  
  if(R == AliasAnalysis::MustAlias) {

    FirstDef = 0; FirstNotDef = std::min(LoadSize, PtrSize); ReadOffset = 0;

    if(StoreInst* SI = dyn_cast<StoreInst>(I)) {

      ValCtx NewVC = IA->getReplacement(SI->getOperand(0));
      if(NewVC != make_vc(SI, IA))
	NewPV = PartialVal::getTotal(NewVC);
      else {

	// Defined by store with no value
	NLFWFail("DNS");

      }

    }
    else if(isa<AllocaInst>(I) || (isa<CallInst>(I) && extractMallocCall(I))) {

      const Type* defType;
      if(AllocaInst* AI = dyn_cast<AllocaInst>(I)) 
	defType = AI->getAllocatedType();
      else
	defType = Type::getIntNTy(I->getContext(), 8 * LoadSize);
      NewPV = PartialVal::getTotal(const_vc(Constant::getNullValue(defType)));

    }
    else {

      std::string error;
      if(!getMIOrReadValue(I, IA, 0, std::min(LoadSize, PtrSize), 0, LoadSize, NewPV, error)) {

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

      if(StoreInst* SI = dyn_cast<StoreInst>(I)) {

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
  if(!addPartialVal(NewPV, error, I, IA, FirstDef, FirstNotDef, true)) {
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

      DEBUG(dbgs() << "Load using global initialiser " << (*(GV->getInitializer())) << "\n");

      Constant* GVC = GV->getInitializer();
      uint64_t GVCSize = (TD->getTypeSizeInBits(GVC->getType()) + 7) / 8;
      uint64_t FirstNotDef = std::min(GVCSize - LoadPtrOffset, LoadSize);
      DEBUG(dbgs() << "Read offset is " << LoadPtrOffset << "\n");

      PartialVal GPV = PartialVal::getPartial(GVC, LoadPtrOffset);
      PartialVal valSoFar = inputPV;
      std::string error;

      bool ret = addPartialVal(GPV, error, 0, 0, 0, FirstNotDef, false);
      if(!ret) {
	FailureCode = error;
	FailureVC = const_vc(GV);
      }
      return ret;

    }

  }

  FailureCode = "UG";
  FailureVC = LoadPtrBase;
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

bool* NormalLoadForwardWalker::getValidBuf() {

  return resultPV.getValidArray(LoadSize);

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

WalkInstructionResult PBLoadForwardWalker::handleAlias(Instruction* I, IntegrationAttempt* IA, AliasAnalysis::AliasResult R, Value* Ptr, uint64_t PtrSize) {

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
  
  raw_ostream& prout = nulls();

  if(R == AliasAnalysis::MustAlias) {

    if(StoreInst* SI = dyn_cast<StoreInst>(I)) {
      PointerBase NewPB;
      if(IA->getPointerBase(SI->getOperand(0), NewPB, SI)) {
	prout << "Add PB ";
	IA->printPB(prout, NewPB);
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
	  IA->printPB(prout, PB);
	  prout << "\n";
	  addPBDefn(PB);
	}
	else {
	  prout << "Overdef (1) on " << IA->itcache(Repl) << " / " << IA->itcache(ReplUO) << "\n";
	  std::string RStr;
	  raw_string_ostream RSO(RStr);
	  RSO << "DN " << IA->itcache(make_vc(I, IA), true);
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
      prout << "Overdef (2) on " << IA->itcache(*(I)) << "\n";
      std::string RStr;
      raw_string_ostream RSO(RStr);
      RSO << "DNS " << IA->itcache(make_vc(I, IA), true);
      RSO.flush();
      setPBOverdef(RStr);
    }

  }
  else {

    // MayAlias

    Instruction* Inst = I;
    std::string RStr;
    raw_string_ostream RSO(RStr);
    RSO << "C " << IA->itcache(make_vc(Inst, IA), true);
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

ValCtx IntegrationAttempt::getWalkerResult(NormalLoadForwardWalker& Walker, const Type* TargetType, raw_string_ostream& RSO) {

  if(Walker.resultPV.isEmpty()) {
    // Can happen for e.g. loads from unreachable code, that hit a call without reachable returns.
    // We shouldn't ever be able to analyse from dead blocks on an intraprocedural level
    // and possibly ought to spot this and stop analysing early rather than proceed out the 
    // notional return edge when there is none.
    RSO << "No result";
    return VCNull;
  }

  uint64_t LoadSize = (TD->getTypeSizeInBits(TargetType) + 7) / 8;
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

    if(SalvageC) {

      uint64_t Offset = PV.isTotal() ? 0 : PV.ReadOffset;
      ValCtx extr = extractAggregateMemberAt(SalvageC, Offset, TargetType, LoadSize, TD);
      if(extr != VCNull)
	return extr;

    }
    else {

      RSO << "NonConstBOps";
      return VCNull;

    }

  }

  if(containsPointerTypes(TargetType)) {
    RSO << "PtrBOps";
    return VCNull;
  }

  // Finally build it from bytes.
  std::string error;
  if(!PV.convertToBytes(LoadSize, TD, error)) {
    RSO << error;
    return VCNull;
  }

  assert(PV.isByteArray());

  return const_vc(constFromBytes((unsigned char*)PV.partialBuf, TargetType, TD));

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

PartialVal IntegrationAttempt::tryForwardLoadSubquery(Instruction* StartInst, ValCtx LoadPtr, uint64_t LoadSize, PartialVal& ResolvedSoFar, std::string& error) {

  NormalLoadForwardWalker Walker(StartInst, this, LoadPtr, LoadSize, AA, TD, ResolvedSoFar);
  Walker.walk();

  if(Walker.FailureVC != VCNull) {

    error = "";
    raw_string_ostream RSO(error);
    RSO << "SQ1 (" << Walker.FailureCode << " " << itcache(Walker.FailureVC) << ")";
    return PVNull;

  }

  return Walker.resultPV;

}

ValCtx IntegrationAttempt::tryForwardLoad(Instruction* StartInst, ValCtx LoadPtr, const Type* TargetType, uint64_t LoadSize, raw_string_ostream& RSO) {

  PartialVal emptyPV;
  NormalLoadForwardWalker Walker(StartInst, this, LoadPtr, LoadSize, AA, TD, emptyPV);

  if(TargetType->isStructTy() || TargetType->isArrayTy()) {
    bool* validBytes = Walker.getValidBuf();
    markPaddingBytes(validBytes, TargetType, TD);
  }

  Walker.walk();

  if(Walker.FailureVC != VCNull) {
    RSO << Walker.FailureCode << " " << itcache(Walker.FailureVC);
    return VCNull;
  }

  ValCtx Res = getWalkerResult(Walker, TargetType, RSO);

  if(Res != VCNull && !shouldForwardValue(Res)) {
    RSO << "Can't forward " << itcache(Res);
    return VCNull;
  }

  return Res;

}

PartialVal IntegrationAttempt::tryForwardLoadTypeless(Instruction* StartInst, ValCtx LoadPtr, uint64_t LoadSize, bool* alreadyValidBytes, std::string& error) {

  PartialVal emptyPV;
  NormalLoadForwardWalker Walker(StartInst, this, LoadPtr, LoadSize, AA, TD, emptyPV);

  if(alreadyValidBytes) {
    bool* validBytes = Walker.getValidBuf();
    memcpy(validBytes, alreadyValidBytes, sizeof(bool) * LoadSize);
  }

  Walker.walk();

  if(Walker.FailureVC != VCNull) {

    error = "";
    raw_string_ostream RSO(error);
    RSO << "SQ2 (" << itcache(Walker.FailureVC) << ")";
    return PVNull;

  }

  return Walker.resultPV;

}

ValCtx IntegrationAttempt::tryForwardLoad(LoadInst* LI) {

  ValCtx ConstResult;
  if(tryResolveLoadFromConstant(LI, ConstResult))
    return ConstResult;

  if(LI->getPointerOperand()->getName() == "__exit_cleanup") {

    errs() << "Hit!";

  }

  std::string failure;
  raw_string_ostream RSO(failure);

  ValCtx ret = tryForwardLoad(LI, make_vc(LI->getPointerOperand(), this), LI->getType(), AA->getTypeStoreSize(LI->getType()), RSO);

  if(ret == VCNull) {
    RSO.flush();
    normalLFFailures[LI] = failure;
  }

  return ret;

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
  
static double time_diff(struct timespec& start, struct timespec& end) {

  timespec temp;
  if ((end.tv_nsec-start.tv_nsec)<0) {
    temp.tv_sec = end.tv_sec-start.tv_sec-1;
    temp.tv_nsec = 1000000000+end.tv_nsec-start.tv_nsec;
  } else {
    temp.tv_sec = end.tv_sec-start.tv_sec;
    temp.tv_nsec = end.tv_nsec-start.tv_nsec;
  }

  return (temp.tv_sec) + (((double)temp.tv_nsec) / 1000000000.0);

}

// Do load forwarding, possibly in optimistic mode: this means that
// stores that def but which have no associated PB are optimistically assumed
// to be compatible with anything, the same as the mergepoint logic above
// when finalise is false. When finalise = true this is just like normal load
// forwarding operating in PB mode.
bool IntegrationAttempt::tryForwardLoadPB(LoadInst* LI, bool finalise, PointerBase& NewPB) {

  PBLoadForwardWalker Walker(LI, this, make_vc(LI->getOperand(0), this), 
			     AA->getTypeStoreSize(LI->getType()),
			     !finalise, LI->getType(), AA, TD);

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
    errs() << "TFLPB took " << time_diff(start, end) << "\n";
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
