
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

public:

  ShadowValue LoadedPtr
  uint64_t LoadSize;
  AliasAnalysis* AA;
  TargetData* TD;

  ShadowValue LoadPtrBase;
  int64_t LoadPtrOffset;

  LoadForwardWalker(ShadowInstruction* Start, ShadowValue Ptr, uint64_t Size, AliasAnalysis* _AA, TargetData* _TD, void* InitialCtx) 
    : BackwardIAWalker(Start, true, InitialCtx), LoadedPtr(Ptr), LoadSize(Size), AA(_AA), TD(_TD) {

    LoadPtrOffset = 0;
    if(!getBaseAndOffset(LoaddedPtr, LoadPtrBase, LoadPtrOffset)) {
      LoadPtrBase = ShadowValue();
      LoadPtrOffset = 0;
    }

  }
  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void*);
  virtual bool shouldEnterCall(ShadowInstruction*);
  virtual WalkInstructionResult handleAlias(ShadowInstruction*, AliasAnalysis::AliasResult R, ShadowValue& Ptr, uint64_t PtrSize, void* Ctx) = 0;

};

class NormalLoadForwardWalker : public LoadForwardWalker {

public:

  PartialVal& inputPV;
  PartialVal resultPV;
  ShadowValue FailureSV;
  std::string FailureCode;

  NormalLoadForwardWalker(ShadowInstruction* Start, ShadowValue Ptr, uint64_t Size, AliasAnalysis* _AA, TargetData* _TD, PartialVal& iPV) : LoadForwardWalker(Start, Ptr, Size, _AA, _TD, 0), inputPV(iPV), resultPV(PVNull), FailureVC(VCNull) { }

  virtual WalkInstructionResult handleAlias(ShadowInstruction* SI, AliasAnalysis::AliasResult R, ShadowValue Ptr, uint64_t PtrSize, void* Ctx);
  virtual bool reachedTop();
  virtual bool mayAscendFromContext(IntegrationAttempt* IA, void*);
  bool addPartialVal(PartialVal& PV, std::string& error, ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, bool maySubquery);
  bool getMIOrReadValue(ShadowInstruction* SI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, PartialVal& NewPV, std::string& error);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);
  bool* getValidBuf();

};

class PBLoadForwardWalker : public LoadForwardWalker {

  bool OptimisticMode;
  const Type* originalType;
  
  BasicBlock* optimisticBB;
  IntegrationAttempt* optimisticIA;

public:

  PointerBase Result;
  std::vector<std::string> OverdefReasons;
  std::vector<ShadowInstruction*> PredStores;
  PointerBase* activeCacheEntry;
  IntegrationAttempt* usedCacheEntryIA;
  LFCacheKey usedCacheEntryKey;

  PBLoadForwardWalker(ShadowInstruction* Start, ShadowValue Ptr, uint64_t Size, bool OM, const Type* OT, AliasAnalysis* _AA, TargetData* _TD, BasicBlock* optBB, IntegrationAttempt* optIA, bool* initialCtx) : LoadForwardWalker(Start, Ptr, Size, _AA, _TD, initialCtx), OptimisticMode(OM), originalType(OT), optimisticBB(optBB), optimisticIA(optIA), activeCacheEntry(0), usedCacheEntryIA(0) { }

  virtual WalkInstructionResult handleAlias(ShadowInstruction*, AliasAnalysis::AliasResult R, ShadowValue, uint64_t PtrSize, void* Ctx);
  void addPBDefn(PointerBase& NewPB, bool cacheAllowed);
  void _addPBDefn(PointerBase& MergeWith, PointerBase& NewPB);
  void setPBOverdef(std::string reason, bool cacheAllowed);
  virtual bool reachedTop();
  virtual bool mayAscendFromContext(IntegrationAttempt* IA, void*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);
  virtual WalkInstructionResult walkFromBlock(ShadowBB*, void* Ctx);
  void cancelCache();

  virtual void freeContext(void* ctx) {
    delete ((bool*)ctx);
  }

  virtual void* copyContext(void* ctx) {
    bool* newctx = new bool;
    *newctx = *((bool*)ctx);
    return newctx;
  }

};

}

//// Implement generic LF

bool LoadForwardWalker::shouldEnterCall(ShadowInstruction* SI) {

  CallInst* CI = cast_inst<CallInst>(SI);

  switch(AA->getModRefInfo(SI, LoadedPtr, LoadSize, true)) {

  case AliasAnalysis::NoModRef:
  case AliasAnalysis::Ref:
    return false;
  default:
    return true;
  }

}

WalkInstructionResult LoadForwardWalker::walkInstruction(ShadowInstruction* I, void* Ctx) {

  ShadowValue Ptr;
  uint64_t PtrSize;

  if (inst_is<StoreInst>(I)) {

    Ptr = I->getOperand(1);
    PtrSize = AA->getTypeStoreSize(I->invar->I->getOperand(0)->getType());
    // Fall through to alias analysis

  }
  else if (inst_is<AllocaInst>(I) || (inst_is<CallInst>(I) && extractMallocCall(I->invar->I))) {
    
    if(LoadPtrBase == I) {
      return handleAlias(I, AliasAnalysis::MustAlias, ShadowValue(I), LoadSize, Ctx);
    }
    else
      return WIRContinue;

  }
  else if(inst_is<MemIntrinsic>(I)) {

    Ptr = I->getCallArgOperand(0);
    ConstantInt* CI = dyn_cast_or_null<ConstantInt>(getConstReplacement(I->getCallArgOperand(2)));
    PtrSize = CI ? CI->getLimitedValue() : AliasAnalysis::UnknownSize;
    // Fall through to alias analysis

  }
  else if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {

    if(ReadFile* RF = I->parent->IA->tryGetReadFile(CI)) {
      
      Ptr = SI->getCallArgOperand(1);
      PtrSize = RF->readSize;
      // Fall through to alias analysis

    }
    else if(Function* CalledF = getCalledFunction(SI)) {

      if(CalledF->getName() == "llvm.va_start" || CalledF->getName() == "llvm.va_copy") {

	Ptr = I->getCallArgOperand(0);
	PtrSize = 24;

      }
      else if(CalledF->getName() == "realloc") {

	Ptr = I;
	PtrSize = AliasAnalysis::UnknownSize;

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

  AliasAnalysis::AliasResult R = AA->aliasHypothetical(LoadedPtr, LoadSize, Ptr, PtrSize, true);
  if(R == AliasAnalysis::NoAlias)
    return WIRContinue;

  return handleAlias(I, IA, R, Ptr, PtrSize, Ctx);

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
  TotalSV = Other.TotalSV;
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

  if(Other.isVarargTainted)
    isVarargTainted = true;

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

    Constant* TotalC = dyn_cast_or_null<Constant>(Other.TotalSV.getVal());
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

bool NormalLoadForwardWalker::addPartialVal(PartialVal& PV, std::string& error, ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, bool maySubquery) {

  PartialVal valSoFar(inputPV);
  if(!valSoFar.combineWith(PV, FirstDef, FirstNotDef, LoadSize, TD, error))
    return false;

  if(!valSoFar.isComplete()) {

    if(maySubquery) {

      valSoFar = tryForwardLoadSubquery(I, LoadedPtr, LoadSize, valSoFar, error);
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

bool NormalLoadForwardWalker::getMIOrReadValue(ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, PartialVal& NewPV, std::string& error) {

  if (inst_is<MemIntrinsic>(I)) {

    if(inst_is<MemSetInst>(DepMI))
      return getMemsetPV(I, FirstNotDef - FirstDef, NewPV, error);
    else {
      bool* validBytes = inputPV.isByteArray() ? inputPV.partialValidBuf : 0;
      return getMemcpyPV(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, validBytes, NewPV, error);
    }

  }
  else {

    Function* F = getCalledFunction(I);
    if(F->getName() == "read") {
      
      return getReadPV(I, FirstNotDef - FirstDef, ReadOffset, NewPV, error);

    }
    else if(F->getName() == "llvm.va_start") {

      return getVaStartPV(I, ReadOffset, NewPV, error);

    }
    else if(F->getName() == "realloc") {

      bool* validBytes = inputPV.isByteArray() ? inputPV.partialValidBuf : 0;
      return getReallocPV(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, validBytes, NewPV, error);

    }
    else {

      assert(F->getName() == "llvm.va_copy");
      bool* validBytes = inputPV.isByteArray() ? inputPV.partialValidBuf : 0;
      return getVaCopyPV(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, validBytes, NewPV, error);

    }

  }

}

#define NLFWFail(Code) do { FailureCode = Code; FailureSV = ShadowValue(I); return WIRStopWholeWalk; } while(0);

WalkInstructionResult NormalLoadForwardWalker::handleAlias(ShadowInstruction* I, AliasAnalysis::AliasResult R, ShadowValue Ptr, uint64_t PtrSize, void*) { 

  PartialVal NewPV;
  uint64_t FirstDef, FirstNotDef, ReadOffset;
  
  if(R == AliasAnalysis::MustAlias) {

    FirstDef = 0; FirstNotDef = std::min(LoadSize, PtrSize); ReadOffset = 0;

    if(inst_is<StoreInst>(I)) {

      ShadowValue NewV = getReplacement(I->getOperand(0), true);
      if(!NewV.isInval())
	NewPV = PartialVal::getTotal(NewV);
      else {

	// Defined by store with no value
	NLFWFail("DNS");

      }

    }
    else if(isa<AllocaInst>(I) || (isa<CallInst>(I) && extractMallocCall(I->invar->I))) {

      const Type* defType;
      if(AllocaInst* AI = dyn_cast_inst<AllocaInst>(I)) 
	defType = AI->getAllocatedType();
      else
	defType = Type::getIntNTy(I->getContext(), 8 * LoadSize);
      NewPV = PartialVal::getTotal(ShadowValue(Constant::getNullValue(defType)));

    }
    else {

      std::string error;
      if(!getMIOrReadValue(I, 0, std::min(LoadSize, PtrSize), 0, LoadSize, NewPV, error)) {

	// Memcpy, memset or read failed
	NLFWFail(error);

      }
      // Else fall through

    }

  }
  else {
    
    // MayAlias

    int64_t WriteOffset = 0;
    ShadowValue WriteBase;
    if(getBaseAndOffset(Ptr, WriteBase, WriteOffset)) {

      if(IA->GetDefinedRange(LoadPtrBase, LoadPtrOffset, LoadSize,
			     WriteBase, WriteOffset, PtrSize,
			     FirstDef, FirstNotDef, ReadOffset)) {

	if(inst_is<StoreInst>(I)) {

	  Constant* StoreC = getConstReplacement(I->getOperand(0));
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
	  if(!getMIOrReadValue(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, NewPV, error)) {
	
	    // Memset, memcpy or read failed
	    NLFWFail(error);

	  }
	  // Else fall through
	
	}

      }
      else {
	
	NLFWFail("C");

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

bool NormalLoadForwardWalker::blockedByUnexpandedCall(ShadowInstruction* I, void*) {

  FailureCode = "UEC";
  FailureSV = ShadowValue(I);
  return true;

}

bool NormalLoadForwardWalker::reachedTop() {

  if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(LoadPtrBase.getVal())) {
	    
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
	FailureSV = ShadowValue(GV);
      }
      return ret;

    }

  }

  FailureCode = "UG";
  FailureSV = ShadowValue(LoadPtrBase);
  return false;

}

bool NormalLoadForwardWalker::mayAscendFromContext(IntegrationAttempt* IA, void*) {

  if(ShadowInst* SI = LoadPtrBase.getInst()) {

    if(IA == SI->parent->IA) {
    
      FailureVC = make_vc(IA->getEntryInstruction(), IA);
      FailureCode = "Scope";
      return false;

    }

  }
    
  return true;

}

bool* NormalLoadForwardWalker::getValidBuf() {

  return resultPV.getValidArray(LoadSize);

}

//// Implement PBLF:

void PBLoadForwardWalker::_addPBDefn(PointerBase& MergeWith, PointerBase& NewPB) {

  bool WasOverdef = MergeWith.Overdef;
  MergeWith.merge(NewPB);
  if(MergeWith.Overdef && (!WasOverdef) && (!NewPB.Overdef))
    OverdefReasons.push_back("Fan-in");

}

void PBLoadForwardWalker::addPBDefn(PointerBase& NewPB, bool cacheAllowed) {

  _addPBDefn(Result, NewPB);
  if(activeCacheEntry && cacheAllowed)
    _addPBDefn(*activeCacheEntry, NewPB);

}

void PBLoadForwardWalker::setPBOverdef(std::string reason, bool cacheAllowed) {
  OverdefReasons.push_back(reason);
  Result = PointerBase::getOverdef();
  if(activeCacheEntry && cacheAllowed)
    *activeCacheEntry = PointerBase::getOverdef();
}

void PBLoadForwardWalker::cancelCache() {

  if(activeCacheEntry) {

    LFCacheKey Key = LFCK(optimisticBB, LoadPtrBase, LoadPtrOffset, LoadSize);
    optimisticIA->deleteLFPBCacheEntry(Key);
    activeCacheEntry = 0;

  }

}

WalkInstructionResult PBLoadForwardWalker::handleAlias(ShadowInstruction* I, AliasAnalysis::AliasResult R, ShadowValue Ptr, uint64_t PtrSize, void* Ctx) {

  // If we're in the optimistic phase, ignore anything but the following:
  // * Defining stores with an associated PB
  // * Defining alloca instructions
  // Unexpanded calls are also significant but these are caught by blockedByUnexpandedCall.
  // Don't behave optimistically if we're outside the loop subject to consideration.

  bool cacheAllowed = *((bool*)Ctx);

  if(inst_is<StoreInst>(I)) {

    PredStores.push_back(I);

  }

  if(OptimisticMode && !cacheAllowed) {

    bool ignore = true;

    if(R == AliasAnalysis::MustAlias) {
      if(inst_is<AllocaInst>(I))
	ignore = false;
      else if(inst_is<StoreInst>(I)) {
	PointerBase ResPB;
	ShadowValue StoredVal = I->getOperand(0);
	if(getPointerBase(StoredVal, ResPB, I) || !isUnresolved(StoredVal))
	  ignore = false;
      }
    }
      
    if(ignore)
      return WIRContinue;

  }
  
  raw_ostream& prout = nulls();

  if(R == AliasAnalysis::MustAlias) {

    if(inst_is<StoreInst>(I)) {
      PointerBase NewPB;
      if(getPointerBase(I->getOperand(0), NewPB, I)) {
	prout << "Add PB ";
	I->invar->IA->printPB(prout, NewPB);
	prout << "\n";
	// Actually addPBDefn will do the merge anyhow, but we annotate the LFA with a reason.
	if(NewPB.Overdef) {
	  std::string RStr;
	  raw_string_ostream RSO(RStr);
	  RSO << "DO " << I->invar->IA->itcache(I, true);
	  RSO.flush();
	  setPBOverdef(RStr, cacheAllowed);
	}
	else {
	  addPBDefn(NewPB, cacheAllowed);
	}
      }
      else {
	// Try to find a concrete definition, since the concrete defns path is more advanced.
	// Remember the PB sets only take constants or identified underlying objects.
	ShadowValue Repl = getReplacement(SI->getOperand(0), true);
	if(Repl.isInval()) {
	  int64_t Offset;
	  getBaseAndOffset(SI->getOperand(0), Repl, Offset);
	}
	
	if(!Repl.isInval()) {
	  PointerBase PB = PointerBase::get(Repl);
	  prout << "Add PB ";
	  IA->printPB(prout, PB);
	  prout << "\n";
	  addPBDefn(PB, cacheAllowed);
	}
	else {
	  prout << "Overdef (1) on " << IA->itcache(Repl) << " / " << IA->itcache(ReplUO) << "\n";
	  std::string RStr;
	  raw_string_ostream RSO(RStr);
	  RSO << "DN " << IA->itcache(make_vc(I, IA), true);
	  RSO.flush();
	  setPBOverdef(RStr, cacheAllowed);
	}
      }
    }
    else if(AllocaInst* AI = dyn_cast<AllocaInst>(I)) {

      // Allocas have no defined initial value, so just assume null.
      PointerBase NewPB = PointerBase::get(ShadowValue(Constant::getNullValue(AI->getType())));
      addPBDefn(NewPB, cacheAllowed);

    }
    else {
      prout << "Overdef (2) on " << IA->itcache(*(I)) << "\n";
      std::string RStr;
      raw_string_ostream RSO(RStr);
      RSO << "DNS " << I->parent->IA->itcache(I, true);
      RSO.flush();
      setPBOverdef(RStr, cacheAllowed);
    }

  }
  else {

    // MayAlias

    std::string RStr;
    raw_string_ostream RSO(RStr);
    RSO << "C " << I->parent->IA->itcache(I, true);
    RSO.flush();
    setPBOverdef(RStr, cacheAllowed);

  }

  if(Result.Overdef && !cacheAllowed) {
    // If we abort within the loop, whatever results we gathered from without will be partial.
    cancelCache();
    return WIRStopWholeWalk;
  }
  else
    return WIRStopThisPath;
  
}

bool PBLoadForwardWalker::reachedTop() {

  if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(LoadPtrBase.getVal())) {
	    
    if(GV->hasDefinitiveInitializer()) {
	
      Constant* GVC = GV->getInitializer();
      uint64_t GVCSize = (TD->getTypeSizeInBits(GVC->getType()) + 7) / 8;
      uint64_t FirstNotDef = std::min(GVCSize - LoadPtrOffset, LoadSize);
      if(FirstNotDef == LoadSize) {

	Constant* FieldVC = extractAggregateMemberAt(GVC, LoadPtrOffset, originalType, LoadSize, TD);
	if(FieldVC != VCNull) {
	  
	  assert(isa<Constant>(FieldVC.first));
	  PointerBase NewPB = PointerBase::get(ShadowValue(FieldVC));
	  addPBDefn(NewPB, true);
	  return true;
	  
	}

      }

    }
    
  }

  setPBOverdef("Reached top", true);

  return false;

}

bool PBLoadForwardWalker::blockedByUnexpandedCall(ShadowValue* I, void* Ctx) {

  bool cacheAllowed = *((bool*)Ctx);

  if(OptimisticMode && !cacheAllowed) {

    bool ignore = true;

    if(!inst_is<MemIntrinsic>(I)) {
      Function* CF = getCalledFunction(I);
      if(!CF)
	ignore = false;
      else {
	if(!functionIsBlacklisted(CF))
	  ignore = false;
      }
    }

    if(ignore)
      return false;

  }

  std::string RStr;
  raw_string_ostream RSO(RStr);
  RSO << "UEC " << I->parent->IA->itcache(I, true);
  RSO.flush();
  setPBOverdef(RStr, cacheAllowed);

  if(!cacheAllowed)
    cancelCache();

  return true;

}

bool PBLoadForwardWalker::mayAscendFromContext(IntegrationAttempt* IA, void* Ctx) {

  bool cacheAllowed = *((bool*)Ctx);

  if(ShadowInstruction* SI = LoadPtrBase.getInst()) {

    if(IA == SI->parent->IA) {
    
      setPBOverdef("Scope", cacheAllowed);
      if(!cacheAllowed)
	cancelCache();
      return false;

    }
    
    return true;

  }

}

PointerBase* IntegrationAttempt::getLFPBCacheEntry(LFCacheKey& Key) {

  DenseMap<LFCacheKey, PointerBase>::iterator it = LFPBCache.find(Key);
  if(it != LFPBCache.end())
    return &(it->second);
  else
    return 0;

}

void IntegrationAttempt::deleteLFPBCacheEntry(LFCacheKey& Key) {

  release_assert(LFPBCache.erase(Key));

}

PointerBase* IntegrationAttempt::createLFPBCacheEntry(LFCacheKey& Key) {

  return &(LFPBCache[Key]);

}

WalkInstructionResult PBLoadForwardWalker::walkFromBlock(ShadowBB* BB, void* Ctx) {

  bool cacheAllowed = *((bool*)Ctx);

  if(!cacheAllowed) {

    // See if we're walking from the first block that is cache-eligible
    if(BB == optimisticBB && IA == optimisticIA) {

      LPDEBUG("Left loop at " << BB->invar->BB->getName() << "\n");
      *((bool*)Ctx) = 1;

    }
    else {

      return WIRContinue;

    }

  }

  // No point either looking for cache entries or making them if the block isn't a certainty.
  if(BB->status != BBSTATUS_CERTAIN)
    return WIRContinue;

  // See if this block has a cache entry for us:
  LFCacheKey Key = LFCK(BB, LoadPtrBase, LoadPtrOffset, LoadSize);
  if(PointerBase* CachedPB = BB->IA->getLFPBCacheEntry(Key)) {
      
    LPDEBUG("Use cache entry at " << BB->getName() << "\n");
    addPBDefn(*CachedPB, true);
    
    usedCacheEntryIA = IA;
    usedCacheEntryKey = Key;

    return WIRStopThisPath;

    // Don't delete this potentially redundant cache entry just yet!
    // We might yet abort this walk and want to keep it.
    // Instead clean it up in TFLPB below if necessary.

  }
  else if(!activeCacheEntry) {

    // This is necessarily the cache threshold:
    LPDEBUG("Create cache entry at " << BB->getName() << "\n");
    // Make a cache entry here:
    activeCacheEntry = BB->IA->createLFPBCacheEntry(Key);
    return WIRContinue;
      
  }
  else {
      
    // Keep building existing entry
    return WIRContinue;

  }

}

//// Conventional LF interface:

ShadowValue IntegrationAttempt::getWalkerResult(NormalLoadForwardWalker& Walker, const Type* TargetType, raw_string_ostream& RSO) {

  if(Walker.resultPV.isEmpty()) {
    // Can happen for e.g. loads from unreachable code, that hit a call without reachable returns.
    // We shouldn't ever be able to analyse from dead blocks on an intraprocedural level
    // and possibly ought to spot this and stop analysing early rather than proceed out the 
    // notional return edge when there is none.
    RSO << "No result";
    return ShadowValue();
  }

  uint64_t LoadSize = (TD->getTypeSizeInBits(TargetType) + 7) / 8;
  PartialVal& PV = Walker.resultPV;

  // Try to use an entire value:
  if(PV.isTotal()) {

    ShadowValue Res = PV.TotalSV;
    const Type* sourceType = Res.getType();
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
      Constant* extr = extractAggregateMemberAt(SalvageC, Offset, TargetType, LoadSize, TD);
      if(extr)
	return ShadowValue(extr);

    }
    else {

      RSO << "NonConstBOps";
      return VCNull;

    }

  }

  // Finally build it from bytes.
  std::string error;
  if(!PV.convertToBytes(LoadSize, TD, error)) {
    RSO << error;
    return ShadowValue();
  }

  assert(PV.isByteArray());

  if(containsPointerTypes(TargetType)) {

    // If we're trying to synthesise a pointer from raw bytes, only a null pointer is allowed.
    unsigned char* checkBuf = (unsigned char*)PV.partialBuf;
    for(unsigned i = 0; i < PV.partialBufBytes; ++i) {

      if(checkBuf[i]) {
	RSO << "Non-null Ptr Byteops";
	return ShadowValue();
      }

    }

  }

  return ShadowValue(constFromBytes((unsigned char*)PV.partialBuf, TargetType, TD));

}

bool IntegrationAttempt::tryResolveLoadFromConstant(ShadowInstruction* LoadI, ShadowValue& Result) {

  // A special case: loading from a symbolic vararg:

  ShadowValue LPtr = getReplacement(LoadI->getOperand(0));
  ShadowValue LPtrStr = ShadowValue(LPtr.stripPointerCasts(), LPtr.va_arg);

  if(LPtrStr.isVaArg() && LPtrStr.getVaArgType() != ValCtx::va_baseptr) {
    
    ShadowInstruction* PtrI = LPtrStr.getInst();
    PtrI->parent->IA->getVarArg(LPtrStr.va_arg, Result);
    LPDEBUG("va_arg " << itcache(LPtrStr) << " " << LPtrStr.va_arg << " yielded " << itcache(Result) << "\n");
    
    if((!Result.isInval()) && Result.getType() != LoadI->getType()) {
      if(!(Result.getType()->isPointerTy() && LoadI->getType()->isPointerTy()))
	Result = ShadowValue();
    }

    // Is this va_arg read out of bounds or wrong type?
    if(Result.isInval())
      return true;
    
    if(!shouldForwardValue(Result))
      Result = ShadowValue();

    return true;

  }

  if(Value* PtrVal = LPtr.getVal()) {

    if(Constant* PtrC = dyn_cast<Constant>(PtrVal)) {

      int64_t Offset = 0;
      Constant* Base = GetBaseWithConstantOffset(PtrC, this, Offset);

      if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(Base.first)) {
	if(GV->isConstant()) {

	  uint64_t LoadSize = (TD->getTypeSizeInBits(LoadI->getType()) + 7) / 8;
	  const Type* FromType = GV->getInitializer()->getType();
	  uint64_t FromSize = (TD->getTypeSizeInBits(FromType) + 7) / 8;

	  if(Offset < 0 || Offset + LoadSize > FromSize) {
	    Result = ShadowValue();
	    return true;
	  }

	  Result = ShadowValue(extractAggregateMemberAt(GV->getInitializer(), Offset, LoadI->getType(), LoadSize, TD));
	  if(!Result.isInval())
	    return true;

	  int64_t CSize = TD->getTypeAllocSize(GV->getInitializer()->getType());
	  if(CSize < Offset) {

	    LPDEBUG("Can't forward from constant: read from global out of range\n");
	    Result = ShadowValue();
	    return true;
	    
	  }

	  unsigned char* buf = (unsigned char*)alloca(LoadSize);
	  memset(buf, 0, LoadSize);
	  if(ReadDataFromGlobal(GV->getInitializer(), Offset, buf, LoadSize, *TD)) {

	    Result = ShadowValue(constFromBytes(buf, LoadI->getType(), TD));
	    return true;
	    
	  }
	  else {

	    LPDEBUG("ReadDataFromGlobal failed\n");
	    Result = VCNull;
	    return true;

	  }

	}

      }

    }

  }
      
  // Check for loads which are pointless to pursue further because they're known to be rooted on
  // a constant global but we're uncertain what offset within that global we're looking for:

  if(ShadowInstruction* SI = LPtr.getInst()) {

    if(SI->PB.Values.size() > 0 && SI->PB.Type == ValSetTypePB) {

      bool foundNonConst = false;
      for(unsigned i = 0; i < SI->PB.Values.size(); ++i) {

	GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(SI->PB.Values[i].getVal());
	if((!GV) || !GV->isConstant())
	  foundNonConst = true;

      }

      if(!foundNonConst) {

	LPDEBUG("Load cannot presently be resolved, but is rooted on a constant global. Abandoning search\n");
	Result = ShadowValue();
	return true;

      }

    }

  }

  return false;

}

PartialVal llvm::tryForwardLoadSubquery(ShadowInstruction* StartInst, ShadowValue LoadPtr, uint64_t LoadSize, PartialVal& ResolvedSoFar, std::string& error) {

  NormalLoadForwardWalker Walker(StartInst, LoadPtr, LoadSize, AA, TD, ResolvedSoFar);
  Walker.walk();

  if(Walker.FailureVC != VCNull) {

    error = "";
    raw_string_ostream RSO(error);
    RSO << "SQ1 (" << Walker.FailureCode << " " << StartInst->parent->IA->itcache(Walker.FailureVC) << ")";
    return PVNull;

  }

  return Walker.resultPV;

}

ValCtx llvm::tryForwardLoad(ShadowInstruction* StartInst, ShadowValue& LoadPtr, const Type* TargetType, uint64_t LoadSize, raw_string_ostream& RSO) {

  PartialVal emptyPV;
  NormalLoadForwardWalker Walker(StartInst, LoadPtr, LoadSize, AA, TD, emptyPV);

  if(TargetType->isStructTy() || TargetType->isArrayTy()) {
    bool* validBytes = Walker.getValidBuf();
    markPaddingBytes(validBytes, TargetType, TD);
  }

  Walker.walk();

  if(Walker.FailureVC != VCNull) {
    RSO << Walker.FailureCode << " " << itcache(Walker.FailureVC);
    return VCNull;
  }

  ShadowValue Res = getWalkerResult(Walker, TargetType, RSO);

  if(Res != VCNull && !shouldForwardValue(Res)) {
    RSO << "Can't forward " << itcache(Res);
    return VCNull;
  }

  if(Walker.resultPV.isVarargTainted)
    contextTaintedByVarargs = true;

  return Res;

}

PartialVal llvm::tryForwardLoadTypeless(ShadowInstruction* StartInst, ValCtx LoadPtr, uint64_t LoadSize, bool* alreadyValidBytes, std::string& error) {

  PartialVal emptyPV;
  NormalLoadForwardWalker Walker(StartInst, LoadPtr, LoadSize, AA, TD, emptyPV);

  if(alreadyValidBytes) {
    bool* validBytes = Walker.getValidBuf();
    memcpy(validBytes, alreadyValidBytes, sizeof(bool) * LoadSize);
  }

  Walker.walk();

  if(Walker.FailureVC != VCNull) {

    error = "";
    raw_string_ostream RSO(error);
    RSO << "SQ2 (" << StartInst->parent->IA->itcache(Walker.FailureVC) << ")";
    return PVNull;

  }

  return Walker.resultPV;

}

void IntegrationAttempt::addForwardedInst(Instruction* I, ValCtx User) {

  DenseMap<Instruction*, SmallVector<ValCtx, 4> >::iterator it = instIndirectUsers.find(I);
  if(it != instIndirectUsers.end()) {

    if(std::find(it->second.begin(), it->second.end(), User) == it->second.end())
      it->second.push_back(User);

  }
  else {

    instIndirectUsers[I].push_back(User);

  }

}

ShadowValue IntegrationAttempt::tryForwardLoad(ShadowInstruction* LI) {

  ShadowValue ConstResult;
  if(tryResolveLoadFromConstant(LI, ConstResult))
    return ConstResult;

  std::string failure;
  raw_string_ostream RSO(failure);

  ShadowValue ret = tryForwardLoad(LI, LI->getOperand(0), LI->getType(), AA->getTypeStoreSize(LI->getType()), RSO);

  if(ret.isInval()) {
    RSO.flush();
    normalLFFailures[LI] = failure;
  }
  else if(ShadowInstruction* ForwardedSI = ret.getInst()) {

    ForwardedSI->i.indirectUsers.push_back(LI);
      
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
bool IntegrationAttempt::tryForwardLoadPB(ShadowInstruction* LI, bool finalise, PointerBase& NewPB, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA) {

  // Freed by the walker:
  bool* initialCtx = new bool;
  // Per-block context records whether we've passed the cache threshold.
  // Always start with 0, might immediately flip and cache in the starting block.
  // When we're outside the cache threshold we also switch to pessimistic mode
  // since everything before that point is a fixed certainty.
  *initialCtx = 0;

  PBLoadForwardWalker Walker(LI, LI->getOperand(0), 
			     AA->getTypeStoreSize(LI->getType()),
			     !finalise, LI->getType(), AA, TD,
			     CacheThresholdBB, CacheThresholdIA, initialCtx);

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

    errs() << "Consider " << itcache(*LI) << " took " << time_diff(start, end) << "\n";
    errs() << "Cache params: " << itcache(Walker.LoadPtrBase) << ", " << Walker.LoadPtrOffset << ", " << Walker.LoadSize << ", " << (!!Walker.activeCacheEntry) << ", " << (Walker.usedCacheEntryIA ? Walker.usedCacheEntryIA->getShortHeader() : "(none)") << ", " << (Walker.usedCacheEntryIA ? Walker.usedCacheEntryKey.first.first.first->getName() : "(none)") << "\n";

  }

  if(Walker.activeCacheEntry && Walker.usedCacheEntryIA) {

    LPDEBUG("Delete cache entry\n");
    // Our new cache entry subsumes this old one, since we walk the program in topological order.
    Walker.usedCacheEntryIA->deleteLFPBCacheEntry(Walker.usedCacheEntryKey);

  }

  for(std::vector<ShadowInstruction*>::iterator it = Walker.PredStores.begin(), it2 = Walker.PredStores.end(); it != it2; ++it) {

    // Register our dependency on various instructions:
    if(std::find(LI, (*it)->PBIndirectUsers.begin(), (*it)->PBIndirectUsers.end()) ==  (*it)->PBIndirectUsers.end())
      (*it)->PBIndirectUsers.push_back(LI);

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

void IntegrationAttempt::checkLoad(ShadowInstruction* LI) {

  ShadowValue Result = tryForwardLoad(LI);
  if(!Result.isInval())
    LI->i.replaceWith = Result;

}
