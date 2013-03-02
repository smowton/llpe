
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
    if(!getBaseAndConstantOffset(LoaddedPtr, LoadPtrBase, LoadPtrOffset)) {
      LoadPtrBase = ShadowValue();
      LoadPtrOffset = 0;
    }

  }

  LoadForwardWalker(ShadowInstruction* Start, ShadowValue Base, int64_t Offset, uint64_t Size, AliasAnalysis* _AA, TargetData* _TD, void* InitialCtx) 
    : BackwardIAWalker(Start, true, InitialCtx), LoadedPtr(), LoadPtrBase(Base), LoadPtrOffset(Offset), LoadSize(Size), AA(_AA), TD(_TD) {



  }

  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void*);
  virtual bool shouldEnterCall(ShadowInstruction*);
  virtual WalkInstructionResult handleAlias(ShadowInstruction*, AliasAnalysis::AliasResult R, ShadowValue& Ptr, uint64_t PtrSize, void* Ctx) = 0;

};

class NormalLoadForwardWalker : public LoadForwardWalker {

  const Type* originalType;
  bool OptimisticMode;
  
  BasicBlock* optimisticBB;
  IntegrationAttempt* optimisticIA;

public:

  PartialVal& inputPV;
  PointerBase Result;
  std::vector<std::string> OverdefReasons;
  std::vector<ShadowInstruction*> UsedInstructions;
  PointerBase* activeCacheEntry;
  IntegrationAttempt* usedCacheEntryIA;
  LFCacheKey usedCacheEntryKey;

  NormalLoadForwardWalker(ShadowInstruction* Start, ShadowValue Ptr, uint64_t Size, const Type* OT, bool OM, AliasAnalysis* _AA, TargetData* _TD, BasicBlock* optBB, IntegrationAttempt* optIA, bool* firstCtx, PartialVal& iPV) : LoadForwardWalker(Start, Ptr, Size, _AA, _TD, firstCtx), originalType(OT), OptimisticMode(OM), optimisticBB(optBB), optimisticIA(optIA), inputPV(iPV) { }

  NormalLoadForwardWalker(ShadowInstruction* Start, ShadowValue PtrBase, int64_t PtrOffset, uint64_t Size, const Type* OT, bool OM, AliasAnalysis* _AA, TargetData* _TD, BasicBlock* optBB, IntegrationAttempt* optIA, bool* firstCtx, PartialVal& iPV) : LoadForwardWalker(Start, PtrBase, PtrOffset, Size, _AA, _TD, firstCtx), originalType(OT), OptimisticMode(OM), optimisticBB(optBB), optimisticIA(optIA), inputPV(iPV) { }

  virtual WalkInstructionResult handleAlias(ShadowInstruction* SI, AliasAnalysis::AliasResult R, ShadowValue Ptr, uint64_t PtrSize, void* Ctx);
  virtual bool reachedTop();
  virtual bool mayAscendFromContext(IntegrationAttempt* IA, void*);
  bool addPartialVal(PartialVal& PV, std::string& error, ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, bool maySubquery);
  bool getMIOrReadValue(ShadowInstruction* SI, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, PartialVal& NewPV, std::string& error);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);
  bool* getValidBuf();

  void addPBDefn(PointerBase& NewPB, bool cacheAllowed);
  void _addPBDefn(PointerBase& MergeWith, PointerBase& NewPB);
  void setPBOverdef(std::string reason, bool cacheAllowed);

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

//// Implement generic LF

bool LoadForwardWalker::shouldEnterCall(ShadowInstruction* SI) {

  CallInst* CI = cast_inst<CallInst>(SI);

  if(!LoadedPtr.isInval()) {
    switch(AA->getModRefInfo(SI, LoadedPtr, LoadSize, true)) {
      
    case AliasAnalysis::NoModRef:
    case AliasAnalysis::Ref:
      return false;
    default:
      return true;
    }
  }
  else {

    // Less ambitious check when we don't have a real instruction to hand to AA
    ModRefBehavior MRB = getModRefBehavior(ImmutableCallSite(CS));
    if (MRB == DoesNotAccessMemory)
      return false;
    else if (MRB == OnlyReadsMemory)
      return false;
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

  AliasAnalysis::AliasResult R;
  if(!(LoadedPtr.isInval()))
    R = AA->tryResolvePointerBases(LoadPtrBase, LoadSize, Ptr, PtrSize, true);
  else
    R = AA->aliasHypothetical(LoadedPtr, LoadSize, Ptr, PtrSize, true);
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

bool NormalLoadForwardWalker::addPartialVal(PartialVal& PV, PointerBase& PB, std::string& error, ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, bool cacheAllowed, bool maySubquery) {

  if(PB.Overdef) {
    addPBDefn(PB, cacheAllowed);
    return false;
  }

  // For now, forbid using pursuing several different subqueries because a partial defn had multiple values.
  if(PB.Values.size() >= 1) {

    if(PB.FirstDef == 0 && FirstNotDef == LoadSize && inputPV.isEmpty()) {

      addPBDefn(PB, cacheAllowed);
      return !PB.Overdef;

    }
    else if(PB.Values.size() == 1 && PB.type == ValSetTypeScalar) {

      PV = PartialVal::getPartial(PB.Values[0].V, 0);
      // Fall through to standard PV case
      
    }
    else {

      return false;

    }
    
  }

  PartialVal valSoFar(inputPV);
  if(!valSoFar.combineWith(PV, FirstDef, FirstNotDef, LoadSize, TD, error))
    return false;

  if(!valSoFar.isComplete()) {

    // Disallow complex queries when solving for loop invariants:
    if(maySubquery && cacheAllowed) {

      NewPB = tryForwardLoadSubquery(I, LoadedPtr, LoadPtrBase, LoadPtrOffset, LoadSize, originalType, valSoFar, error);

    }
    else {

      error = "Reached top";
      return false;

    }

  }
  else {

    std::string synthError;
    ShadowValue NewSV;
    {
      raw_string_ostream RSO(synthError);
      NewSV = PVToSV(valSoFar, RSO);
    }
    if(NewSV.isInval()) {
      error = synthError;
      return false;
    }

    if(!getPointerBase(NewSV, NewPB))
      return false;

  }

  addPBDefn(NewPB, cacheAllowed);
  return !Result.Overdef;

}

bool NormalLoadForwardWalker::getMIOrReadValue(ShadowInstruction* I, uint64_t FirstDef, uint64_t FirstNotDef, int64_t ReadOffset, uint64_t LoadSize, PartialVal& NewPV, PointerBase& NewPB, PointerBase* NewPB, std::string& error) {

  if (inst_is<MemIntrinsic>(I)) {

    if(inst_is<MemSetInst>(DepMI))
      return getMemsetPV(I, FirstNotDef - FirstDef, NewPV, error);
    else {
      bool* validBytes = inputPV.isByteArray() ? inputPV.partialValidBuf : 0;
      return getMemcpyPB(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, originalType, validBytes, NewPB, error);
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
      return getReallocPB(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, originalType, validBytes, NewPB, error);

    }
    else {

      assert(F->getName() == "llvm.va_copy");
      bool* validBytes = inputPV.isByteArray() ? inputPV.partialValidBuf : 0;
      return getVaCopyPB(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, originalType, validBytes, NewPB, error);

    }

  }

}



#define NLFWFail(Code) do { std::string failureText; { raw_string_ostream RSO(failureText); RSO << Code << " " << (*I); }  setPBOverdef(failureText, cacheAllowed); if(!cacheAllowed) { cancelCache(); } return WIRStopWholeWalk; } while(0);

WalkInstructionResult NormalLoadForwardWalker::handleAlias(ShadowInstruction* I, AliasAnalysis::AliasResult R, ShadowValue Ptr, uint64_t PtrSize, void* Ctx) { 

  PartialVal NewPV;
  PointerBase NewPB;
  uint64_t FirstDef, FirstNotDef, ReadOffset;

  // If we're in the optimistic phase, ignore anything but the following:
  // * Defining stores with an associated PB
  // * Defining alloca instructions
  // Unexpanded calls are also significant but these are caught by blockedByUnexpandedCall.
  // Don't behave optimistically if we're outside the loop subject to consideration.

  bool cacheAllowed = *((bool*)Ctx);

  if(OptimisticMode && !cacheAllowed) {

    bool ignore = true;

    if(R == AliasAnalysis::MustAlias) {
      if(inst_is<AllocaInst>(I))
	ignore = false;
      else if(inst_is<StoreInst>(I)) {
	PointerBase ResPB;
	ShadowValue StoredVal = I->getOperand(0);
	if(StoredVal.isVal() || getPointerBase(StoredVal))
	  ignore = false;
      }
    }
      
    if(ignore)
      return WIRContinue;

  }
  
  if(R == AliasAnalysis::MustAlias) {

    FirstDef = 0; FirstNotDef = std::min(LoadSize, PtrSize); ReadOffset = 0;

    if(inst_is<StoreInst>(I)) {

      if(!getPointerBase(I->getOperand(0), NewPB))
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
      if(!getMIOrReadValue(I, 0, std::min(LoadSize, PtrSize), 0, LoadSize, NewPV, NewPB, error)) {

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
    if(getBaseAndConstantOffset(Ptr, WriteBase, WriteOffset)) {

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
	  if(!getMIOrReadValue(I, FirstDef, FirstNotDef, ReadOffset, LoadSize, NewPV, NewPB, error)) {
	
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

  UsedInstructions.push_back(I);

  std::string error;
  if(!addPartialVal(NewPV, NewPB, error, I, IA, FirstDef, FirstNotDef, cacheAllowed, true)) {
    // Couldn't perform some implicit cast, or encountered a conflict
    NLFWFail(error);
  }

  return WIRStopThisPath;

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

      return addPartialVal(GPV, error, 0, 0, 0, FirstNotDef, true, false);

    }

  }

  setPBOverdef("Reached top", true);
  return false;

}

bool* NormalLoadForwardWalker::getValidBuf() {

  return resultPV.getValidArray(LoadSize);

}

void NormalLoadForwardWalker::_addPBDefn(PointerBase& MergeWith, PointerBase& NewPB) {

  bool WasOverdef = MergeWith.Overdef;
  MergeWith.merge(NewPB);
  if(MergeWith.Overdef && (!WasOverdef) && (!NewPB.Overdef))
    OverdefReasons.push_back("Fan-in");

}

void NormalLoadForwardWalker::addPBDefn(PointerBase& NewPB, bool cacheAllowed) {

  _addPBDefn(Result, NewPB);
  if(activeCacheEntry && cacheAllowed)
    _addPBDefn(*activeCacheEntry, NewPB);

}

void NormalLoadForwardWalker::setPBOverdef(std::string reason, bool cacheAllowed) {
  OverdefReasons.push_back(reason);
  Result = PointerBase::getOverdef();
  if(activeCacheEntry && cacheAllowed)
    *activeCacheEntry = PointerBase::getOverdef();
}

void NormalLoadForwardWalker::cancelCache() {

  if(activeCacheEntry) {

    LFCacheKey Key = LFCK(optimisticBB, LoadPtrBase, LoadPtrOffset, LoadSize);
    optimisticIA->deleteLFPBCacheEntry(Key);
    activeCacheEntry = 0;

  }

}

bool NormalLoadForwardWalker::blockedByUnexpandedCall(ShadowValue* I, void* Ctx) {

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

bool NormalLoadForwardWalker::mayAscendFromContext(IntegrationAttempt* IA, void* Ctx) {

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

WalkInstructionResult NormalLoadForwardWalker::walkFromBlock(ShadowBB* BB, void* Ctx) {

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
 
ShadowValue NormalLoadForwardWalker::PVToSV(PartialVal& PV, raw_string_ostream& RSO) {

  uint64_t LoadSize = (TD->getTypeSizeInBits(originalType) + 7) / 8;

  // Try to use an entire value:
  if(PV.isTotal()) {

    ShadowValue Res = PV.TotalSV;
    const Type* sourceType = Res.getType();
    if(Res.isVaArg() || allowTotalDefnImplicitCast(sourceType, originalType)) {
      return Res;
    }
    else if(allowTotalDefnImplicitPtrToInt(sourceType, originalType, TD)) {
      LPDEBUG("Accepting " << itcache(Res) << " implicit ptrtoint to " << *(sourceType) << "\n");
      Res = getAsPtrAsInt(Res, originalType);
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
      Constant* extr = extractAggregateMemberAt(SalvageC, Offset, originalType, LoadSize, TD);
      if(extr)
	return ShadowValue(extr);

    }
    else {

      RSO << "NonConstBOps";
      return ShadowValue();

    }

  }

  // Finally build it from bytes.
  std::string error;
  if(!PV.convertToBytes(LoadSize, TD, error)) {
    RSO << error;
    return ShadowValue();
  }

  assert(PV.isByteArray());

  if(containsPointerTypes(originalType)) {

    // If we're trying to synthesise a pointer from raw bytes, only a null pointer is allowed.
    unsigned char* checkBuf = (unsigned char*)PV.partialBuf;
    for(unsigned i = 0; i < PV.partialBufBytes; ++i) {

      if(checkBuf[i]) {
	RSO << "Non-null Ptr Byteops";
	return ShadowValue();
      }

    }

  }

  return ShadowValue(constFromBytes((unsigned char*)PV.partialBuf, originalType, TD));

}

bool IntegrationAttempt::tryResolveLoadFromConstant(ShadowInstruction* LoadI, PointerBase& Result) {

  // A special case: loading from a symbolic vararg:

  PointerBase PtrPB;
  if(!getPointerBase(LoadI->getOperand(0), PtrPB))
    return false;

  if(PtrPB.type == ValSetTypeVarArg && PtrPB.Values.size() == 1) {
  
    ImprovedVal& IV = PtrPB.Values[0];
    if(IV.getVaArgType() != ValCtx::va_baseptr) {
    
      ShadowInstruction* PtrI = IV.V.getInst();
      PtrI->parent->IA->getVarArg(IV.Offset, Result);
      LPDEBUG("va_arg " << itcache(IV.V) << " " << IV.Offset << " yielded " << itcache(Result) << "\n");
    
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

  }

  ShadowValue PtrBase;
  int64_t PtrOffset;

  if(getBaseAndConstantOffset(LoadI->getOperand(0), PtrBase, PtrOffset)) {

    if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(Base.first)) {

      if(GV->isConstant()) {

	uint64_t LoadSize = (TD->getTypeSizeInBits(LoadI->getType()) + 7) / 8;
	const Type* FromType = GV->getInitializer()->getType();
	uint64_t FromSize = (TD->getTypeSizeInBits(FromType) + 7) / 8;

	if(Offset < 0 || Offset + LoadSize > FromSize) {
	  Result = ShadowValue();
	  return true;
	}

	Result = getPointerBase(ShadowValue(extractAggregateMemberAt(GV->getInitializer(), Offset, LoadI->getType(), LoadSize, TD)));
	if(!Result.isInval())
	  return true;

	int64_t CSize = TD->getTypeAllocSize(GV->getInitializer()->getType());
	if(CSize < Offset) {
	  
	  LPDEBUG("Can't forward from constant: read from global out of range\n");
	  Result = PointerBase();
	  return true;
	    
	}

	unsigned char* buf = (unsigned char*)alloca(LoadSize);
	memset(buf, 0, LoadSize);
	if(ReadDataFromGlobal(GV->getInitializer(), Offset, buf, LoadSize, *TD)) {

	  Result = getPointerBase(ShadowValue(constFromBytes(buf, LoadI->getType(), TD)));
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
      
  // Check for loads which are pointless to pursue further because they're known to be rooted on
  // a constant global but we're uncertain what offset within that global we're looking for:

  if(ShadowInstruction* SI = LoadI->getOperand(0).getInst()) {

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

PointerBase llvm::tryForwardLoadSubquery(ShadowInstruction* StartInst, ShadowValue LoadPtr, ShadowValue LoadPtrBase, int64_t LoadPtrOffset, uint64_t LoadSize, const Type* originalType, PartialVal& ResolvedSoFar, std::string& error) {

  bool* disableCaching = new bool;
  *disableCaching = false;

  if(LoadPtr.isInval()) {
    NormalLoadForwardWalker Walker(StartInst, LoadPtrBase, LoadPtrOffset, LoadSize, originalType, false, AA, TD, 0, 0, disableCaching, ResolvedSoFar);
    Walker.walk();
    
    if(Walker.Result.Overdef) {
      
      error = "";
      raw_string_ostream RSO(error);
      RSO << "SQ3 (" describePBWalker(Walker) << ")";
      
    }

    return Walker.Result;
  }
  else {
    NormalLoadForwardWalker Walker(StartInst, LoadPtr, LoadSize, originalType, false, AA, TD, 0, 0, disableCaching, ResolvedSoFar);
    Walker.walk();
    
    if(Walker.Result.Overdef) {
      
      error = "";
      raw_string_ostream RSO(error);
      RSO << "SQ1 (" describePBWalker(Walker) << ")";
      
    }

    return Walker.Result;
  }

}

  // Like normal load forwarding, but using a base+offset instead of a pointer.
  // This is used when forwarding through a copy instruction. 
PointerBase llvm::tryForwardLoadArtifical(ShadowInstruction* StartInst, ShadowValue LoadBase, int64_t LoadOffset, uint64_t LoadSize, const Type* targetType, bool* alreadyValidBytes, std::string& error) {

  PartialVal emptyPV;
  bool* disableCaching = new bool;
  *disableCaching = false;
  NormalLoadForwardWalker Walker(StartInst, LoadBase, LoadOffset, LoadSize, targetType, false, AA, TD, 0, 0, disableCaching, emptyPV);

  if(alreadyValidBytes) {
    bool* validBytes = Walker.getValidBuf();
    memcpy(validBytes, alreadyValidBytes, sizeof(bool) * LoadSize);
  }

  Walker.walk();

  if(Walker.Result.Overdef) {

    error = "";
    raw_string_ostream RSO(error);
    RSO << "SQ2 (" << describePBWalker(Walker) << ")";

  }

  return Walker.Result;

}

//// PBLF Interface

std::string llvm::describePBWalker(PBLoadForwardWalker& Walker) {
  
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

  PointerBase ConstResult;
  if(tryResolveLoadFromConstant(LI, ConstResult)) {
    NewPB = ConstResult;
    return true;
  }

  // Freed by the walker:
  bool* initialCtx = new bool;
  // Per-block context records whether we've passed the cache threshold.
  // Always start with 0, might immediately flip and cache in the starting block.
  // When we're outside the cache threshold we also switch to pessimistic mode
  // since everything before that point is a fixed certainty.
  *initialCtx = 0;

  const Type* TargetType = LI->getType();

  PartialVal emptyPV;
  NormalLoadForwardWalker Walker(LI, LI->getOperand(0),
				 AA->getTypeStoreSize(TargetType), TargetType,
				 !finalise, AA, TD,
				 CacheThresholdBB, CacheThresholdIA, initialCtx,
				 emptyPV);

  if(TargetType->isStructTy() || TargetType->isArrayTy()) {
    bool* validBytes = Walker.getValidBuf();
    markPaddingBytes(validBytes, TargetType, TD);
  }

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

  if(!finalise) {

    for(std::vector<ShadowInstruction*>::iterator it = Walker.UsedInstructions.begin(), it2 = Walker.UsedInstructions.end(); it != it2; ++it) {

      // Register our dependency on various instructions:
      // This is only useful during loop invariant analysis.
      if(std::find(LI, (*it)->indirectUsers.begin(), (*it)->indirectUsers.end()) ==  (*it)->indirectUsers.end())
	(*it)->indirectUsers.push_back(LI);

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

  if(Walker.isVarargTainted)
    contextTaintedByVarargs = true;

  NewPB = Walker.Result;
  return true;

}

