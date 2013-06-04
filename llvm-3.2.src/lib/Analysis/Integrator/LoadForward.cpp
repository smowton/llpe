
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/GlobalVariable.h"
#include "llvm/DataLayout.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/VFSCallModRef.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

bool IntAAProxy::isNoAliasPBs(ShadowValue Ptr1Base, int64_t Ptr1Offset, uint64_t Ptr1Size, ShadowValue Ptr2, uint64_t Ptr2Size) {

  return (tryResolveImprovedValSetSingles(Ptr1Base, Ptr1Offset, Ptr1Size, Ptr2, Ptr2Size, true) == SVNoAlias);

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

PartialVal::PartialVal(uint64_t nbytes) : TotalIV(), C(0), ReadOffset(0), partialValidBuf(0)  {

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
  TotalIV = Other.TotalIV;
  TotalIVType = Other.TotalIVType;
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
    partialBufBytes = nbytes;
  }

  return partialValidBuf;

}

static uint64_t markPaddingBytes(bool* pvb, Type* Ty, DataLayout* TD) {

  uint64_t marked = 0;

  if(StructType* STy = dyn_cast<StructType>(Ty)) {
    
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
  else if(ArrayType* ATy = dyn_cast<ArrayType>(Ty)) {

    uint64_t ECount = ATy->getNumElements();
    Type* EType = ATy->getElementType();
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

bool PartialVal::convertToBytes(uint64_t size, DataLayout* TD, std::string& error) {

  if(isByteArray())
    return true;

  PartialVal conv(size);
  if(!conv.combineWith(*this, 0, size, size, TD, error))
    return false;

  (*this) = conv;

  return true;

}

bool PartialVal::combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t LoadSize, DataLayout* TD, std::string& error) {

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

    Constant* TotalC = dyn_cast_or_null<Constant>(Other.TotalIV.V.getVal());
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

static bool containsPointerTypes(Type* Ty) {

  if(Ty->isPointerTy())
    return true;

  for(Type::subtype_iterator it = Ty->subtype_begin(), it2 = Ty->subtype_end(); it != it2; ++it) {

    if(containsPointerTypes(*it))
      return true;

  }

  return false;

}

ImprovedValSetSingle llvm::PVToPB(PartialVal& PV, raw_string_ostream& RSO, uint64_t Size, LLVMContext& Ctx) {

  ShadowValue NewSV = PVToSV(PV, RSO, Size, Ctx);
  if(NewSV.isInval())
    return ImprovedValSetSingle();

  ImprovedValSetSingle NewPB;
  if(!getImprovedValSetSingle(NewSV, NewPB)) {
    RSO << "PVToPB";
    return ImprovedValSetSingle();
  }

  return NewPB;

}

ShadowValue llvm::PVToSV(PartialVal& PV, raw_string_ostream& RSO, uint64_t Size, LLVMContext& Ctx) {

  // Otherwise try to use a sub-value:
  if(PV.isTotal() || PV.isPartial()) {

    // Try to salvage a total definition from a partial if this is a load clobbered by a store
    // of a larger aggregate type. This is to permit pointers and other non-constant forwardable values
    // to be moved about. In future our value representation needs to get richer to become a recursive type like
    // ConstantStruct et al.

    // Note that because you can't write an LLVM struct literal featuring a non-constant,
    // the only kinds of pointers this permits to be moved around are globals, since they are constant pointers.
    Constant* SalvageC = PV.isTotal() ? dyn_cast_or_null<Constant>(PV.TotalIV.V.getVal()) : PV.C;

    if(SalvageC) {

      uint64_t Offset = PV.isTotal() ? 0 : PV.ReadOffset;
      Constant* extr = extractAggregateMemberAt(SalvageC, Offset, 0, Size, GlobalTD);
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
  if(!PV.convertToBytes(Size, GlobalTD, error)) {
    RSO << error;
    return ShadowValue();
  }

  assert(PV.isByteArray());

  Type* targetType = Type::getIntNTy(Ctx, Size * 8);
  return ShadowValue(constFromBytes((unsigned char*)PV.partialBuf, targetType, GlobalTD));

}

bool IntegrationAttempt::tryResolveLoadFromConstant(ShadowInstruction* LoadI, ImprovedValSetSingle& Result, std::string& error) {

  // A special case: loading from a symbolic vararg:

  ImprovedValSetSingle PtrPB;
  if(!getImprovedValSetSingle(LoadI->getOperand(0), PtrPB))
    return false;

  if(PtrPB.SetType == ValSetTypeVarArg && PtrPB.Values.size() == 1) {
  
    ImprovedVal& IV = PtrPB.Values[0];
    if(IV.getVaArgType() != ImprovedVal::va_baseptr) {
    
      ShadowInstruction* PtrI = IV.V.getInst();
      PtrI->parent->IA->getVarArg(IV.Offset, Result);
      //LPDEBUG("va_arg " << itcache(IV.V) << " " << IV.Offset << " yielded " << printPB(Result) << "\n");
    
      return true;

    }

  }

  ShadowValue PtrBase;
  int64_t PtrOffset;

  if(getBaseAndConstantOffset(LoadI->getOperand(0), PtrBase, PtrOffset)) {

    if(ShadowGV* SGV = PtrBase.getGV()) {

      GlobalVariable* GV = SGV->G;

      if(GV->isConstant()) {

	uint64_t LoadSize = GlobalAA->getTypeStoreSize(LoadI->getType());
	Type* FromType = GV->getInitializer()->getType();
	uint64_t FromSize = GlobalAA->getTypeStoreSize(FromType);

	if(PtrOffset < 0 || PtrOffset + LoadSize > FromSize) {
	  error = "Const out of range";
	  Result = ImprovedValSetSingle::getOverdef();
	  return true;
	}

	getConstSubVal(GV->getInitializer(), PtrOffset, LoadSize, LoadI->getType(), Result);
	return true;

      }

    }

  }
      
  // Check for loads which are pointless to pursue further because they're known to be rooted on
  // a constant global but we're uncertain what offset within that global we're looking for:

  if(ShadowInstruction* SI = LoadI->getOperand(0).getInst()) {

    if(SI->i.PB.Values.size() > 0 && SI->i.PB.SetType == ValSetTypePB) {

      bool foundNonNull = false;
      bool foundNonConst = false;
      for(unsigned i = 0; i < SI->i.PB.Values.size(); ++i) {

	Value* BaseV = SI->i.PB.Values[i].V.getVal();

	if(BaseV && isa<ConstantPointerNull>(BaseV))
	  continue;

	foundNonNull = true;

	GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(BaseV);
	if((!GV) || !GV->isConstant())
	  foundNonConst = true;

      }

      if(!foundNonNull) {

	// Suppose that loading from a known null returns a null result.
	// TODO: convert this to undef, and thus rationalise the multi-load path.
	Type* defType = LoadI->getType();
	Constant* nullVal = Constant::getNullValue(defType);
	std::pair<ValSetType, ImprovedVal> ResultIV = getValPB(nullVal);
	Result = ImprovedValSetSingle::get(ResultIV.second, ResultIV.first);
	return true;

      }
      else if(!foundNonConst) {

	LPDEBUG("Load cannot presently be resolved, but is rooted on a constant global. Abandoning search\n");
	error = "Const pointer vague";
	Result = ImprovedValSetSingle::getOverdef();
	return true;

      }

    }

  }

  return false;

}

static bool shouldMultiload(ImprovedValSetSingle& PB) {

  if(PB.Overdef || PB.Values.size() == 0)
    return false;

  if(PB.SetType != ValSetTypePB)
    return false;

  uint32_t numNonNulls = 0;

  for(uint32_t i = 0, ilim = PB.Values.size(); i != ilim; ++i) {

    if(Value* V = PB.Values[i].V.getVal()) {
      if(isa<ConstantPointerNull>(V))
	continue;      
    }

    if(PB.Values[i].Offset == LLONG_MAX)
      return false;

    ++numNonNulls;

  }

  return numNonNulls >= 1;

}

static bool tryMultiload(ShadowInstruction* LI, ImprovedValSetSingle& NewPB, std::string& report) {

  uint64_t LoadSize = GlobalAA->getTypeStoreSize(LI->getType());

  // We already know that LI's PB is made up entirely of nulls and definite pointers.
  NewPB = ImprovedValSetSingle();
  ImprovedValSetSingle LIPB;
  getImprovedValSetSingle(LI->getOperand(0), LIPB);

  raw_string_ostream RSO(report); 

  for(uint32_t i = 0, ilim = LIPB.Values.size(); i != ilim && !NewPB.Overdef; ++i) {

    if(Value* V = LIPB.Values[i].V.getVal()) {
      if(isa<ConstantPointerNull>(V)) {

	Type* defType = LI->getType();
	Constant* nullVal = Constant::getNullValue(defType);
	std::pair<ValSetType, ImprovedVal> ResultIV = getValPB(nullVal);
	ImprovedValSetSingle NullPB = ImprovedValSetSingle::get(ResultIV.second, ResultIV.first);
	NewPB.merge(NullPB);
	continue;

      }
    }

    std::string ThisError;
    ImprovedValSetSingle ThisPB;

    readValRange(LIPB.Values[i].V, LIPB.Values[i].Offset, LoadSize, LI->parent, ThisPB, ThisError);

    if(!ThisPB.Overdef) {
      if(!ThisPB.coerceToType(LI->getType(), LoadSize, ThisError)) {
	NewPB.setOverdef();
      }
      else {
	NewPB.merge(ThisPB);
      }
    }
    else {
      NewPB.merge(ThisPB);
    }

    if(ThisPB.Overdef) {
	
      RSO << "Load " << itcache(LIPB.Values[i].V, true) << " -> " << ThisError;

    }
    else if(NewPB.Overdef) {
	
      RSO << "Loaded ";
      printPB(RSO, ThisPB, true);
      RSO << " -merge-> " << ThisError;

    }

  }

  return NewPB.isInitialised();

}

// Fish a value out of the block-local or value store for LI.
bool IntegrationAttempt::tryForwardLoadPB(ShadowInstruction* LI, ImprovedValSetSingle& NewPB, bool& loadedVararg) {

  ImprovedValSetSingle ConstResult;
  std::string error;
  if(tryResolveLoadFromConstant(LI, ConstResult, error)) {
    NewPB = ConstResult;
    if(NewPB.Overdef)
      optimisticForwardStatus[LI->invar->I] = error;
    return NewPB.isInitialised();
  }

  bool ret;
  std::string report;

  ImprovedValSetSingle LoadPtrPB;
  getImprovedValSetSingle(LI->getOperand(0), LoadPtrPB);
  if(shouldMultiload(LoadPtrPB)) {
    
    ret = tryMultiload(LI, NewPB, report);
    if(NewPB.SetType == ValSetTypeVarArg)
      loadedVararg = true;

  }
  else {

    // Load from a vague pointer -> Overdef.
    ret = true;
    raw_string_ostream RSO(report);
    RSO << "Load vague ";
    printPB(RSO, LoadPtrPB, true);
    NewPB.setOverdef();

  }

  optimisticForwardStatus[LI->invar->I] = report;
   
  return ret;

}

static ImprovedVal* getUniqueNonNullIV(ImprovedValSetSingle& PB) {

  ImprovedVal* uniqueVal = 0;
  
  for(uint32_t i = 0, ilim = PB.Values.size(); i != ilim; ++i) {

    if(Value* V = PB.Values[i].V.getVal()) {
      if(isa<ConstantPointerNull>(V))
	continue;
    }
    
    if(uniqueVal)
      return 0;
    else
      uniqueVal = &(PB.Values[i]);

  }

  return uniqueVal;

}

// Potentially dubious: report a must-alias relationship even if either of them may be null.
// The theory is that either a store-through or read-from a null pointer will kill the program,
// so we can safely assume they alias since either they do or the resulting code is not executed.
static bool PBsMustAliasIfStoredAndLoaded(ImprovedValSetSingle& PB1, ImprovedValSetSingle& PB2) {

  ImprovedVal* IV1;
  ImprovedVal* IV2;

  if((!(IV1 = getUniqueNonNullIV(PB1))) || (!(IV2 = getUniqueNonNullIV(PB2))))
    return false;
  
  return (IV1->Offset != LLONG_MAX && IV1->Offset == IV2->Offset && IV1->V == IV2->V);

}

SVAAResult llvm::tryResolveImprovedValSetSingles(ImprovedValSetSingle& PB1, uint64_t V1Size, ImprovedValSetSingle& PB2, uint64_t V2Size, bool usePBKnowledge) {

  if(V1Size == V2Size && PBsMustAliasIfStoredAndLoaded(PB1, PB2))
    return SVMustAlias;

  for(unsigned i = 0; i < PB1.Values.size(); ++i) {

    for(unsigned j = 0; j < PB2.Values.size(); ++j) {

      if(!basesAlias(PB1.Values[i].V, PB2.Values[j].V))
	continue;

      if(PB1.Values[i].Offset == LLONG_MAX || PB2.Values[j].Offset == LLONG_MAX)
	return SVPartialAlias;
	   
      if(!((V2Size != AliasAnalysis::UnknownSize && 
	    PB1.Values[i].Offset >= (int64_t)(PB2.Values[j].Offset + V2Size)) || 
	   (V1Size != AliasAnalysis::UnknownSize && 
	    (int64_t)(PB1.Values[i].Offset + V1Size) <= PB2.Values[j].Offset)))
	return SVPartialAlias;

    }

  }
	
  return SVNoAlias;

}

SVAAResult llvm::tryResolveImprovedValSetSingles(ShadowValue V1Base, int64_t V1Offset, uint64_t V1Size, ShadowValue V2, uint64_t V2Size, bool usePBKnowledge) {
      
  ImprovedValSetSingle PB1(ValSetTypePB);
  PB1.insert(ImprovedVal(V1Base, V1Offset));
  ImprovedValSetSingle PB2;
  if(!getImprovedValSetSingle(V2, PB2))
    return SVMayAlias;
      
  if(PB2.Overdef || PB2.Values.size() == 0)
    return SVMayAlias;

  if(PB2.SetType != ValSetTypePB)
    return SVMayAlias;

  return tryResolveImprovedValSetSingles(PB1, V1Size, PB2, V2Size, usePBKnowledge);

}

SVAAResult llvm::tryResolveImprovedValSetSingles(ShadowValue V1, uint64_t V1Size, ShadowValue V2, uint64_t V2Size, bool usePBKnowledge) {
      
  ImprovedValSetSingle PB1, PB2;
  if((!getImprovedValSetSingle(V1, PB1)) || (!getImprovedValSetSingle(V2, PB2)))
    return SVMayAlias;
      
  if(PB1.Overdef || PB1.Values.size() == 0 || PB2.Overdef || PB2.Values.size() == 0)
    return SVMayAlias;

  if(PB1.SetType != ValSetTypePB || PB2.SetType != ValSetTypePB)
    return SVMayAlias;

  return tryResolveImprovedValSetSingles(PB1, V1Size, PB2, V2Size, usePBKnowledge);
       
}

#define LFV3(x) do {} while(0)
//#define LFV3(x) x

DenseMap<ShadowValue, LocStore>& ShadowBB::getWritableStoreMap() {

  release_assert(localStore && "getWritableStoreMap without a local store?");
  LocalStoreMap* newMap = localStore->getWritableStoreMap();
  if(newMap != localStore) {
    
    // Store the new one:
    LFV3(errs() << "Stored new map " << newMap << "\n");
    localStore = newMap;

  }

  return newMap->store;

}

LocalStoreMap* LocalStoreMap::getWritableStoreMap() {

  // Refcount == 1 means we can just write in place.
  if(refCount == 1) {
    LFV3(errs() << "Local map " << this << " already writable\n");
    return this;
  }

  // COW break: copy the map and either share or copy its entries.
  LFV3(errs() << "COW break local map " << this << " with " << store.size() << " entries\n");
  LocalStoreMap* newMap = new LocalStoreMap();
  for(DenseMap<ShadowValue, LocStore>::iterator it = store.begin(), it2 = store.end(); it != it2; ++it) {

    if(ImprovedValSetSingle* OldSet = dyn_cast<ImprovedValSetSingle>(it->second.store)) {

      LFV3(errs() << "Copy single val\n");
      // Individual valsets are not sharable: copy.
      ImprovedValSetSingle* NewSet = new ImprovedValSetSingle(*OldSet);
      newMap->store[it->first] = LocStore(NewSet);

    }
    else {

      ImprovedValSetMulti* SharedSet = cast<ImprovedValSetMulti>(it->second.store);
      LFV3(errs() << "Share multimap " << SharedSet << "\n");
      SharedSet->MapRefCount++;
      newMap->store[it->first] = LocStore(SharedSet);

    }

  }

  newMap->allOthersClobbered = allOthersClobbered;

  // Drop reference on the existing map (can't destroy it):
  refCount--;

  return newMap;

}

LocStore& ShadowBB::getWritableStoreFor(ShadowValue& V, int64_t Offset, uint64_t Size, bool willWriteSingleObject) {

  // We're about to write to memory location V + Offset -> Offset+Size. 
  // We must return a LocStore for that value that can be updated (i.e. is not shared).

  // Can write direct to the base store if we're sure this write is "for good".
  LocStore* ret = 0;
  if(status == BBSTATUS_CERTAIN && (!inAnyLoop) && !localStore->allOthersClobbered) {
    LFV3(errs() << "Use base store for " << IA->F.getName() << " / " << IA->SeqNumber << " / " << invar->BB->getName() << "\n");
    ret = &V.getBaseStore();
  }

  // Otherwise we need to write into the block-local store map. COW break it if necessary:
  bool writeWholeObject = (Offset == 0 && (Size == ULONG_MAX || Size == V.getAllocSize()));
   
  if(!ret) {

    DenseMap<ShadowValue, LocStore>& storeMap = getWritableStoreMap();
    LocStore newStore;
    std::pair<DenseMap<ShadowValue, LocStore>::iterator, bool> insResult = storeMap.insert(std::make_pair(V, newStore));
    ret = &(insResult.first->second);
  
    if(insResult.second) {

      // There wasn't an entry in the local map. Make a Single or Multi store depending on
      // whether we're about to cover the whole store or not:
      if(writeWholeObject && willWriteSingleObject) {
	LFV3(errs() << "Create new store with blank single\n");
	ret->store = new ImprovedValSetSingle();
      }
      else {
	// Defer the rest of the multimap to the base object.
	ImprovedValSetMulti* M = new ImprovedValSetMulti(V);
	if(writeWholeObject) {
	  M->Underlying = 0;
	}
	else {
	  M->Underlying = V.getBaseStore().store->getReadableCopy();
	  LFV3(errs() << "Create new store with multi based on " << M->Underlying << "\n");
	  LFV3(M->print(errs()));
	}
	ret->store = M;
      }

      return *ret;

    }
    else {

      LFV3(errs() << "Use existing store " << insResult.first->second.store << "\n");

    }

  }

  // There was already an entry in the local map or base store.

  if(writeWholeObject && willWriteSingleObject) {
      
    // If we're about to overwrite the whole thing with a single, convert a multi to a single.

    if(ImprovedValSetMulti* M = dyn_cast<ImprovedValSetMulti>(ret->store)) {
	
      // Might delete the Multi:
      M->dropReference();
      ret->store = new ImprovedValSetSingle();
      LFV3(errs() << "Free multi " << M << " and replace with single " << ret->store << "\n");

    }
    else {

      LFV3(errs() << "Retain existing single " << ret->store << "\n");

    }

    // Or retain an existing single as-is, they're always private and writable.

  }
  else {

    // If we're doing a partial overwrite, make sure a multi is writable and promote
    // a single to a multi with that single as base.
    if(!ret->store->isWritableMulti()) {

      ImprovedValSetMulti* NewIMap = new ImprovedValSetMulti(V);
      if(isa<ImprovedValSetMulti>(ret->store))
	LFV3(errs() << "Break shared multi " << ret->store << " -> " << NewIMap << "\n");
      else
	LFV3(errs() << "Break single -> multi " << ret->store << " -> " << NewIMap << "\n");
      if(writeWholeObject) {
	NewIMap->Underlying = 0;
	ret->store->dropReference();
      }
      else {
	NewIMap->Underlying = ret->store;
	// M's refcount remains unchanged, it's just now referenced as a base rather than
	// being directly used here.
      }
      ret->store = NewIMap;
	
    }
    else {
      // Else already a local map, nothing to do.
      LFV3(errs() << "Retain existing writable multi " << ret->store << "\n");
    }

  }

  return *ret;
  
}

bool llvm::addIVSToPartialVal(ImprovedValSetSingle& IVS, uint64_t IVSOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string& error) {

  release_assert(PV && PV->type == PVByteArray && "Must allocate PV before calling addIVSToPartialVal");

  // For now we forbid building from bytes when an input is set-typed:
  if(IVS.Overdef || IVS.Values.size() != 1)
    return false;
  // And also if the value that would be merged is not constant-typed:
  if(IVS.SetType != ValSetTypeScalar && IVS.SetType != ValSetTypeScalarSplat)
    return false;

  PartialVal NewPV;
  Constant* DefC = cast<Constant>(IVS.Values[0].V.getVal());
  if(IVS.SetType == ValSetTypeScalar) {
    NewPV = PartialVal::getPartial(DefC, IVSOffset);
  }
  else {
    // Splat of i8:
    uint8_t SplatVal = (uint8_t)(cast<ConstantInt>(DefC)->getLimitedValue());
    NewPV = PartialVal::getByteArray(Size);
    
    uint8_t* buffer = (uint8_t*)NewPV.partialBuf;
    bool* validBuf = (bool*)NewPV.partialValidBuf;
    
    for(uint64_t i = 0; i < Size; ++i) {
      buffer[i] = SplatVal;
      validBuf[i] = true;
    }

    NewPV.loadFinished = true;
  }

  if(!PV->combineWith(NewPV, PVOffset, PVOffset + Size, PV->partialBufBytes, GlobalTD, error))
    return false;

  return true;

}

void llvm::readValRangeFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, ImprovedValSetSingle& Result, PartialVal*& ResultPV, std::string& error) {

  ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(store);
  uint64_t IVSSize = V.getAllocSize();
  ImprovedValSetMulti* IVM;
  ImprovedValSetMulti::MapIt it;

  LFV3(errs() << "Read range " << Offset << "-" << (Offset+Size) << "\n");

  if(!IVS) {

    // Check for a multi-member that wholly defines the target value:

    IVM = cast<ImprovedValSetMulti>(store);
    it = IVM->Map.find(Offset);

    if(it != IVM->Map.end() && it.start() <= Offset && it.stop() >= (Offset + Size)) {

      IVS = &it.val();
      IVSSize = it.stop() - it.start();
      Offset -= it.start();
      LFV3(errs() << "Read fully defined by multi subval " << it.start() << "-" << it.stop() << "\n");

    }

  }

  if(IVS) {

    if(!ResultPV) {

      // Try to extract the entire value
      if(IVSSize == Size && Offset == 0) {
	Result = *IVS;
	LFV3(errs() << "Return whole value\n");
	return;
      }
      
      // Otherwise we need to extract a sub-value: only works on constants:
      bool rejectHere = IVS->Overdef || (IVS->SetType != ValSetTypeScalar && IVS->SetType != ValSetTypeScalarSplat);
      if(rejectHere) {
	LFV3(errs() << "Reject: non-scalar\n");
	Result = ImprovedValSetSingle::getOverdef();
	return;
      }
      
      if(IVS->SetType == ValSetTypeScalar) {
      
	bool extractWorked = true;

	for(uint32_t i = 0, endi = IVS->Values.size(); i != endi; ++i) {
	
	  Constant* bigConst = cast<Constant>(IVS->Values[i].V.getVal());
	  Constant* smallConst = extractAggregateMemberAt(bigConst, Offset, 0, Size, GlobalTD);
	  if(smallConst) {

	    ShadowValue SV(smallConst);
	    ImprovedValSetSingle NewIVS;
	    getImprovedValSetSingle(SV, NewIVS);
	    Result.merge(NewIVS);
	    if(Result.Overdef)
	      return;

	  }
	  else {
	    
	    LFV3(errs() << "Extract-aggregate failed, fall through\n");
	    extractWorked = false;

	  }
					  
	}

	if(extractWorked)
	  return;

      }

      // Else fall through to bytewise case:
      ResultPV = new PartialVal(Size);

    }

    if(!addIVSToPartialVal(*IVS, Offset, 0, Size, ResultPV, error)) {
      
      LFV3(errs() << "Partial build failed\n");
      delete ResultPV;
      ResultPV = 0;
      Result = ImprovedValSetSingle::getOverdef();

    }
    else {

      release_assert(ResultPV->isComplete() && "Fetch defined by a Single value but not complete?");
      LFV3(errs() << "Built from bytes\n");

    }

    return;

  }

  // If we get to here the value is not wholly covered by this Multi map. Add what we can and defer:
  release_assert(IVM && "Fell through without a multi?");

  LFV3(errs() << "Build from bytes (multi path)\n");

  for(; it != IVM->Map.end() && it.start() < (Offset + Size); ++it) {

    if(!ResultPV)
      ResultPV = new PartialVal(Size);

    uint64_t FirstReadByte = std::max(Offset, it.start());
    uint64_t LastReadByte = std::min(Offset + Size, it.stop());

    LFV3(errs() << "Merge subval at " << FirstReadByte << "-" << LastReadByte << "\n");

    if(!addIVSToPartialVal(it.val(), FirstReadByte - it.start(), FirstReadByte - Offset, LastReadByte - FirstReadByte, ResultPV, error)) {
      delete ResultPV;
      ResultPV = 0;
      Result = ImprovedValSetSingle::getOverdef();
      return;
    }

  }
  
  if((!ResultPV) || !ResultPV->isComplete()) {
      
    // Try the next linked map (one should exist:)
    release_assert(IVM->Underlying && "Value not complete, but no underlying map?");
    LFV3(errs() << "Defer to next map: " << IVM->Underlying << "\n");
    readValRangeFrom(V, Offset, Size, ReadBB, IVM->Underlying, Result, ResultPV, error);
      
  }

}

void llvm::readValRange(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSetSingle& Result, std::string& error) {

  // Try to make an IVS representing the block-local value of V+Offset -> Size.
  // Limitations for now: because our output is a single IVS, non-scalar types may only be described
  // if they correspond to a whole object.

  LocStore* firstStore;

  LFV3(errs() << "Start read " << Offset << "-" << (Offset + Size) << "\n");

  DenseMap<ShadowValue, LocStore>::iterator it = ReadBB->localStore->store.find(V);
  if(it == ReadBB->localStore->store.end()) {
    if(ReadBB->localStore->allOthersClobbered) {
      LFV3(errs() << "Location not in local map and allOthersClobbered\n");
      Result.setOverdef();
      return;
    }
    LFV3(errs() << "Starting at base store\n");
    firstStore = &(V.getBaseStore());
  }
  else {
    LFV3(errs() << "Starting at local store\n");
    firstStore = &(it->second);
  }

  PartialVal* ResultPV = 0;
  readValRangeFrom(V, Offset, Size, ReadBB, firstStore->store, Result, ResultPV, error);

  if(ResultPV) {

    LFV3(errs() << "Read used a PV\n");
    raw_string_ostream RSO(error);
    Result = PVToPB(*ResultPV, RSO, Size, V.getLLVMContext());
    delete ResultPV;

  }

  release_assert(Result.isInitialised());

}

bool ImprovedValSetSingle::coerceToType(Type* Target, uint64_t TargetSize, std::string& error) {

  Type* Source = Values[0].V.getType();
  
  // All casts ignored for VAs:
  if(SetType == ValSetTypeVarArg)
    return true;

  // Allow implicit ptrtoint and bitcast between pointer types
  // without modifying anything:
  if(allowTotalDefnImplicitCast(Source, Target))
    return true;
  if(allowTotalDefnImplicitPtrToInt(Source, Target, GlobalTD))
    return true;

  if(SetType != ValSetTypeScalar) {
    error = "Non-scalar coercion";
    return false;
  }

  // Finally reinterpret cast each member:
  for(uint32_t i = 0, iend = Values.size(); i != iend; ++i) {

    PartialVal PV = PartialVal::getPartial(cast<Constant>(Values[i].V.getVal()), 0);
    if(!PV.convertToBytes(TargetSize, GlobalTD, error))
      return false;

    if(containsPointerTypes(Target)) {

      // If we're trying to synthesise a pointer from raw bytes, only a null pointer is allowed.
      unsigned char* checkBuf = (unsigned char*)PV.partialBuf;
      for(unsigned i = 0; i < PV.partialBufBytes; ++i) {
	
	if(checkBuf[i]) {
	  error = "Cast non-zero to pointer";
	  return false;
	}
	
      }

    }

    Values[i].V = ShadowValue(constFromBytes((unsigned char*)PV.partialBuf, Target, GlobalTD));

  }

  return true;

}

void llvm::executeStoreInst(ShadowInstruction* StoreSI) {

  // Get written location:
  ShadowBB* StoreBB = StoreSI->parent;
  ShadowValue Ptr = StoreSI->getOperand(1);
  uint64_t PtrSize = GlobalAA->getTypeStoreSize(StoreSI->invar->I->getOperand(0)->getType());

  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.Overdef || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");

  ShadowValue Val = StoreSI->getOperand(0);
  ImprovedValSetSingle ValPB;
  getImprovedValSetSingle(Val, ValPB);

  executeWriteInst(PtrSet, ValPB, PtrSize, StoreBB);

}

void llvm::executeMemsetInst(ShadowInstruction* MemsetSI) {

  ShadowBB* MemsetBB = MemsetSI->parent;
  ShadowValue Ptr = MemsetSI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.Overdef || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");
  
  ConstantInt* LengthCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemsetSI->getCallArgOperand(2)));
  ConstantInt* ValCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemsetSI->getCallArgOperand(1)));

  ImprovedValSetSingle ValSet;

  if(LengthCI && ValCI) {
   
    ValSet.SetType = ValSetTypeScalarSplat;
    ImprovedVal IV(ShadowValue(ValCI), LengthCI->getLimitedValue());
    ValSet.insert(IV);

  }
  else {

    ValSet.setOverdef();

  }

  executeWriteInst(PtrSet, ValSet, LengthCI ? LengthCI->getLimitedValue() : ULONG_MAX, MemsetBB);
  
}

#define IVSR(x, y, z) std::make_pair(std::make_pair(x, y), z)
#define AddIVSConst(x, y, z) do { std::pair<ValSetType, ImprovedVal> V = getValPB(z); Dest.push_back(IVSR(x + OffsetAbove, x + y + OffsetAbove, ImprovedValSetSingle::get(V.second, V.first))); } while(0);

void llvm::getIVSSubVals(ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest) {

  // Subvals only allowed for scalars:

  if(Src.Overdef || Src.Values.size() == 0) {
    Dest.push_back(IVSR(OffsetAbove + Offset, OffsetAbove + Offset + Size, Src));
    return;
  }

  switch(Src.SetType) {
  case ValSetTypeScalar:
    break;
  case ValSetTypeScalarSplat:
  case ValSetTypeVarArg:
    Dest.push_back(IVSR(OffsetAbove + Offset, OffsetAbove + Offset + Size, Src));
    return;
  default:
    if(Offset == 0) {
      Type* SrcTy = Src.Values[0].V.getType();
      uint64_t SrcSize = GlobalAA->getTypeStoreSize(SrcTy);
      if(Size == SrcSize) {
	Dest.push_back(IVSR(OffsetAbove + Offset, OffsetAbove + Offset + Size, Src));
	return;
      }
    }
    // Otherwise can't take a subvalue:
    Dest.push_back(IVSR(OffsetAbove + Offset, OffsetAbove + Offset + Size, ImprovedValSetSingle::getOverdef()));
    return;
  }

  if(Src.Values.size() == 1) {

    // Grab sub-constants:
    getConstSubVals(cast_val<Constant>(Src.Values[0].V), Offset, Size, OffsetAbove, Dest);

  }
  else {

    // Punt on the tricky business of merging potentially misaligned sets of constants for now; only allow
    // subvalues expressible as a single constant.

    ImprovedValSetSingle DestSingle;

    for(uint32_t i = 0, endi = Src.Values.size(); i != endi; ++i) {
	
      Constant* bigConst = cast<Constant>(Src.Values[i].V.getVal());
    
      Constant* smallConst = getSubConst(bigConst, Offset, Size);
      if(!smallConst) {
	DestSingle.setOverdef();
	break;
      }

      ShadowValue SV(smallConst);
      ImprovedValSetSingle NewIVS;
      getImprovedValSetSingle(SV, NewIVS);
      DestSingle.merge(NewIVS);
					  
    }

    Dest.push_back(IVSR(OffsetAbove + Offset, OffsetAbove + Offset + Size, DestSingle));

  }
  
}

void llvm::getIVSSubVal(ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, ImprovedValSetSingle& Dest) {

  SmallVector<IVSRange, 4> Subvals;
  getIVSSubVals(Src, Offset, Size, 0, Subvals);
  if(Subvals.size() != 1)
    Dest.setOverdef();
  else
    Dest = Subvals[0].second;
  
}

// Describe FromC[Offset:Offset+TargetSize] as a series of PBs with extents.
// Makes some effort to coalesce PBs (e.g. using a big ConstantArray rather than an extent per element) but could do more.
// Writes Overdef extents where we couldn't read the source constant.
// OffsetAbove specifies all recorded extents should have OffsetAbove added; saves post-processing when
// making a subquery.
void llvm::getConstSubVals(Constant* FromC, uint64_t Offset, uint64_t TargetSize, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest) {

  uint64_t FromSize = GlobalAA->getTypeStoreSize(FromC->getType());

  if(Offset == 0 && TargetSize == FromSize) {
    AddIVSConst(0, TargetSize, FromC);
    return;
  }

  if(Offset + TargetSize > FromSize) {

    // Out of bounds read on the right. Define as much as we can:
    getConstSubVals(FromC, Offset, FromSize - Offset, OffsetAbove, Dest);
    // ...then overdef the rest.
    Dest.push_back(IVSR(FromSize, (Offset + TargetSize) - FromSize, ImprovedValSetSingle::getOverdef()));
    return;

  }

  // Reading a sub-value. Cases:
  // * Array type / Struct type: Grab sub-elements whole as far as possible.
  // * ConstantDataSequential / ConstantAggregateZero / vectors / primitives: Do byte-wise constant extraction.

  if(ConstantArray* CA = dyn_cast<ConstantArray>(FromC)) {

    Type* EType = CA->getType()->getElementType();
    uint64_t ESize = GlobalTD->getTypeAllocSize(EType);    

    uint64_t StartE = Offset / ESize;
    uint64_t StartOff = Offset % ESize;

    uint64_t EndE = (Offset + TargetSize) / ESize;
    uint64_t EndOff = (Offset + TargetSize) % ESize;

    if(StartOff) {

      // Read a partial on the left:
      uint64_t ThisReadSize;
      if(EndE == StartE)
	ThisReadSize = EndOff - StartOff;
      else
	ThisReadSize = ESize - StartOff;

      getConstSubVals(CA->getAggregateElement(StartE), StartOff, ThisReadSize, OffsetAbove + (ESize * StartE), Dest);

      if(StartE == EndE)
	return;

      StartE++;
      StartOff = 0;

      if(StartE == EndE && EndOff == 0)
	return;

    }

    // Read as many whole elements as possible:
    if(EndE - StartE == 1) {

      AddIVSConst(StartE * ESize, ESize, CA->getAggregateElement(StartE));

    }
    else if(EndE - StartE > 1) {

      // Make a sub-array.
      SmallVector<Constant*, 128> subArray(EndE - StartE);
      for(uint64_t i = StartE, iend = EndE; i != iend; ++i)
	subArray[i - StartE] = CA->getAggregateElement(i);

      AddIVSConst(StartE * ESize, ESize * (EndE - StartE), ConstantArray::get(CA->getType(), subArray));

    }

    // Read final subelement
    if(EndOff)
      getConstSubVals(CA->getAggregateElement(EndE), 0, EndOff, OffsetAbove + (ESize * EndE), Dest);

  }
  else if(ConstantStruct* CS = dyn_cast<ConstantStruct>(FromC)) {

    const StructLayout* SL = GlobalTD->getStructLayout(CS->getType());
    if(!SL) {
      DEBUG(dbgs() << "Couldn't get struct layout for type " << *(CS->getType()) << "\n");
      Dest.push_back(IVSR(Offset, TargetSize, ImprovedValSetSingle::getOverdef()));
      return;
    }

    uint64_t StartE = SL->getElementContainingOffset(Offset);
    uint64_t StartOff = Offset - SL->getElementOffset(StartE);
    uint64_t EndE = SL->getElementContainingOffset(Offset + TargetSize);
    uint64_t EndOff = (Offset + TargetSize) - SL->getElementOffset(EndE);

    if(StartOff) {

      // Read a partial on the left:
      Constant* StartC = CS->getAggregateElement(StartE);
      uint64_t StartCSize = GlobalAA->getTypeStoreSize(StartC->getType());
      uint64_t ThisReadSize;

      if(EndE == StartE)
	ThisReadSize = EndOff - StartOff;
      else
	ThisReadSize = StartCSize - StartOff;

      getConstSubVals(StartC, StartOff, ThisReadSize, OffsetAbove + SL->getElementOffset(StartE), Dest);

      if(StartE == EndE)
	return;

      StartE++;
      StartOff = 0;

      if(StartE == EndE && EndOff == 0)
	return;

    }

    // Read whole elements:
    for(;StartE < EndE; ++StartE) {

      Constant* E = CS->getAggregateElement(StartE);
      uint64_t ESize = GlobalAA->getTypeStoreSize(E->getType());
      uint64_t ThisOff = SL->getElementOffset(StartE);
      AddIVSConst(ThisOff, ESize, E);

      // Padding?
      if(StartE + 1 < CS->getType()->getNumElements()) {
	uint64_t NextOff = SL->getElementOffset(StartE + 1);
	uint64_t PaddingBytes = (NextOff - (ThisOff + ESize));
	if(PaddingBytes) {

	  Type* PaddingType = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
	  Constant* Padding = UndefValue::get(PaddingType);
	  AddIVSConst(ThisOff + ESize, PaddingBytes, Padding);

	}
      }

    }

    // Read final subelement
    if(EndOff) {
      Constant* E = CS->getAggregateElement(EndE);
      getConstSubVals(E, 0, EndOff, OffsetAbove + SL->getElementOffset(EndE), Dest);
    }

  }
  else {

    // C is a primitive, constant-aggregate-zero, constant-data-array or similar.
    // Attempt bytewise extraction and present as an integer.
    SmallVector<uint8_t, 16> Buffer(TargetSize);
    if(ReadDataFromGlobal(FromC, Offset, Buffer.data(), TargetSize, *GlobalTD)) {

      Type* Target = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
      Constant* SubC = constFromBytes((uint8_t*)Buffer.data(), Target, GlobalTD);
      AddIVSConst(Offset, TargetSize, SubC);
      
    }
    else {

      Dest.push_back(IVSR(Offset, TargetSize, ImprovedValSetSingle::getOverdef()));      

    }

  }
  
}

Constant* llvm::valsToConst(SmallVector<IVSRange, 4>& subVals, uint64_t TargetSize, Type* targetType) {

  if(subVals.size() == 0)
    return 0;

  for(SmallVector<IVSRange, 4>::iterator it = subVals.begin(), itend = subVals.end();
      it != itend; ++it) {

    if(it->second.Overdef)
      return 0;

  }

  if(subVals.size() == 1)
    return cast_val<Constant>(subVals[0].second.Values[0].V);

  // Otherwise attempt a big synthesis from bytes.
  SmallVector<uint8_t, 16> buffer(TargetSize);

  for(SmallVector<IVSRange, 4>::iterator it = subVals.begin(), itend = subVals.end();
      it != itend; ++it) {

    uint8_t* ReadPtr = &(buffer.data()[it->first.first]);
    if(!ReadDataFromGlobal(cast_val<Constant>(it->second.Values[0].V), 0, ReadPtr, it->first.second - it->first.first, *GlobalTD))
      return 0;

  }

  if(!targetType)
    targetType = Type::getIntNTy(subVals[0].second.Values[0].V.getLLVMContext(), TargetSize * 8);

  return constFromBytes((uint8_t*)buffer.data(), targetType, GlobalTD);

}

void llvm::getConstSubVal(Constant* FromC, uint64_t Offset, uint64_t TargetSize, Type* TargetType, ImprovedValSetSingle& Result) {

  SmallVector<IVSRange, 4> subVals;
  getConstSubVals(FromC, Offset, TargetSize, -((int64_t)Offset), subVals);

  if(subVals.size() != 1) {
    if(Constant* C = valsToConst(subVals, TargetSize, TargetType)) {
      std::pair<ValSetType, ImprovedVal> V = getValPB(C);
      Result = ImprovedValSetSingle::get(V.second, V.first);
    }
    else {
      Result.setOverdef();
    }
  }
  else {
    Result = subVals[0].second;
    if(TargetType) {
      std::string ign;
      Result.coerceToType(TargetType, TargetSize, ign);
    }
  }

}

Constant* llvm::getSubConst(Constant* FromC, uint64_t Offset, uint64_t TargetSize, Type* targetType) {
  
  SmallVector<IVSRange, 4> subVals;
  getConstSubVals(FromC, Offset, TargetSize, -((int64_t)Offset), subVals);

  return valsToConst(subVals, TargetSize, targetType);

}

void llvm::replaceRangeWithPB(ImprovedValSet* Target, ImprovedValSetSingle& NewVal, int64_t Offset, uint64_t Size) {

  if(ImprovedValSetSingle* S = dyn_cast<ImprovedValSetSingle>(Target)) {
    *S = NewVal;
  }
  else {
    
    ImprovedValSetMulti* M = cast<ImprovedValSetMulti>(Target);

    if(Size == ULONG_MAX) {

      release_assert(NewVal.Overdef && "Indefinite write with non-clobber value?");
      
    }

    clearRange(M, Offset, Size);
    M->Map.insert(Offset, Offset + Size, NewVal);

    M->CoveredBytes += Size;
    if(M->Underlying && M->CoveredBytes == M->AllocSize) {

      // This Multi now defines the whole object: drop the underlying object as it never shows through.
      M->Underlying->dropReference();
      M->Underlying = 0;

    }

  }

}

void llvm::clearRange(ImprovedValSetMulti* M, uint64_t Offset, uint64_t Size) {

  ImprovedValSetMulti::MapIt found = M->Map.find(Offset);
  if(found == M->Map.end())
    return;

  uint64_t LastByte = Offset + Size;

  if(found.start() < Offset) {

    ImprovedValSetSingle RHS;
    if(LastByte < found.stop()) {

      // Punching a hole in the middle of a large value:
      // keep a copy to derive the RHS remainder later.
      RHS = *found;

    }

    if(canTruncate(found.val())) {
      M->CoveredBytes -= (found.stop() - Offset);
      truncateRight(found, Offset - found.start());
    }
    else {
      found.val().setOverdef();
    }
    uint64_t oldStop = found.stop();
    found.setStopUnchecked(Offset);

    if(RHS.isInitialised()) {

      ++found;
      found.insert(LastByte, oldStop, RHS);
      truncateLeft(found, oldStop - LastByte);
      M->CoveredBytes += (oldStop - LastByte);
      return;

    }

    ++found;

  }
  
  while(found != M->Map.end() && found.start() < LastByte && found.stop() <= LastByte) {

    // Implicitly bumps the iterator forwards:
    M->CoveredBytes -= (found.stop() - found.start());
    found.erase();

  }

  if(found != M->Map.end() && found.start() < LastByte) {

    if(canTruncate(found.val())) {
      truncateLeft(found, found.stop() - LastByte);
    }
    else {
      found.val().setOverdef();
    }
    M->CoveredBytes -= (LastByte - found.start());
    found.setStartUnchecked(LastByte);

  }

}

void llvm::replaceRangeWithPBs(ImprovedValSet* Target, SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size) {

  if(ImprovedValSetSingle* S = dyn_cast<ImprovedValSetSingle>(Target)) {
    release_assert(NewVals.size() == 1 && Offset == 0);
    *S = NewVals[0].second;
  }
  else {
    
    ImprovedValSetMulti* M = cast<ImprovedValSetMulti>(Target);

    clearRange(M, Offset, Size);
    ImprovedValSetMulti::MapIt it = M->Map.find(Offset);

    for(unsigned i = 0, iend = NewVals.size(); i != iend; ++i) {

      IVSRange& RangeVal = NewVals[i];
      it.insert(RangeVal.first.first, RangeVal.first.second, RangeVal.second);
      ++it;

    }

    M->CoveredBytes += Size;
    if(M->Underlying && M->CoveredBytes == M->AllocSize) {

      // This Multi now defines the whole object: drop the underlying object as it never shows through.
      M->Underlying->dropReference();
      M->Underlying = 0;

    }

  }

}

void llvm::truncateConstVal(ImprovedValSetMulti::MapIt& it, uint64_t off, uint64_t size) {

  ImprovedValSetSingle& S = it.val();

  // Dodge problem of taking e.g. { complex_val, other_complex_val } that
  // split into multiple values and then recombining: only allow value splitting for singleton sets.
  if(S.Values.size() == 1) {

    SmallVector<IVSRange, 4> SubVals;
    Constant* OldC = cast<Constant>(S.Values[0].V.getVal());
    getConstSubVals(OldC, off, size, /* reporting offset = */ it.start(), SubVals);
    if(SubVals.size() == 1)
      S = SubVals[0].second;
    else {

      // Replace single with several:
      it.erase();

      for(SmallVector<IVSRange, 4>::iterator valit = SubVals.begin(), valend = SubVals.end();
	  valit != valend; ++valit) {

	it.insert(valit->first.first, valit->first.second, valit->second);
	++it;

      }

      // Pointer ends up aimed at the last part of the replacement.

    }

    return;

  }

  for(uint32_t i = 0; i < S.Values.size(); ++i) {

    Constant* OldC = cast<Constant>(S.Values[i].V.getVal());
    Constant* NewC = getSubConst(OldC, off, size);
    if(NewC)
      S.Values[i].V = ShadowValue(NewC);
    else {
      S.setOverdef();
      return;
    }

  }

}

void llvm::truncateRight(ImprovedValSetMulti::MapIt& it, uint64_t n) {

  // Remove bytes from the RHS, leaving a value of size n bytes.
  // it points at the current value that should be altered.

  ImprovedValSetSingle& S = it.val();

  if(S.Overdef || S.Values.empty())
    return;
  if(S.SetType == ValSetTypeScalarSplat) {
    release_assert(S.Values.size() == 1 && "Splat set can't be multivalued");
    S.Values[0].Offset = (int64_t)n;
    return;
  }

  truncateConstVal(it, 0, n);

}


void llvm::truncateLeft(ImprovedValSetMulti::MapIt& it, uint64_t n) {

  // Remove bytes from the LHS, leaving a value of size n bytes.
  // it points at the current value that should be altered.

  ImprovedValSetSingle& S = it.val();

  if(S.Overdef || S.Values.empty())
    return;
  if(S.SetType == ValSetTypeScalarSplat) {
    release_assert(S.Values.size() == 1 && "Splat value must be single-valued");
    S.Values[0].Offset = (int64_t)n;
    return;
  }

  Constant* C = cast<Constant>(S.Values[0].V.getVal());
  uint64_t CSize = GlobalAA->getTypeStoreSize(C->getType());
  truncateConstVal(it, CSize - n, n);

}

bool llvm::canTruncate(ImprovedValSetSingle& S) {

  return 
    S.Overdef || 
    S.SetType == ValSetTypeScalar || 
    S.SetType == ValSetTypeScalarSplat;
  
}

void llvm::readValRangeMultiFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, SmallVector<IVSRange, 4>& Results, ImprovedValSet* ignoreBelowStore) {

  if(ignoreBelowStore && ignoreBelowStore == store) {
    LFV3(errs() << "Leaving a gap due to threshold store " << ignoreBelowStore << "\n");
    return;
  }

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(store)) {

    if(Offset == 0 && Size == V.getAllocSize()) {
      
      LFV3(errs() << "Single val satisfies whole read\n");
      Results.push_back(IVSR(0, Size, *IVS));
      
    }
    else {
      
      LFV3(errs() << "Single val subval satisfies whole read\n");
      ImprovedValSetSingle SubVal;
      getIVSSubVals(*IVS, Offset, Size, 0, Results);
      
    }

  }
  else {
    
    ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(store);
    ImprovedValSetMulti::MapIt it = IVM->Map.find(Offset);

    // Value overlapping range on the left:
    if(it != IVM->Map.end() && it.start() < Offset) {

      // Read a sub-value:
      uint64_t SubvalOffset = Offset - it.start();
      uint64_t SubvalSize = std::min(Offset + Size, it.stop()) - Offset;

      LFV3(errs() << "Add val at " << it.start() << "-" << it.stop() << " subval " << SubvalOffset << "-" << (SubvalOffset + SubvalSize) << "\n");
      
      getIVSSubVals(it.val(), SubvalOffset, SubvalSize, it.start(), Results);
      Offset += SubvalSize;
      Size -= SubvalSize;
      ++it;
		     
    }

    // Process vals that don't overlap on the left, but may on the right:
    while(it != IVM->Map.end() && it.start() < (Offset + Size)) {

      if(it.start() != Offset) {

	release_assert(it.start() > Offset && "Overlapping-on-left should be caught already");
	// Gap -- defer this bit to our parent map (which must exist)
	release_assert(IVM->Underlying && "Gap but no underlying map?");
	LFV3(errs() << "Defer to underlying map " << IVM->Underlying << " for range " << Offset << "-" << it.start() << "\n");
	readValRangeMultiFrom(V, Offset, it.start() - Offset, ReadBB, IVM->Underlying, Results, ignoreBelowStore);
	Size -= (it.start() - Offset);
	Offset = it.start();
	
      }

      if(it.stop() > (Offset + Size)) {

	LFV3(errs() << "Add val at " << it.start() << "-" << it.stop() << " subval " << "0-" << Size << "\n");

	// Overlap on the right: extract sub-val.
	getIVSSubVals(it.val(), 0, Size, it.start(), Results);
	Offset += Size;
	Size = 0;
	break;

      }
      else {

	LFV3(errs() << "Add whole val at " << it.start() << "-" << it.stop() << "\n");

	// No overlap: use whole value.
	Results.push_back(IVSR(it.start(), it.stop(), it.val()));
	Offset += (it.stop() - it.start());
	Size -= (it.stop() - it.start());
	++it;

      }

    }

    // Check for gap on the right:
    if(Size != 0) {

      release_assert(IVM->Underlying && "Gap but no underlying map/2?");
      LFV3(errs() << "Defer to underlying map " << IVM->Underlying << " for range " << Offset << "-" << (Offset+Size) << " (end path)\n");      
      readValRangeMultiFrom(V, Offset, Size, ReadBB, IVM->Underlying, Results, ignoreBelowStore);

    }

  }

}

void llvm::readValRangeMulti(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, SmallVector<IVSRange, 4>& Results) {

  // Try to make an IVS representing the block-local value of V+Offset -> Size.
  // Limitations for now: because our output is a single IVS, non-scalar types may only be described
  // if they correspond to a whole object.

  LFV3(errs() << "Start read-multi " << Offset << "-" << (Offset+Size) << "\n");

  // Special case: read from constant global. Read the initialiser.
  if(ShadowGV* G = V.getGV()) {
    
    if(G->G->isConstant()) {

      getConstSubVals(G->G->getInitializer(), Offset, Size, 0, Results);
      return;

    }

  }

  LocStore* firstStore;

  DenseMap<ShadowValue, LocStore>::iterator it = ReadBB->localStore->store.find(V);
  if(it == ReadBB->localStore->store.end()) {
    if(ReadBB->localStore->allOthersClobbered) {
      LFV3(errs() << "Location not in local map and allOthersClobbered\n");
      Results.push_back(IVSR(Offset, Offset+Size, ImprovedValSetSingle::getOverdef()));
      return;
    }
    else {
      LFV3(errs() << "Starting at base store\n");
      firstStore = &(V.getBaseStore());
    }
  }
  else {
    LFV3(errs() << "Starting at local store\n");
    firstStore = &(it->second);
  }

  readValRangeMultiFrom(V, Offset, Size, ReadBB, firstStore->store, Results, 0);

}

void llvm::executeMemcpyInst(ShadowInstruction* MemcpySI) {

  ShadowBB* MemcpyBB = MemcpySI->parent;
  ShadowValue Ptr = MemcpySI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.Overdef || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");

  ConstantInt* LengthCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemcpySI->getCallArgOperand(2)));

  ShadowValue SrcPtr = MemcpySI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  release_assert((SrcPtrSet.Overdef || SrcPtrSet.SetType == ValSetTypePB) && "Memcpy from non-pointer value?");

  executeCopyInst(PtrSet, SrcPtrSet, LengthCI ? LengthCI->getLimitedValue() : ULONG_MAX, MemcpyBB);

}

void llvm::executeVaCopyInst(ShadowInstruction* SI) {
  
  ShadowBB* BB = SI->parent;
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.Overdef || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");
  
  ShadowValue SrcPtr = SI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  release_assert((SrcPtrSet.Overdef || SrcPtrSet.SetType == ValSetTypePB) && "Memcpy from non-pointer value?");
  
  executeCopyInst(PtrSet, SrcPtrSet, 24, BB);

}

void llvm::executeAllocInst(ShadowInstruction* SI, Type* AllocType, uint64_t AllocSize) {

  // Represent the store by a big undef value at the start, or if !AllocType (implying AllocSize
  // == ULONG_MAX, unknown size), start with a big Overdef.
  release_assert((!SI->store.store) && "Allocation already initialised?");

  if(AllocType) {
    Constant* Undef = UndefValue::get(AllocType);
    ImprovedVal IV(ShadowValue(Undef), 0);
    SI->store.store = new ImprovedValSetSingle(ImprovedValSetSingle::get(IV, ValSetTypeScalar));
  }
  else {
    SI->store.store = new ImprovedValSetSingle(ImprovedValSetSingle::getOverdef());
  }

  SI->storeSize = AllocSize;
  
  SI->i.PB = ImprovedValSetSingle::get(ImprovedVal(SI, 0), ValSetTypePB);

}

void llvm::executeAllocaInst(ShadowInstruction* SI) {

  // If the store is already initialised this must represent the general case of an allocation
  // within a loop or recursive call.
  if(SI->store.store)
    return;

  AllocaInst* AI = cast_inst<AllocaInst>(SI);
  Type* allocType = AI->getAllocatedType();
 
  if(AI->isArrayAllocation()) {

    ConstantInt* N = cast_or_null<ConstantInt>(getConstReplacement(AI->getArraySize()));
    if(!N)
      allocType = 0;
    else
      allocType = ArrayType::get(allocType, N->getLimitedValue());

  }

  InlineAttempt* thisIA = SI->parent->IA->getFunctionRoot();
  thisIA->localAllocas.push_back(SI);

  executeAllocInst(SI, allocType, allocType ? GlobalAA->getTypeStoreSize(allocType) : ULONG_MAX);

}

void llvm::executeMallocInst(ShadowInstruction* SI) {

  if(SI->store.store)
    return;

  ConstantInt* AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(0)));
  Type* allocType = 0;
  if(AllocSize)
    allocType = ArrayType::get(Type::getInt8Ty(SI->invar->I->getContext()), AllocSize->getLimitedValue());

  executeAllocInst(SI, allocType, AllocSize ? AllocSize->getLimitedValue() : ULONG_MAX);

}

void llvm::executeReallocInst(ShadowInstruction* SI) {

  if(!SI->store.store) {

    // Only alloc the first time; always carry out the copy implied by realloc.
    ConstantInt* AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(0)));
    Type* allocType = 0;
    if(AllocSize)
      allocType = ArrayType::get(Type::getInt8Ty(SI->invar->I->getContext()), AllocSize->getLimitedValue());
    executeAllocInst(SI, allocType, AllocSize ? AllocSize->getLimitedValue() : ULONG_MAX);    

  }

  ShadowValue SrcPtr = SI->getCallArgOperand(0);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Realloc from uninitialised PB?");
  release_assert((SrcPtrSet.Overdef || SrcPtrSet.SetType == ValSetTypePB) && "Realloc non-pointer-typed value?");
  uint64_t CopySize = ULONG_MAX;

  if(SrcPtrSet.Overdef || SrcPtrSet.Values.size() > 1) {

    // Overdef the realloc.
    SrcPtrSet.setOverdef();

  }
  else {

    CopySize = SrcPtrSet.Values[0].V.getAllocSize();

  }

  ImprovedValSetSingle ThisInst = ImprovedValSetSingle::get(ImprovedVal(ShadowValue(SI), 0), ValSetTypePB);

  executeCopyInst(ThisInst, SrcPtrSet, CopySize, SI->parent);

}

void llvm::executeCopyInst(ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& SrcPtrSet, uint64_t Size, ShadowBB* BB) {

  LFV3(errs() << "Start copy inst\n");

  if(Size == ULONG_MAX || PtrSet.Overdef || PtrSet.Values.size() != 1 || SrcPtrSet.Overdef || SrcPtrSet.Values.size() != 1) {

    // Only support memcpy from single pointer to single pointer for the time being:
    ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
    executeWriteInst(PtrSet, OD, Size, BB);
    return;

  }

  if(val_is<ConstantPointerNull>(SrcPtrSet.Values[0].V))
    return;

  if(val_is<ConstantPointerNull>(PtrSet.Values[0].V))
    return;

  SmallVector<IVSRange, 4> copyValues;
  readValRangeMulti(SrcPtrSet.Values[0].V, SrcPtrSet.Values[0].Offset, Size, BB, copyValues);

  int64_t OffDiff = PtrSet.Values[0].Offset - SrcPtrSet.Values[0].Offset;
  for(SmallVector<IVSRange, 4>::iterator it = copyValues.begin(), it2 = copyValues.end();
      it != it2; ++it) {
    
    // The copied values are labelled according to source offsets; relabel for the destination.
    it->first.first += OffDiff;
    it->first.second += OffDiff;
    
  }

  // OK now blow a hole in the local map for that value and write this list of extents into the gap:
  LocStore& Store = BB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, Size, copyValues.size() == 1);
  replaceRangeWithPBs(Store.store, copyValues, (uint64_t)PtrSet.Values[0].Offset, Size);

}

void llvm::executeVaStartInst(ShadowInstruction* SI) {

  LFV3(errs() << "Start va_start inst\n");

  ShadowBB* BB = SI->parent;
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;

  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.Overdef || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");

  if(PtrSet.Overdef || PtrSet.Values.size() > 1) {

    ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
    executeWriteInst(PtrSet, OD, 24, BB);
    return;

  }

  SmallVector<IVSRange, 4> vaStartVals;
  ImprovedValSetSingle nonFPOffset = ImprovedValSetSingle::get(ImprovedVal(ShadowValue(SI), ImprovedVal::first_nonfp_arg), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(0, 4, nonFPOffset));

  ImprovedValSetSingle FPOffset = ImprovedValSetSingle::get(ImprovedVal(ShadowValue(SI), ImprovedVal::first_fp_arg), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(4, 8, FPOffset));

  ImprovedValSetSingle AnyPtr = ImprovedValSetSingle::get(ImprovedVal(ShadowValue(SI), ImprovedVal::first_any_arg), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(8, 16, AnyPtr));
  
  ImprovedValSetSingle StackBase = ImprovedValSetSingle::get(ImprovedVal(ShadowValue(SI), ImprovedVal::va_baseptr), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(16, 24, StackBase));

  LocStore& Store = BB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, 24, false);
  replaceRangeWithPBs(Store.store, vaStartVals, (uint64_t)PtrSet.Values[0].Offset, 24);

}

void llvm::executeReadInst(ShadowInstruction* ReadSI, OpenStatus& OS, uint64_t FileOffset, uint64_t Size) {

  LFV3(errs() << "Start read inst\n");

  ShadowBB* ReadBB = ReadSI->parent;

  ShadowValue Ptr = ReadSI->getCallArgOperand(1);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB (read)?");
  release_assert((PtrSet.Overdef || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value (read)?");

  ImprovedValSetSingle WriteIVS;
  
  if(PtrSet.Overdef || PtrSet.Values.size() != 1) {

    WriteIVS = ImprovedValSetSingle::getOverdef();

  }
  else {

    std::vector<Constant*> constBytes;
    std::string errors;
    LLVMContext& Context = Ptr.getLLVMContext();
    if(getFileBytes(OS.Name, FileOffset, Size, constBytes, Context,  errors)) {
      ArrayType* ArrType = ArrayType::get(IntegerType::get(Context, 8), constBytes.size());
      Constant* ByteArray = ConstantArray::get(ArrType, constBytes);
      WriteIVS = ImprovedValSetSingle::get(ImprovedVal(ByteArray, 0), ValSetTypeScalar);
    }

  }

  executeWriteInst(PtrSet, WriteIVS, Size, ReadBB);

}

enum specialfunctions {

  SF_MALLOC,
  SF_REALLOC,
  SF_VASTART,
  SF_VACOPY

};

static DenseMap<Function*, specialfunctions> SpecialFunctionMap;

void llvm::initSpecialFunctionsMap(Module& M) {

  if(Function* F1 = M.getFunction("malloc"))
    SpecialFunctionMap[F1] = SF_MALLOC;  
  if(Function* F2 = M.getFunction("realloc"))
    SpecialFunctionMap[F2] = SF_REALLOC;
  if(Function* F4 = M.getFunction("llvm.va_start"))
    SpecialFunctionMap[F4] = SF_VASTART;
  if(Function* F5 = M.getFunction("llvm.va_copy"))
    SpecialFunctionMap[F5] = SF_VACOPY;

}

void llvm::executeUnexpandedCall(ShadowInstruction* SI) {

  if(MemIntrinsic* MI = dyn_cast_inst<MemIntrinsic>(SI)) {

    if(isa<MemTransferInst>(MI))
      executeMemcpyInst(SI);
    else
      executeMemsetInst(SI);
    return;

  }

  Function* F = getCalledFunction(SI);

  if(F) {

    // Try to execute a special instruction:

    DenseMap<Function*, specialfunctions>::iterator it = SpecialFunctionMap.find(F);
    if(it != SpecialFunctionMap.end()) {
      
      switch(it->second) {
	
      case SF_MALLOC:
	executeMallocInst(SI);
	break;
      case SF_REALLOC:
	executeReallocInst(SI);
	break;
      case SF_VASTART:
	executeVaStartInst(SI);
	break;
      case SF_VACOPY:
	executeVaCopyInst(SI);
	break;

      }

      return;

    }

    // All unannotated calls return an unknown value:
    SI->i.PB.setOverdef();

    // See if we can discard the call because it's annotated read-only:
    if(F->onlyReadsMemory())
      return;

    // Otherwise do selective clobbering for annotated syscalls:

    if(const LibCallFunctionInfo* FI = GlobalVFSAA->getFunctionInfo(F)) {

      if(!(FI->UniversalBehavior & llvm::AliasAnalysis::Mod))
	return;
      
      const LibCallFunctionInfo::LocationMRInfo *Details = 0;

      if(FI->LocationDetails)
	Details = FI->LocationDetails;
      else if(FI->getLocationDetailsFor)
	Details = FI->getLocationDetailsFor(ShadowValue(SI));

      release_assert(FI->DetailsType == LibCallFunctionInfo::DoesOnly);

      for (unsigned i = 0; Details[i].Location; ++i) {

	if(!(Details[i].MRInfo & AliasAnalysis::Mod))
	  continue;

	ShadowValue ClobberV;
	uint64_t ClobberSize = 0;
	if(Details[i].Location->getLocation) {
	  Details[i].Location->getLocation(ShadowValue(SI), ClobberV, ClobberSize);
	}
	else {
	  ClobberV = SI->getCallArgOperand(Details[i].Location->argIndex);
	  ClobberSize = Details[i].Location->argSize;
	}

	if(ClobberV.isInval())
	  continue;

	ImprovedValSetSingle ClobberSet;
	getImprovedValSetSingle(ClobberV, ClobberSet);
	ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
	executeWriteInst(ClobberSet, OD, ClobberSize, SI->parent);

      }

      return;

    }

  }

  // Finally clobber all locations; this call is entirely unhandled
  errs() << "Warning: unhandled call to " << itcache(SI) << " clobbers all locations\n";
  ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
  executeWriteInst(OD, OD, AliasAnalysis::UnknownSize, SI->parent);

}

void llvm::executeWriteInst(ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, uint64_t PtrSize, ShadowBB* StoreBB) {

  if(!ValPB.isInitialised())
    ValPB.setOverdef();

  if(PtrSet.Overdef) {

    // Start with a plain local store map giving no locations.
    // getEmptyMap clears the map if it's writable or makes a new blank one otherwise.
    StoreBB->localStore = StoreBB->localStore->getEmptyMap();
    StoreBB->localStore->allOthersClobbered = true;
    LFV3(errs() << "Write through overdef; local map " << StoreBB->localStore << " clobbered\n");

  }
  else if(PtrSet.Values.size() == 1 && PtrSet.Values[0].Offset != LLONG_MAX) {

    LFV3(errs() << "Write through certain pointer\n");
    // Best case: store through a single, certain pointer. Overwrite the location with our new PB.

    if(val_is<ConstantPointerNull>(PtrSet.Values[0].V))
      return;

    LocStore& Store = StoreBB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, PtrSize, true);
    replaceRangeWithPB(Store.store, ValPB, (uint64_t)PtrSet.Values[0].Offset, PtrSize);

  }
  else {

    for(SmallVector<ImprovedVal, 1>::iterator it = PtrSet.Values.begin(), it2 = PtrSet.Values.end(); it != it2; ++it) {

      if(val_is<ConstantPointerNull>(it->V))
	continue;

      if(it->Offset == LLONG_MAX) {
	LFV3(errs() << "Write through vague pointer; clobber\n");
	LocStore& Store = StoreBB->getWritableStoreFor(it->V, 0, ULONG_MAX, true);
	ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
	replaceRangeWithPB(Store.store, OD, 0, ULONG_MAX);
      }
      else {

	ImprovedValSetSingle oldValSet;
	if(ValPB.Overdef) {

	  // Overdef merges with everything to make overdef, so don't bother with the lookup.
	  oldValSet = ValPB;

	}
	else {

	  std::string ignoreErrorHere;
	  LFV3(errs() << "Write through maybe pointer; merge\n");
	  readValRange(it->V, (uint64_t)it->Offset, PtrSize, StoreBB, oldValSet, ignoreErrorHere);

	  if((!oldValSet.Overdef) && oldValSet.isInitialised()) {

	    std::string ignoredError;
	    if(!ValPB.coerceToType(oldValSet.Values[0].V.getType(), PtrSize, ignoredError)) {
	      LFV3(errs() << "Read-modify-write failure coercing to type " << (*oldValSet.Values[0].V.getType()) << "\n");
	    }

	  }

	  oldValSet.merge(ValPB);

	}

	LocStore& Store = StoreBB->getWritableStoreFor(it->V, it->Offset, PtrSize, true);
	replaceRangeWithPB(Store.store, oldValSet, (uint64_t)it->Offset, PtrSize); 

      }

    }

  }

}

void LocalStoreMap::clear() {

  release_assert(refCount <= 1 && "clear() against shared map?");

  // Drop references to any maps this points to;
  for(DenseMap<ShadowValue, LocStore>::iterator it = store.begin(), itend = store.end(); it != itend; ++it) {
    LFV3(errs() << "Drop ref to " << it->second.store << "\n");
    it->second.store->dropReference();
  }

  store.clear();

}

LocalStoreMap* LocalStoreMap::getEmptyMap() {

  if(store.empty())
    return this;
  else if(refCount == 1) {
    clear();
    return this;
  }
  else {
    dropReference();
    return new LocalStoreMap();
  }

}

void LocalStoreMap::dropReference() {

  if(!--refCount) {

    LFV3(errs() << "Local map " << this << " freed\n");
    clear();

    delete this;

  }
  else {

    LFV3(errs() << "Local map " << this << " refcount down to " << refCount << "\n");

  }

}

static bool getCommonAncestor(ImprovedValSet* LHS, ImprovedValSet* RHS, ImprovedValSet*& LHSResult, ImprovedValSet*& RHSResult, SmallPtrSet<ImprovedValSetMulti*, 4>& Seen) {

  LFV3(errs() << "gca " << LHS << " " << RHS << " " << isa<ImprovedValSetSingle>(LHS) << " " << isa<ImprovedValSetSingle>(RHS) << "\n");

  if(ImprovedValSetSingle* LHSS = dyn_cast<ImprovedValSetSingle>(LHS)) {

    if(ImprovedValSetSingle* RHSS = dyn_cast<ImprovedValSetSingle>(RHS)) {
      
      bool match = (*LHSS) == (*RHSS);
      if(match) {
	
	LHSResult = LHS;
	RHSResult = RHS;

      }
      return match;

    }
    else {

      // Flip args:
      return getCommonAncestor(RHS, LHS, RHSResult, LHSResult, Seen);

    }

  }

  ImprovedValSetMulti* LHSM = cast<ImprovedValSetMulti>(LHS);
  if(LHS == RHS || Seen.count(LHSM)) {
    LHSResult = LHS;
    RHSResult = LHS;
    return true;
  }

  // Neither side can advance?
  if((!LHSM->Underlying)) {

    if(isa<ImprovedValSetSingle>(RHS) || (!cast<ImprovedValSetMulti>(RHS)->Underlying))
      return false;

  }
  else {
    
    Seen.insert(LHSM);
    
  }

  // Advance the LHS pointer if possible, flip args to advance other side next.
  return getCommonAncestor(RHS, LHSM->Underlying ? LHSM->Underlying : LHS, RHSResult, LHSResult, Seen);

}

void MergeBlockVisitor::mergeStores(ShadowBB* BB, LocStore* mergeFromStore, LocStore* mergeToStore, ShadowValue& MergeV) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(mergeToStore->store)) {

    LFV3(errs() << "Merge in store " << mergeFromStore << " -> " << mergeToStore << "\n");

    if(IVS->Overdef) {
      LFV3(errs() << "Target already clobbered\n");
      return;
    }

    if(ImprovedValSetSingle* IVS2 = dyn_cast<ImprovedValSetSingle>(mergeFromStore->store)) {
      LFV3(errs() << "Merge in another single\n");
      IVS->merge(*IVS2);
      return;
    }

  }

  // Get an IVS list for each side that contains gaps where there is a common ancestor:
  ImprovedValSet *LHSAncestor, *RHSAncestor;
  {
    SmallPtrSet<ImprovedValSetMulti*, 4> Seen;
    // If we're making a new base store, flatten entirely.
    if(mergeToBase)
      LFV3(errs() << "Not using ancestor because target is base object\n");
    if(mergeToBase || !getCommonAncestor(mergeToStore->store, mergeFromStore->store, LHSAncestor, RHSAncestor, Seen)) {

      LHSAncestor = 0;
      RHSAncestor = 0;
	      
    }
    LFV3(errs() << "Merging multi stores; use common ancestor " << LHSAncestor << "/" << RHSAncestor << "\n");
  }

  {
    SmallVector<IVSRange, 4> LHSVals;
    SmallVector<IVSRange, 4> RHSVals;
    uint64_t TotalBytes = MergeV.getAllocSize();

    readValRangeMultiFrom(MergeV, 0, TotalBytes, BB, mergeToStore->store, LHSVals, LHSAncestor);
    readValRangeMultiFrom(MergeV, 0, TotalBytes, BB, mergeFromStore->store, RHSVals, RHSAncestor);
	  
    SmallVector<IVSRange, 4> MergedVals;
    // Algorithm:
    // Where both ancestors cover some range, merge.
    // Where neither ancestor covers, leave blank for deferral.
    // Where only one covers, get that subrange from the common ancestor store.
    // Where granularity of coverage differs, break apart into subvals.

    SmallVector<IVSRange, 4>::iterator LHSit = LHSVals.begin(), RHSit = RHSVals.begin();
    SmallVector<IVSRange, 4>::iterator LHSitend = LHSVals.end(), RHSitend = RHSVals.end();
    uint64_t LastOffset = 0;
    bool anyGaps = false;

    while(LHSit != LHSitend || RHSit != RHSitend) {

      // Pick earlier-starting, earlier-ending operand to consume from next:
      SmallVector<IVSRange, 4>::iterator* consumeNext;
      if(LHSit == LHSitend)
	consumeNext = &RHSit;
      else if(RHSit == RHSitend)
	consumeNext = &LHSit;
      else {

	// Regard starting before now as equal to starting right now.
	uint64_t consumeLHS = std::max(LHSit->first.first, LastOffset);
	uint64_t consumeRHS = std::max(RHSit->first.first, LastOffset);

	if(consumeLHS == consumeRHS)
	  consumeNext = LHSit->first.second <= RHSit->first.second ? &LHSit : &RHSit;
	else
	  consumeNext = consumeLHS < consumeRHS ? &LHSit : &RHSit;

      }
      SmallVector<IVSRange, 4>::iterator& consumeit = *consumeNext;
      SmallVector<IVSRange, 4>::iterator& otherit = (consumeNext == &LHSit ? RHSit : LHSit);
      SmallVector<IVSRange, 4>::iterator& otherend = (consumeNext == &LHSit ? RHSitend : LHSitend);

      LFV3(errs() << "Consume from " << ((consumeNext == &LHSit) ? "LHS" : "RHS") << " val at " << consumeit->first.first << "-" << consumeit->first.second << "\n");

      // consumeit is now the input iterator that
      // (a) is not at the end
      // (b) is defined at LastOffset, in which case otherit is not defined here,
      // (c) or it is defined and otherit is also defined here and otherit remains defined for longer,
      // (d) or else both iterators are not defined here and consumeit becomes defined first.
      // In short we should leave a gap until consumeit becomes defined, or merge the next
      // consumeit object with either the base (if otherit is not defined) or with a partial
      // otherit object.

      // Find next event:
      if(LastOffset < consumeit->first.first) {
		
	LFV3(errs() << "Gap " << LastOffset << "-" << LHSit->first.first << "\n");
	// Case (d) Leave a gap
	anyGaps = true;
	LastOffset = consumeit->first.first;

      }
      else if(otherit == otherend || otherit->first.first > LastOffset) {

	// consumeit entry begins here or earlier but otherit is not defined, case (b). 
	// Merge it with base up to this entry's end or otherit becoming defined.
	uint64_t stopAt;
	bool bump;
	if(otherit == otherend || otherit->first.first >= consumeit->first.second) {
	  stopAt = consumeit->first.second;
	  bump = true;
	}
	else {
	  stopAt = otherit->first.first;
	  bump = false;
	}

	LFV3(errs() << "Merge with base " << LastOffset << "-" << stopAt << "\n");
	  
	SmallVector<IVSRange, 4> baseVals;
	readValRangeMultiFrom(MergeV, LastOffset, stopAt - LastOffset, BB, LHSAncestor, baseVals, 0);
		
	for(SmallVector<IVSRange, 4>::iterator baseit = baseVals.begin(), baseend = baseVals.end();
	    baseit != baseend; ++baseit) {

	  ImprovedValSetSingle subVal;
	  getIVSSubVal(consumeit->second, baseit->first.first - consumeit->first.first, baseit->first.second - baseit->first.first, subVal);
	  subVal.merge(baseit->second);
	  MergedVals.push_back(IVSR(baseit->first.first, baseit->first.second, subVal));
		    
	}

	LastOffset = stopAt;
	if(bump)
	  ++consumeit;
		
      }
      else {

	LFV3(errs() << "Merge two vals " << LastOffset << "-" << consumeit->first.second << "\n");

	// Both entries are defined here, case (c), so consumeit finishes equal or sooner.
	ImprovedValSetSingle consumeVal;
	getIVSSubVal(consumeit->second, LastOffset - consumeit->first.first, consumeit->first.second - LastOffset, consumeVal);
		
	ImprovedValSetSingle otherVal;
	getIVSSubVal(otherit->second, LastOffset - otherit->first.first, consumeit->first.second - LastOffset, otherVal);

	LFV3(errs() << "Value 1:\n");
	LFV3(printPB(errs(), consumeVal));
	LFV3(errs() << "\nValue 2:\n");
	LFV3(printPB(errs(), otherVal));
	LFV3(errs() << "\n");

	if(useVarargMerge && consumeVal.SetType == ValSetTypeVarArg && otherVal.SetType == ValSetTypeVarArg && consumeVal.Values.size() == 1 && otherVal.Values.size() == 1) {

	  if(otherVal.Values[0].Offset > consumeVal.Values[0].Offset)
	    consumeVal = otherVal;

	}
	else {
		
	  consumeVal.merge(otherVal);

	}

	MergedVals.push_back(IVSR(LastOffset, consumeit->first.second, consumeVal));

	LastOffset = consumeit->first.second;

	if(consumeit->first.second == otherit->first.second)
	  ++otherit;
	++consumeit;

      }
	      
    }
      
    // MergedVals is now an in-order extent list of values for the merged store
    // except for gaps where LHSAncestor (or RHSAncestor) would show through.
    // Figure out if we in fact have any gaps:

    ImprovedValSet* newUnderlying;

    if(anyGaps || (LHSVals.back().first.second != TotalBytes && RHSVals.back().first.second != TotalBytes)) {
      LFV3(errs() << "Using ancestor " << LHSAncestor << "\n");
      newUnderlying = LHSAncestor->getReadableCopy();
    }
    else {
      LFV3(errs() << "No ancestor used (totally defined locally)\n");
      newUnderlying = 0;
    }

    // Get a Multi to populate: either clear an existing one or allocate one.

    ImprovedValSetMulti* newStore;

    if(mergeToStore->store->isWritableMulti()) {
      ImprovedValSetMulti* M = cast<ImprovedValSetMulti>(mergeToStore->store);
      LFV3(errs() << "Using existing writable multi " << M << "\n");
      M->Map.clear();
      if(M->Underlying)
	M->Underlying->dropReference();
      newStore = M;
    }
    else {
      mergeToStore->store->dropReference();
      newStore = new ImprovedValSetMulti(MergeV);
      LFV3(errs() << "Drop existing store " << mergeToStore->store << ", allocate new multi " << newStore << "\n");
    }	

    newStore->Underlying = newUnderlying;

    ImprovedValSetMulti::MapIt insertit = newStore->Map.end();
    for(SmallVector<IVSRange, 4>::iterator finalit = MergedVals.begin(), finalitend = MergedVals.end();
	finalit != finalitend; ++finalit) {

      insertit.insert(finalit->first.first, finalit->first.second, finalit->second);
      insertit = newStore->Map.end();
	
    }

    LFV3(errs() << "Merge result:\n");
    LFV3(newStore->print(errs()));

    mergeToStore->store = newStore;

  }

}

void MergeBlockVisitor::visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx) {

  LFV3(errs() << "Merge: visit BB " << BB->invar->BB->getName() << "\n");

  if(!seenMaps.insert(BB->localStore)) {
    // We've already seen this exact map as a pred; drop the extra ref.
    LFV3(errs() << "Seen map " << BB->localStore << " before; drop ref\n");
    BB->localStore->dropReference();
    return;
  }

  if(!newMapValid) {
    // This is the first predecessor, borrow the incoming block's map / use the base map.
    // Note that the refcount is already correct (blocks assume their map will be taken per default)
    // Also note if the incoming block shadowed nothing this might still leave newMap == 0.
    newMap = BB->localStore;
    LFV3(errs() << "Take incoming map " << BB->localStore << "\n");
    newMapValid = true;
    return;
  }
  else {

    // Merge in the new map or base store values as appropriate.
    // Create a local map if we didn't have one; COW break it if it was shared.
    // The first time a real merge is necessary this might COW-break.
    // After that it's a no-op.
    LocalStoreMap* mergeMap = newMap->getWritableStoreMap();
    LocalStoreMap* mergeFromMap = BB->localStore;

    release_assert(mergeMap && "Must have a concrete destination map");
    release_assert(mergeFromMap && "Incoming block must have a map");

    if(mergeFromMap->allOthersClobbered) {

      SmallVector<ShadowValue, 4> keysToRemove;

      // Remove any existing mappings in mergeMap that do not occur in mergeFromMap:
      for(DenseMap<ShadowValue, LocStore>::iterator it = mergeMap->store.begin(), 
	    itend = mergeMap->store.end(); it != itend; ++it) {

	if(!mergeFromMap->store.count(it->first)) {

	  LFV3(errs() << "Merge from " << mergeFromMap << " with allOthersClobbered; drop local obj\n");
	  keysToRemove.push_back(it->first);
	  it->second.store->dropReference();

	}

      }

      for(SmallVector<ShadowValue, 4>::iterator delit = keysToRemove.begin(), 
	    delitend = keysToRemove.end(); delit != delitend; ++delit) {

	mergeMap->store.erase(*delit);

      }

      mergeMap->allOthersClobbered = true;

    }
    else if(!mergeMap->allOthersClobbered) {

      LFV3(errs() << "Both maps don't have allOthersClobbered; reading through allowed\n");

      // For any locations mentioned in mergeFromMap but not mergeMap,
      // move them over. We'll still need to merge in the base object below, this
      // just creates the asymmetry that x in mergeFromMap -> x in mergeMap.
	  
      SmallVector<ShadowValue, 4> toDelete;

      for(DenseMap<ShadowValue, LocStore>::iterator it = mergeFromMap->store.begin(),
	    itend = mergeFromMap->store.end(); it != itend; ++it) {
	
	std::pair<DenseMap<ShadowValue, LocStore>::iterator, bool> ins = 
	  mergeMap->store.insert(std::make_pair(it->first, it->second));
	
	if(ins.second)
	  toDelete.push_back(ins.first->first);

      }
      
      for(SmallVector<ShadowValue, 4>::iterator delit = toDelete.begin(), delend = toDelete.end();
	  delit != delend; ++delit)
	mergeFromMap->store.erase(*delit);

    }
    else {
	  
      LFV3(errs() << "Merge map " << mergeMap << " has allOthersClobbered; only common objects will merge\n");
	  
    }

    // mergeMap now contains all information from one or other incoming branch;
    // for each location it mentions merge in the other map's version or the base object.
    // Note that in the mergeMap->allOthersClobbered case this only merges in
    // information from locations explicitly mentioned in mergeMap.

    for(DenseMap<ShadowValue, LocStore>::iterator it = mergeMap->store.begin(),
	  itend = mergeMap->store.end(); it != itend; ++it) {

      LocStore* mergeFromStore;
      DenseMap<ShadowValue, LocStore>::iterator found = mergeFromMap->store.find(it->first);
      if(found != mergeFromMap->store.end())
	mergeFromStore = &(found->second);
      else
	mergeFromStore = &it->first.getBaseStore();

      // Right, merge it->second and mergeFromStore.
      // If the pointers match these are two refs to the same Multi.
      // Refcounting will be caught up when we deref mergeFromMap below:
      if(mergeFromStore->store != it->second.store) {

	mergeStores(BB, mergeFromStore, &it->second, it->first);

      }

    }

    mergeFromMap->dropReference();

    newMap = mergeMap;

  }

}

void llvm::commitStoreToBase(LocalStoreMap* Map) {

  for(DenseMap<ShadowValue, LocStore>::iterator it = Map->store.begin(), itend = Map->store.end(); it != itend; ++it) {

    LocStore& baseStore = it->first.getBaseStore();
    baseStore.store->dropReference();
    baseStore.store = it->second.store->getReadableCopy();

  }

}

// Return false if this block turns out to have no live predecessors at the moment.
// This is possible in the unusual case that a per-iteration loop exploration has
// created the block to find invariants but it isn't yet reachable according to the
// fixed point analyser -- e.g. this block only becomes reachable on iteration 2.
bool llvm::doBlockStoreMerge(ShadowBB* BB) {

  // We're entering BB; one or more live predecessor blocks exist and we must produce an appropriate
  // localStore from them.

  LFV3(errs() << "Start block store merge\n");

  bool mergeToBase = BB->status == BBSTATUS_CERTAIN && !BB->inAnyLoop;
  if(mergeToBase) {

    LFV3(errs() << "MERGE to base store for " << BB->IA->F.getName() << " / " << BB->IA->SeqNumber << " / " << BB->invar->BB->getName() << "\n");

  }
  // This BB is a merge of all that has gone before; merge to values' base stores
  // rather than a local map.

  MergeBlockVisitor V(mergeToBase, BB->useSpecialVarargMerge);
  BB->IA->visitNormalPredecessorsBW(BB, &V, /* ctx = */0);

  if(!V.newMap) {
    BB->localStore = 0;
    return false;
  }

  // TODO: do this better
  if(mergeToBase && !V.newMap->allOthersClobbered) {
    commitStoreToBase(V.newMap);
    V.newMap = V.newMap->getEmptyMap();
  }

  BB->localStore = V.newMap;

  return true;

}

void llvm::doCallStoreMerge(ShadowInstruction* SI) {

  LFV3(errs() << "Start call-return store merge\n");

  bool mergeToBase = SI->parent->status == BBSTATUS_CERTAIN && !SI->parent->inAnyLoop;
  if(mergeToBase) {

    LFV3(errs() << "MERGE to base store for " << SI->parent->IA->F.getName() << " / " << SI->parent->IA->SeqNumber << " / " << SI->parent->invar->BB->getName() << "\n");

  }

  InlineAttempt* CallIA = SI->parent->IA->getInlineAttempt(cast_inst<CallInst>(SI));

  MergeBlockVisitor V(mergeToBase);
  CallIA->visitLiveReturnBlocks(V);
  
  // If V.newMap is not set this must be an unreachable block
  // and our caller will bail out rather than use SI->parent->localStore.
  if(mergeToBase && V.newMap && !V.newMap->allOthersClobbered) {
    commitStoreToBase(V.newMap);
    V.newMap = V.newMap->getEmptyMap();
  }

  SI->parent->localStore = V.newMap;
  
}

SVAAResult llvm::aliasSVs(ShadowValue V1, uint64_t V1Size,
			  ShadowValue V2, uint64_t V2Size,
			  bool usePBKnowledge) {
  
  SVAAResult Alias = tryResolveImprovedValSetSingles(V1, V1Size, V2, V2Size, usePBKnowledge);
  if(Alias != SVMayAlias)
    return Alias;

  switch(GlobalAA->aliasHypothetical(V1, V1Size, V1.getTBAATag(), V2, V2Size, V2.getTBAATag(), usePBKnowledge)) {
  case AliasAnalysis::NoAlias: return SVNoAlias;
  case AliasAnalysis::MustAlias: return SVMustAlias;
  case AliasAnalysis::MayAlias: return SVMayAlias;
  case AliasAnalysis::PartialAlias: return SVPartialAlias;
  default: release_assert(0); return SVMayAlias;
  }

}

bool llvm::basesAlias(ShadowValue V1, ShadowValue V2) {

  switch(V1.t) {
  case SHADOWVAL_OTHER:

    if(!V2.isVal())
      return false;
    else
      return V1.getVal() == V2.getVal();

  case SHADOWVAL_ARG:

    if(!V2.isArg())
      return false;
    return V1.getArg() == V2.getArg();

  case SHADOWVAL_GV:

    if(V2.t != SHADOWVAL_GV)
      return false;
    return V1.u.GV == V2.u.GV;

  case SHADOWVAL_INST:

    if(!V2.isInst())
      return false;

    if(V1.getInst()->invar == V2.getInst()->invar) {

      return (V1.getCtx()->ctxContains(V2.getCtx()) || V2.getCtx()->ctxContains(V1.getCtx()));

    }
    else
      return false;

  default:
    release_assert(0 && "basesAlias with bad value type");
    llvm_unreachable();

  }
   
}

bool InlineAttempt::ctxContains(IntegrationAttempt* IA) {

  return this == IA;

}

bool PeelIteration::ctxContains(IntegrationAttempt* IA) {

  if(this == IA)
    return true;
  return parent->ctxContains(IA);

}
