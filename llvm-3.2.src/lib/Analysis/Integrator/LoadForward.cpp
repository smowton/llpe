
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/GlobalVariable.h"
#include "llvm/DataLayout.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/ConstantFolding.h"
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

ImprovedValSetSingle NormalLoadForwardWalker::PVToPB(PartialVal& PV, raw_string_ostream& RSO) {

  // Try to use an entire value:
  if(PV.isTotal()) {

    release_assert(PV.TotalIVType == ValSetTypeScalar || PV.TotalIVType == ValSetTypeVarArg);
    if(PV.TotalIVType == ValSetTypeVarArg)
      return ImprovedValSetSingle::get(PV.TotalIV, PV.TotalIVType);

    Type* sourceType = PV.TotalIV.V.getType();

    if(allowTotalDefnImplicitCast(sourceType, originalType) || allowTotalDefnImplicitPtrToInt(sourceType, originalType, GlobalTD))
      return ImprovedValSetSingle::get(PV.TotalIV, PV.TotalIVType);

  }

  ShadowValue NewSV = PVToSV(PV, RSO);
  if(NewSV.isInval())
    return ImprovedValSetSingle();

  ImprovedValSetSingle NewPB;
  if(!getImprovedValSetSingle(NewSV, NewPB)) {
    RSO << "PVToPB";
    return ImprovedValSetSingle();
  }

  return NewPB;

}

ShadowValue NormalLoadForwardWalker::PVToSV(PartialVal& PV, raw_string_ostream& RSO) {

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
      Constant* extr = extractAggregateMemberAt(SalvageC, Offset, originalType, LoadSize, GlobalTD);
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
  if(!PV.convertToBytes(LoadSize, GlobalTD, error)) {
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

  return ShadowValue(constFromBytes((unsigned char*)PV.partialBuf, originalType, GlobalTD));

}

bool IntegrationAttempt::tryResolveLoadFromConstant(ShadowInstruction* LoadI, ImprovedValSetSingle& Result, std::string& error, bool finalise) {

  // A special case: loading from a symbolic vararg:

  ImprovedValSetSingle PtrPB;
  if(!getImprovedValSetSingle(LoadI->getOperand(0), PtrPB))
    return false;

  if(PtrPB.Type == ValSetTypeVarArg && PtrPB.Values.size() == 1) {
  
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

    if(GlobalVariable* GV = dyn_cast_or_null<GlobalVariable>(PtrBase.getVal())) {

      if(GV->isConstant()) {

	uint64_t LoadSize = (GlobalTD->getTypeSizeInBits(LoadI->getType()) + 7) / 8;
	Type* FromType = GV->getInitializer()->getType();
	uint64_t FromSize = (GlobalTD->getTypeSizeInBits(FromType) + 7) / 8;

	if(PtrOffset < 0 || PtrOffset + LoadSize > FromSize) {
	  error = "Const out of range";
	  Result = ImprovedValSetSingle::getOverdef();
	  return true;
	}

	Constant* ExVal = extractAggregateMemberAt(GV->getInitializer(), PtrOffset, LoadI->getType(), LoadSize, GlobalTD);

	if(ExVal) {
      
	  getImprovedValSetSingle(ShadowValue(ExVal), Result);
	  if(!((!Result.Overdef) && Result.Values.size() > 0)) {
	    error = "No PB for ExVal";
	    Result = ImprovedValSetSingle::getOverdef();
	  }

	  return true;

	}

	int64_t CSize = GlobalTD->getTypeAllocSize(GV->getInitializer()->getType());
	if(CSize < PtrOffset) {
	  
	  LPDEBUG("Can't forward from constant: read from global out of range\n");
	  error = "Const out of range 2";
	  Result = ImprovedValSetSingle::getOverdef();
	  return true;
	    
	}

	unsigned char* buf = (unsigned char*)alloca(LoadSize);
	memset(buf, 0, LoadSize);
	if(ReadDataFromGlobal(GV->getInitializer(), PtrOffset, buf, LoadSize, *GlobalTD)) {

	  getImprovedValSetSingle(ShadowValue(constFromBytes(buf, LoadI->getType(), GlobalTD)), Result);
	  return true;
	    
	}
	else {

	  LPDEBUG("ReadDataFromGlobal failed\n");
	  error = "Const RDFG failed";
	  Result = ImprovedValSetSingle::getOverdef();
	  return true;

	}

      }

    }

  }
      
  // Check for loads which are pointless to pursue further because they're known to be rooted on
  // a constant global but we're uncertain what offset within that global we're looking for:

  if(ShadowInstruction* SI = LoadI->getOperand(0).getInst()) {

    if(SI->i.PB.Values.size() > 0 && SI->i.PB.Type == ValSetTypePB) {

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
	if(finalise)
	  Result = ImprovedValSetSingle::getOverdef();
	else
	  Result = ImprovedValSetSingle();
	return true;

      }

    }

  }

  return false;

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

static bool multiLoadEnabled = true;

static bool shouldMultiload(ImprovedValSetSingle& PB) {

  if(PB.Overdef || PB.Values.size() == 0)
    return false;

  if(PB.Type != ValSetTypePB)
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

  return numNonNulls > 1;

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
	
      RSO << "Load " << LI->parent->IA->itcache(LIPB.Values[i].V, true) << " -> " << ThisError;

    }
    else if(NewPB.Overdef) {
	
      RSO << "Loaded ";
      LI->parent->IA->printPB(RSO, ThisPB, true);
      RSO << " -merge-> " << ThisError;

    }

  }

  return NewPB.isInitialised();

}

// Fish a value out of the block-local or value store for LI.
bool IntegrationAttempt::tryForwardLoadPB(ShadowInstruction* LI, ImprovedValSetSingle& NewPB) {

  ImprovedValSetSingle ConstResult;
  std::string error;
  if(tryResolveLoadFromConstant(LI, ConstResult, error, finalise)) {
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

  }
  else {

    // Load from a vague pointer -> Overdef.
    ret = true;
    raw_string_ostream RSO(report);
    RSO << "Load vague ";
    LI->parent->IA->printPB(RSO, LoadPtrPB, true);

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

  if(PB2.Type != ValSetTypePB)
    return SVMayAlias;

  return tryResolveImprovedValSetSingles(PB1, V1Size, PB2, V2Size, usePBKnowledge);

}

SVAAResult llvm::tryResolveImprovedValSetSingles(ShadowValue V1, uint64_t V1Size, ShadowValue V2, uint64_t V2Size, bool usePBKnowledge) {
      
  ImprovedValSetSingle PB1, PB2;
  if((!getImprovedValSetSingle(V1, PB1)) || (!getImprovedValSetSingle(V2, PB2)))
    return SVMayAlias;
      
  if(PB1.Overdef || PB1.Values.size() == 0 || PB2.Overdef || PB2.Values.size() == 0)
    return SVMayAlias;

  if(PB1.Type != ValSetTypePB || PB2.Type != ValSetTypePB)
    return SVMayAlias;

  return tryResolveImprovedValSetSingles(PB1, V1Size, PB2, V2Size, usePBKnowledge);
       
}


DenseMap<ShadowValue, LocStore>& ShadowBB::getWritableStoreMap() {

  release_assert(localStore && "getWritableStoreMap without a local store?");
  DenseMap<ShadowValue, LocStore>* newMap = localStore->getWritableStoreMap();
  if(newMap != localStore) {
    
    // Store the new one:
    localStore = newMap;

  }

  return newMap->store;

}

LocalStoreMap* LocalStoreMap::getWritableStoreMap() {

  // Refcount == 1 means we can just write in place.
  if(refCount == 1)
    return this;

  // COW break: copy the map and either share or copy its entries.
  LocalStoreMap* newMap = new LocalStoreMap();
  for(DenseMap<ShadowValue, LocStore>::iterator it = store.begin(), it2 = store.end(); it != it2; ++it) {

    if(ImprovedValSetSingle* OldSet = dyn_cast<ImprovedValSetSingle>(it->second.store)) {

      // Individual valsets are not sharable: copy.
      ImprovedValSetSingle* NewSet = new ImprovedValSetSingle(OldSet);
      newMap->store[it->first] = LocStore(NewSet);

    }
    else {

      ImprovedValSetMulti* SharedSet = cast<ImprovedValSetMulti>(it->second.store);
      SharedSet->MapRefCount++;
      newMap->store[it->first] = LocStore(SharedSet);

    }

  }

  newMap->allOthersClobbered = allOthersClobbered;

  // Drop reference on the existing map (can't destroy it):
  refCount--;

  return newMap;

}

void ImprovedValSetSingle::dropReference() {

  // Singles can never be shared
  delete this;

}

void ImprovedValSetMulti::dropReference() {

  if(!(--MapRefCount)) {

    Underlying->dropReference();
    
    delete this;

  }

}

LocStore& ShadowBB::getWritableStoreFor(ShadowValue& V, int64_t Offset, uint64_t Size, bool willWriteSingleObject) {

  // We're about to write to memory location V + Offset -> Offset+Size. 
  // We must return a LocStore for that value that can be updated (i.e. is not shared).

  // Can write direct to the base store if we're sure this write is "for good".
  LocStore* ret;
  if(status == BBSTATUS_CERTAIN && !localStore->allOthersClobbered)
    ret = V.getBaseStore();

  // Otherwise we need to write into the block-local store map. COW break it if necessary:
  bool writeWholeObject = (Offset == 0 && (Size == ULONG_MAX || Size == V.getAllocSize()));
   
  if(!ret) {

    DenseMap<ShadowValue, LocStore>& storeMap = getWritableStoreMap();
    std::pair<DenseMap<ShadowValue, LocStore>::iterator, bool> insResult = storeMap.insert(V);
    ret = &(insResult.first.second);
  
    if(insResult.second) {

      // There wasn't an entry in the local map. Make a Single or Multi store depending on
      // whether we're about to cover the whole store or not:
      if(writeWholeObject)
	ret->store = new ImprovedValSetSingle();
      else {
	// Defer the rest of the multimap to the base object.
	ImprovedValSetMulti* M = new ImprovedValSetMulti(V);
	M->Underlying = V.getBaseStore().store;
	ret->store = M;
      }

      return *ret;

    }

  }
  else {

    // There was already an entry in the local map or base store.

    if(writeWholeObject && willWriteSingleObject) {
      
      // If we're about to overwrite the whole thing with a single, convert a multi to a single.

      if(ImprovedValSetMulti* M = dyn_cast<ImprovedValSetMulti>(ret->store)) {
	
	// Might delete the Multi:
	M->dropReference();
	ret->store = new ImprovedValSetSingle();

      }

      // Or retain an existing single as-is, they're always private and writable.

    }
    else {

      // If we're doing a partial overwrite, make sure a multi is writable and promote
      // a single to a multi with that single as base.
      if(!ret->store->isWritableMulti()) {

	ImprovedValSetMulti* NewIMap = new ImprovedValSetMulti(V);
	NewIMap->Underlying = ret->store;
	// M's refcount remains unchanged, it's just now referenced as a base rather than
	// being directly used here.
	ret->store = NewIMap;
	
      }
      // Else already a local map, nothing to do.

    }

  }

  return ret;
  
}

void ImprovedValSetSingle::replaceRangeWithPB(ImprovedValSetSingle& NewVal, int64_t Offset, uint64_t Size) {

  *this = NewVal;

}

void ImprovedValSetSingle::truncateRight(uint64_t n) {

  // Remove bytes from the RHS, leaving a value of size n bytes.

  if(Overdef)
    return;
  if(Type == ValSetTypeScalarSplat) {
    Offset = (int64_t)n;
    return;
  }

  for(uint32_t i = 0; i < Values.size(); ++i) {

    ConstantInt* CI = cast<ConstantInt>(Values[i].V.getVal());
    Type* TruncType = Type::getIntNTy(CI->getContext(), n * 8);
    Constant* NewC = ConstantExpr::getTrunc(CI, TruncType);
    release_assert(!isa<ConstantExpr>(NewC));
    Values[i].V = ShadowVal(NewC);

  }

}

void ImprovedValSetSingle::truncateLeft(uint64_t n, LLVMContext& C) {

  // Remove bytes from the LHS, leaving a value of size n bytes.

  if(Overdef)
    return;
  if(Type == ValSetTypeScalar) {
    Offset = (int64_t)n;
    return;
  }

  for(uint32_t i = 0; i < Values.size(); ++i) {

    ConstantInt* CI = cast<ConstantInt>(Values[i].V.getVal());
    uint64_t shiftn = CI->getBitWidth() - (n * 8);
    Constant* ShiftAmount = ConstantInt::get(Type::getInt64Ty(CI->getContext()), shiftn);
    Constant* NewC = ConstantExpr::getShl(CI, ShiftAmount);
    if(ConstantExpr* CE = dyn_cast<ConstantExpr>(NewC))
      NewC = ConstantFoldConstantExpression(CE, GlobalTD, GlobalTLI);
    release_assert(!isa<ConstantExpr>(NewC));
    Values[i].V = ShadowVal(NewC);

  }

}

void ImprovedValSetSingle::canTruncate() {

  return 
    Overdef || 
    (Type == ValSetTypeScalar && Values[0].V.getType()->isIntegerTy()) || 
    Type == ValSetTypeScalarSplat;

}

void ImprovedValSetMulti::clearRange(uint64_t Offset, uint64_t Size) {

  MapIt found = Map.find(Offset);
  if(found == Map.end())
    return;

  uint64_t LastByte = Offset + Size;

  if(found.start() < Offset) {

    ImprovedValSetSingle RHS;

    if(found.stop() > LastByte) {

      // Punching a hole in a value that wholly covers the range we're clearing:
      ImprovedValSetSingle RHS;
      if(found->canTruncate()) {

	RHS = *found;
	RHS.truncateLeft(found.stop() - LastByte);

      }
      else {

	RHS = ImprovedValSetSingle::getOverdef();

      }

    }

    if(found->canTruncate()) {
      CoveredBytes -= (found.stop() - Offset);
      found->truncateRight(Offset - found.start());
    }
    else {
      found->setOverdef();
    }
    uint64_t oldStop = found.stop();
    found.setStopUnchecked(Offset);

    if(RHS.isInitialised()) {

      Map.insert(LastByte, oldStop, RHS);
      CoveredBytes += (oldStop - LastByte);
      return;

    }

    ++found;

  }
  
  while(found != Map.end() && found.start() <= LastByte && found.stop() <= LastByte) {

    // Implicitly bumps the iterator forwards:
    CoveredBytes -= (found.stop() - found.start());
    found.erase();

  }

  if(found != Map.end() && found.start() <= LastByte) {

    if(found->canTruncate()) {
      found->truncateLeft(found.stop() - LastByte);
    }
    else {
      found->setOverdef();
    }
    CoveredBytes -= (LastByte - found.start());
    found.setStartUnchecked(LastByte);

  }

}

void ImprovedValSetMulti::replaceRangeWithPB(ImprovedValSetSingle& NewVal, uint64_t Offset, uint64_t Size) {

  if(Size == ULONG_MAX) {

    release_assert(NewVal.Overdef && "Indefinite write with non-clobber value?");

  }

  clearRange(Offset, Size);
  Map.insert(Offset, Offset + Size, NewVal);

  CoveredBytes += Size;
  if(Underlying && CoveredBytes == AllocSize) {

    // This Multi now defines the whole object: drop the underlying object as it never shows through.
    Underlying->dropReference();
    Underlying = 0;

  }

}

void ImprovedValSetSingle::replaceRangeWithPBs(SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size) {

  release_assert(NewVals.size() == 1 && Offset == 0);
  *this = NewVals[0].second;

}

void ImprovedValSetMulti::replaceRangeWithPBs(SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size) {

  clearRange(Offset, Size);
  MapIt it = Map->find(Offset);

  for(unsigned i = NewVals.size(); i != 0; --i, --it) {

    IVSRange& RangeVal = NewVals[i-1];
    it.insert(RangeVal.second, RangeVal.first.first, RangeVal.first.second);

  }

  CoveredBytes += Size;
  if(Underlying && CoveredBytes == AllocSize) {

    // This Multi now defines the whole object: drop the underlying object as it never shows through.
    Underlying->dropReference();
    Underlying = 0;

  }  

}

bool llvm::addIVStoPartialVal(ImprovedValSetSingle& IVS, uint64_t Offset, uint64_t Size, PartialVal* PV, std::string& error) {

  release_assert(PV && "Must allocate PV before calling addIVSToPartialVal");

  // For now we forbid building from bytes when an input is set-typed:
  if(IVS.Overdef || IVS.Values.size() != 1)
    return false;
  // And also if the value that would be merged is not constant-typed:
  if(IVS.Type != ValSetTypeScalar && IVS.Type != ValSetTypeScalarSplat)
    return false;

  PartialVal NewPV;
  Constant* DefC = cast<Constant>(IVS.Values[0].V.getVal());
  if(IVS.Type == ValSetTypeScalar) {
    NewPV = PartialVal::getConstant(DefC, Offset);
  }
  else {
    // Splat of i8:
    uint8_t SplatVal = (uint8_t)(DefC->getLimitedValue());
    NewPV = PartialVal::getByteArray(Size);
    
    uint8_t* buffer = (uint8_t*)NewPV.partialBuf;
    bool* validBuf = (bool*)NewPV.partialValidBuf;
    
    for(uint64_t i = 0; i < Size; ++i) {
      buffer[i] = SplatVal;
      validBuf[i] = true;
    }

    NewPV.loadFinished = true;
  }

  if(!ResultPV->combineWith(NewPV, 0, Size, Size, GlobalTD, error))
    return false;

  return true;

}

void llvm::readValRangeFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, ImprovedValSetSingle& Result, PartialVal*& ResultPV, std::string& error) {

  ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(store);
  uint64_t IVSSize = V.getAllocSize();
  ImprovedValSetMulti* IVM;
  ImprovedValSetMulti::MapIt it;

  if(!IVS) {

    // Check for a multi-member that wholly defines the target value:

    IVM = cast<ImprovedValSetMulti>(store);
    it = IVM->Map.find(Offset);

    if(it != IVM->Map.end() && it.start() <= Offset && it.stop() >= (Offset + Size)) {

      IVS = &*it;
      IVSSize = it.stop() - it.start();
      Offset -= it.start();

    }

  }

  if(IVS) {

    if(!ResultPV) {

      // Try to extract the entire value
      if(IVSSize == Size && Offset == 0) {
	Result = *IVS;
	return;
      }
      
      // Otherwise we need to extract a sub-value: only works on constants:
      bool rejectHere = IVS->Type != ValSetTypeScalar && IVS->Type != ValSetTypeScalarSplat;
      if(rejectHere) {
	Result = ImprovedValSetSingle::getOverdef();
	return;
      }
      
      if(IVS->Type == ValSetTypeScalar) {
      
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
					  
	}

	return;

      }

      // Else fall through to bytewise case:
      ResultPV = new PartialVal(Size);

    }

    if(!addIVSToPartialVal(IVS, Offset, Size, ResultPV, error)) {
      
      delete ResultPV;
      Result = ImprovedValSetSingle::getOverdef();

    }
    else {

      release_assert(ResultPV->isComplete() && "Fetch defined by a Single value but not complete?");

    }

    return;

  }

  // If we get to here the value is not wholly covered by this Multi map. Add what we can and defer:
  release_assert(IVM && "Fell through without a multi?");

  for(; it != IVM->end() && it.start() < (Offset + Size); ++it) {

    if(!ResultPV)
      ResultPV = new PartialVal(Size);

    uint64_t FirstReadByte = std::max(Offset, it.start());
    uint64_t LastReadByte = std::min(Offset + Size, it.stop());

    if(!addIVSToPartialVal(*it, FirstReadByte - it.start(), LastReadByte - FirstReadByte, ResultPV, error)) {
      delete ResultPV;
      Result = ImprovedValSetSingle::getOverdef();
      return;
    }

  }
  
  if((!ResultPV) || !ResultPV->isComplete()) {
      
    // Try the next linked map (one should exist:)
    release_assert(IVM->Underlying && "Value not complete, but no underlying map?");
    readValueRangeFrom(V, Offset, Size, ReadBB, IVM->Underlying, Result, ResultPV, error);
      
  }

}

void llvm::readValRange(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSetSingle& Result, std::string& error) {

  // Try to make an IVS representing the block-local value of V+Offset -> Size.
  // Limitations for now: because our output is a single IVS, non-scalar types may only be described
  // if they correspond to a whole object.

  LocStore* firstStore;

  DenseMap<ShadowValue, LocStore>::iterator it = ReadBB->localStore->store.find(V);
  if(it == ReadBB->localStore->store.end()) {
    if(ReadBB->localStore->allOthersClobbered) {
      Result.setOverdef();
      return;
    }
    firstStore = &(V.getBaseStore());
  }
  else
    firstStore = &(it->second);

  PartialVal* ResultPV = 0;
  readValRangeFrom(V, Offset, Size, ReadBB, firstStore, Result, ResultPV);

  if(ResultPV) {

    raw_string_ostream RSO(error);
    Result = PVToPB(*ResultPV, RSO);
    delete ResultPV;

  }

}

bool ImprovedValSetSingle::coerceToType(Type* Target, uint64_t TargetSize, std::string& error) {

  Type* Source = Values[i].V.getType();
  
  // All casts ignored for VAs:
  if(Type == ValSetTypeVarArg)
    return true;

  // Allow implicit ptrtoint and bitcast between pointer types
  // without modifying anything:
  if(allowTotalDefnImplicitCast(Source, Target))
    return true;
  if(allowTotalDefnImplicitPtrToInt(Source, Target, GlobalTD))
    return true;

  if(Type != ValSetTypeScalar) {
    error = "Non-scalar coercion";
    return false;
  }

  // Finally reinterpret cast each member:
  for(uint32_t i = 0, iend = Values.size(); i != iend; ++i) {

    PartialVal PV = PartialVal::getTotal(cast<Constant>(Values[i].V.getVal()));
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
  release_assert(PtrSet.Type == ValSetTypePB && "Write through non-pointer-typed value?");

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
  release_assert(PtrSet.Type == ValSetTypePB && "Write through non-pointer-typed value?");
  
  ConstantInt* LengthCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemsetSI->getCallArgOperand(2)));
  ConstantInt* ValCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemsetSI->getCallArgOperand(1)));

  ImprovedValSetSingle ValSet;

  if(LengthCI && ValCI) {
   
    ValSet.Type = ValSetTypeScalarSplat;
    ImprovedVal IV(ShadowValue(ValCI), LengthCI->getLimitedValue());
    ValSet.insert(IV);

  }
  else {

    ValSet.setOverdef();

  }

  executeWriteInst(PtrSet, ValSet, LengthCI ? LengthCI->getLimitedValue() : ULONG_MAX, MemsetBB);
  
}

void llvm::getIVSSubVal(ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, ImprovedValSetSingle& Dest) {

  // Subvals only allowed for scalars:

  if(Src.Overdef) {
    Dest = Src;
    return;
  }

  switch(Src.Type) {
  case ValSetTypeScalar:
    break;
  case ValSetTypeScalarSplat:
    Dest = Src;
    return;
  default:
    Dest.setOverdef();
    return;
  }

  for(uint32_t i = 0, endi = Src->Values.size(); i != endi && !Result.Overdef; ++i) {
	
    Constant* bigConst = cast<Constant>(Src->Values[i].V.getVal());

    Constant* smallConst = extractAggregateMemberAt(bigConst, Offset, 0, Size, GlobalTD);

    if(!smallConst) {

      // Must do a reinterpret cast
      PartialVal PV = PartialVal::getByteArray(Size);
      std::string error;
      PartialVal SrcPV = PartialVal::getPartial(bigConst, Offset);
      if(!PV.combineWith(SrcPV, 0, Size, Size, GlobalTD, error)) {
	Dest.setOverdef();
	return;
      }

      Type* ReinterpType = Type::getIntNTy(bigConst->getContext(), Size * 8);
      smallConst = constFromBytes(PV.partialBuf, ReinterpType, GlobalTD);

    }
    
    ShadowValue SV(smallConst);
    ImprovedValSetSingle NewIVS;
    getImprovedValSetSingle(SV, NewIVS);
    Dest.merge(NewIVS);
					  
  }
  
}

#define IVSR(x, y, z) std::make_pair(std::make_pair(x, y), z)

void llvm::readValRangeMultiFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, SmallVector<IVSRange, 4>& Results, ImprovedValSet* ignoreBelowStore) {

  if(ignoreBelowStore && ignoreBelowStore == store)
    return;

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(store)) {

    if(Offset == 0 && Size == V.getAllocSize()) {
      
      Results.push_back(IVSR(0, Size, *IVS));
      
    }
    else {
      
      ImprovedValSetSingle SubVal;
      getIVSSubVal(*IVS, Offset, Size, SubVal);
      Results.push_back(IVSR(Offset, Offset+Size, SubVal));
      
    }

  }
  else {
    
    ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(store);
    IVM::MapTy it = IVM->Map.find(Offset);

    // Value overlapping range on the left:
    if(it != IVM->Map.end() && it.start() < Offset) {

      // Read a sub-value:
      uint64_t SubvalOffset = Offset - it.start();
      uint64_t SubvalSize = std::min(Offset + Size, it.stop()) - Offset;
      
      ImprovedValSetSingle SubVal;
      getIVSSubVal(*it, SubvalOffset, SubvalSize, SubVal);
      Results.push_back(IVSR(Offset, Offset + SubvalSize, SubVal));
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
	readValRangeMultiFrom(V, Offset, it.start() - Offset, ReadBB, IVM->Underlying, Results, ignoreBelowStore);
	Size -= (it.start() - Offset);
	Offset = it.start();
	
      }

      if(it.stop() > (Offset + Size)) {

	// Overlap on the right: extract sub-val.
	ImprovedValSetSingle SubVal;
	getIVSSubVal(*it, 0, Size, SubVal);
	Results.push_back(IVSR(it.start(), Offset+Size, SubVal));
	Offset += Size;
	Size = 0;
	break;

      }
      else {

	// No overlap: use whole value.
	Results.push_back(IVSR(it.start(), it.stop(), *it));
	Offset += (it.stop() - it.start());
	Size -= (it.stop() - it.start());

      }

    }

    // Check for gap on the right:
    if(Size != 0) {

      release_assert(IVM->Underlying && "Gap but no underlying map/2?");
      readValRangeMultiFrom(V, Offset, Size, ReadBB, IVM->Underlying, Results, ignoreBelowStore);

    }

  }

}

void llvm::readValRangeMulti(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, SmallVector<IVSRange, 4>& Results) {

  // Try to make an IVS representing the block-local value of V+Offset -> Size.
  // Limitations for now: because our output is a single IVS, non-scalar types may only be described
  // if they correspond to a whole object.

  LocStore* firstStore;

  DenseMap<ShadowValue, LocStore>::iterator it = ReadBB->localStore->store.find(V);
  if(it == ReadBB->localStore->store.end()) {
    if(ReadBB->localStore->allOthersClobbered) {
      Results.push_back(IVSR(Offset, Offset+Size, ImprovedValSetSingle::getOverdef()));
      return;
    }
    else {
      firstStore = &(V.getBaseStore());
    }
  }
  else {
    firstStore = &(it->second);
  }

  PartialVal* ResultPV = 0;
  readValRangeMultiFrom(V, Offset, Size, ReadBB, firstStore, Results, 0);

}

void llvm::executeMemcpyInst(ShadowInstruction* MemcpySI) {

  ShadowBB* MemcpyBB = MemcpySI->parent;
  ShadowValue Ptr = MemcpySI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert(PtrSet.Overdef || PtrSet.Type == ValSetTypePB && "Write through non-pointer-typed value?");
  
  ConstantInt* LengthCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemcpySI->getCallArgOperand(2)));

  ShadowValue SrcPtr = MemcpySI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  release_assert(SrcPtrSet.Overdef || SrcPtrSet.Type == ValSetTypePB && "Memcpy from non-pointer value?");

  executeCopyInst(PtrSet, SrcPtrSet, LengthCI ? LengthCI->getLimitedValue() : ULONG_MAX, MemcpyBB);

}

void llvm::executeVaCopyInst(ShadowInstruction* SI) {
  
  ShadowBB* BB = SI->parent;
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert(PtrSet.Overdef || PtrSet.Type == ValSetTypePB && "Write through non-pointer-typed value?");
  
  ShadowValue SrcPtr = SI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  release_assert(SrcPtrSet.Overdef || SrcPtrSet.Type == ValSetTypePB && "Memcpy from non-pointer value?");
  
  executeCopyInst(PtrSet, SrcPtrSet, 24, BB);

}

void llvm::executeAllocInst(ShadowInstruction* SI, Type* AllocType, uint64_t AllocSize) {

  // Represent the store by a big undef value at the start.
  release_assert((!SI->store.store) && "Allocation already initialised?");
  Constant* Undef = UndefValue::get(AllocType);
  ImprovedVal IV(ShadowValue(Undef), 0);
  SI->store.store = new ImprovedValSetSingle(ImprovedValSetSingle::get(IV, ValSetTypeScalar));
  storeSize = AllocSize;

}

void llvm::executeAllocaInst(ShadowInstruction* SI) {

  // If the store is already initialised this must represent the general case of an allocation
  // within a loop or recursive call.
  if(SI->store.store)
    return;

  AllocaInst* AI = cast_inst<AllocaInst>(SI);
  Type* allocType = AI->getAllocatedType();
 
  if(AI->isArrayAlloction()) {

    ConstantInt* N = cast_or_null<ConstantInt>(getConstReplacement(AI->getArraySize()));
    if(!N)
      return;
    allocType = ArrayType::get(allocType, N->getLimitedValue());

  }

  executeAllocInst(SI, allocType, GlobalAA->getTypeStoreSize(allocType));

}

void llvm::executeMallocInst(ShadowInstruction* SI) {

  if(SI->store.store)
    return;

  ConstantInt* AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(0)));
  if(!AllocSize)
    return;

  Type* allocType = ArrayType::get(Type::getInt8Ty(SI->getContext()), AllocSize->getLimitedValue());

  executeAllocInst(SI, allocType, AllocSize->getLimitedValue());

}

void llvm::executeReallocInst(ShadowInstruction* SI) {

  if(!SI->store.store) {

    // Only alloc the first time; always carry out the copy implied by realloc.
    ConstantInt* AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(0)));
    if(!AllocSize)
      return;
    
    Type* allocType = ArrayType::get(Type::getInt8Ty(SI->getContext()), AllocSize->getLimitedValue());
    executeAllocInst(SI, allocType, AllocSize->getLimitedValue());    

  }

  ShadowValue SrcPtr = SI->getCallArgOperand(0);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Realloc from uninitialised PB?");
  release_assert(SrcPtrSet.Overdef || SrcPtrSet.Type == ValSetTypePB && "Realloc non-pointer-typed value?");
  uint64_t CopySize = ULONG_MAX;

  if(PtrSet.Overdef || PtrSet.Values.size() > 1) {

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

  if(Size == ULONG_MAX || PtrSet.Overdef || PtrSet.Values.size() != 1 || SrcPtrSet.Overdef || SrcPtrSet.Values.size() != 1) {

    // Only support memcpy from single pointer to single pointer for the time being:
    ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
    executeWriteInst(PtrSet, OD, Size, BB);
    return;

  }

  SmallVector<IVSRange, 4> copyValues;
  readValRangeMulti(SrcPtrSet.Values[0].V, SrcPtrSet.Values[0].Offset, Size, BB, copyValues);

  // OK now blow a hole in the local map for that value and write this list of extents into the gap:
  LocStore& Store = BB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, Size, copyValues.size() == 1);
  Store.store.replaceRangeWithPBs(copyValues, (uint64_t)PtrSet.Values[0].Offset, Size);

}

void llvm::executeVaStartInst(ShadowInstruction* SI) {

  ShadowBB* BB = SI->parent;
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;

  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert(PtrSet.Overdef || PtrSet.Type == ValSetTypePB && "Write through non-pointer-typed value?");

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
  Store.store.replaceRangeWithPBs(vaStartVals, (uint64_t)PtrSet.Values[0].Offset, 24);

}

void llvm::executeReadInst(ShadowInstruction* ReadSI, OpenStatus& OS, uint64_t FileOffset, uint64_t Size) {

  ShadowBB* ReadBB = ReadSI->parent;

  ShadowValue Ptr = ReadSI->getCallArgOperand(1);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB (read)?");
  release_assert(PtrSet.Overdef || PtrSet.Type == ValSetTypePB && "Write through non-pointer-typed value (read)?");

  ImprovedValSetSingle WriteIVS;
  
  if(PtrSet.Overdef || PtrSet.Values.size() != 1) {

    WriteIVS = ImprovedValSetSingle::getOverdef();

  }
  else {

    std::vector<Constant*> constBytes;
    std::string errors;
    LLVMContext& Context = Ptr.getBareVal().getContext();
    if(getFileBytes(OS->Name, FileOffset, Size, constBytes, Context,  errors)) {
      ArrayType* ArrType = ArrayType::get(IntegerType::get(Context, 8), constBytes.size());
      Constant* ByteArray = ConstantArray::get(ArrType, constBytes);
      WriteIVS = ImprovedValSetSingle::get(ByteArray);
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

    // See if we can discard the call because it's annotated read-only:

    if(F->onlyReadsMemory())
      return;

    // Otherwise do selective clobbering for annotated syscalls:

    if(LibCallFunctionInfo* FI = GlobalVFSAA->getFunctionInfo(F)) {
      
      const LibCallFunctionInfo::LocationMRInfo *Details = 0;

      if(FI->LocationDetails)
	Details = FI->LocationDetails;
      else if(FI->getLocationDetailsFor)
	Details = FI->getLocationDetailsFor(CS);

      release_assert(FI->DetailsType == LibCallFunctionInfo::DoesOnly);

      for (unsigned i = 0; Details[i].Location; ++i) {

	ShadowValue ClobberV;
	uint64_t ClobberSize;
	if(Details[i].Location.getLocation) {
	  Details[i].Location.getLocation(ClobberV, ClobberSize);
	}
	else {
	  ClobberV = getCalllArgOperand(SI, Details[i].Location.argIndex);
	  ClobberSize = Details[i].Location.argSize;
	}

	ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
	executeWriteInst(ClobberV, OD, ClobberSize, SI->parent);

      }

      return;

    }

  }

  // Finally clobber all locations; this call is entirely unhandled
  errs() << "Warning: unhandled call clobbers all locations";
  ImprovedValSetSingle OD = ImprovedValSetSingle::getOverdef();
  executeWriteInst(OD, OD, AliasAnalysis::UnknownSize, SI->parent);

}

void llvm::executeWriteInst(ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, uint64_t PtrSize, ShadowBB* StoreBB) {

  if(PtrSet.Overdef) {

    // Start with a plain local store map giving no locations.
    StoreBB->localStore->dropReference();
    StoreBB->localStore = new LocalStoreMap();
    StoreBB->localStore->allOthersClobbered = true;

  }
  else if(PtrSet.Values.size() == 1 && PtrSet.Values[0].Offset != LLONG_MAX) {

    // Best case: store through a single, certain pointer. Overwrite the location with our new PB.
    LocStore& Store = StoreBB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, PtrSize, true);
    Store.store.replaceRangeWithPB(ValPB, (uint64_t)PtrSet.Values[0].Offset, PtrSize);

  }
  else {

    for(SmallVector<ImprovedVal, 1>::iterator it = PtrSet.Values.begin(), it2 = PtrSet.Values.end(); it != it2; ++it) {

      if(it->Offset == LLONG_MAX) {
	LocStore& Store = StoreBB->getWritableStoreFor(it->V, 0, ULONG_MAX, true);
	Store.store.clobber();
      }
      else {

	ImprovedValSetSingle oldValSet;
	if(ValPB.Overdef) {

	  // Overdef merges with everything to make overdef, so don't bother with the lookup.
	  oldValSet = ValPB;

	}
	else {

	  std::string ignoreErrorHere;
	  readValRange(it->V, (uint64_t)it->Offset, PtrSize, StoreBB, oldValSet, ignoreErrorHere);

	  if((!oldValSet.Overdef) && oldValSet.isInitialised()) {

	    ValPB.coerceToType(oldValSet.Values[0].V.getType(), PtrSize, error);

	  }

	  oldValSet.merge(ValPB);

	}

	LocStore& Store = StoreBB->getWritableStoreFor(it->V, it->Offset, PtrSize, true);
	Store.store.replaceRangeWithPB(oldValSet, (uint64_t)it->Offset, PtrSize); 

      }

    }

  }

}

void LocalStoreMap::dropReference() {

  if(!--refCount) {

    // Drop references to any maps this points to;
    for(DenseMap<ShadowValue, LocStore>::iterator it = store.begin(), itend = store.end(); it != itend; ++it)
      it->second->store->dropReference();

    delete this;

  }

}

static bool getCommonAncestor(ImprovedValSet* LHS, ImprovedValSet* RHS, ImprovedValSet*& LHSResult, ImprovedValSet*& RHSResult, SmallPtrSet<ImprovedValSetMulti>& Seen) {

  if(ImprovedValSetSingle* LHSS = dyn_cast<ImprovedValSetSingle>(LHS)) {

    if(ImprovedValSetSingle* RHSS = dyn_cast<ImprovedValSetSingle>(RHS)) {
      
      bool match = (*LHS) == (*RHS);
      if(match) {
	
	LHSResult = LHS;
	RHSResult = RHS;
	return true;

      }
      return match;

    }
    else {

      // Flip args:
      return getCommonAncestor(RHS, LHS, RHSResult, LHSResult);

    }

  }

  ImprovedValSetMulti* LHSM = cast<ImprovedValSetMulti>(LHS);
  if(!Seen.insert(LHSM)) {
    LHSResult = LHSM;
    RHSResult = RHSM;
    return true;
  }

  // Neither side can advance?
  if((!LHSM->Underlying)) {

    if(isa<ImprovedValSetSingle>(RHS) || (!cast<ImprovedValSetMulti>(RHS)->Underlying))
      return false;

  }

  // Advance the LHS pointer if possible, flip args to advance other side next.
  return getCommonAncestor(RHS, LHS->Underlying ? LHS->Underlying : LHS, RHSResult, LHSResult);

}

struct MergeBlockVisitor : public ShadowBBVisitor {

  bool newMapValid
  LocalStoreMap* newMap;
  SmallPtrSet<LocalStoreMap*> seenMaps;
  bool mergeToBase;

  MergeBlockVisitor(bool mtb) : newMapValid(false), newMap(0), mergeToBase(mtb) { }

  void mergeStores(LocStore* mergeFromStore, LocStore* mergeToStore, ShadowValue& MergeV) {

    if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(mergeToStore->store)) {

      if(IVS->Overdef)
	return;

      if(ImprovedValSetSingle* IVS2 = dyn_cast<ImprovedValSetSingle>(mergeFromStore->store)) {
	IVS->merge(*IVS2);
	return;
      }

    }

    // Get an IVS list for each side that contains gaps where there is a common ancestor:
    ImprovedValSet *LHSAncestor, *RHSAncestor;
    {
      SmallPtrSet<ImprovedValSetMulti> Seen;
      // If we're making a new base store, flatten entirely.
      if(mergeToBase || !getCommonAncestor(mergeToStore->store, mergeFromStore->store, LHSAncestor, RHSAncestor, Seen)) {

	LHSAncestor = 0;
	RHSAncestor = 0;
	      
      }
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

      while(LHSit != LHSitend && RHSit != RHSitend) {

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
		
	  // Case (d) Leave a gap
	  anyGaps = true;
	  LastOffset = LHSit->first.first;

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

	  SmallVector<IVSRange, 4> baseVals;
	  readValRangeMultiFrom(MergeV, LastOffset, stopAt - LastOffset, BB, LHSAncestor, baseVals, 0);
		
	  for(SmallVector<IVSRange, 4>::iterator baseit = baseVals.begin(), baseend = baseVals.end();
	      baseit != baseend; ++baseit) {

	    ImprovedValSetSingle subVal;
	    getIVSSubVal(consumeit.second, baseit->first.first - consumeit->first.first, baseit->first.second - baseit->first.first, subVal);
	    subVal.merge(baseit->second);
	    MergedVals.push_back(IVSR(baseit->first.first, baseit->first.second, subVal));
		    
	  }

	  coveredBytes += (stopAt - LastOffset);
	  LastOffset = stopAt;
	  if(bump)
	    ++consumeit;
		
	}
	else {

	  // Both entries are defined here, case (c), so consumeit finishes equal or sooner.
	  ImprovedValSetSingle consumeVal;
	  getIVSSubVal(consumeit->second, LastOffset - consumeit->first.first, consumeit->first.second - LastOffset, consumeVal);
		
	  ImprovedValSetSingle otherVal;
	  getIVSSubVal(otherit->second, LastOffset - otherit->first.first, consumeit->first.second - LastOffset, otherVal);
		
	  consumeVal.merge(otherVal);
	  MergedVals.push_back(IVSR(LastOffset, consumeit->first.second, otherVal));

	  LastOffset = consumeit->first.second;

	  ++consumeit;
	  if(consumeit->first.second == otherit->first.second)
	    ++otherit;

	}
	      
      }
      
      // MergedVals is now an in-order extent list of values for the merged store
      // except for gaps where LHSAncestor (or RHSAncestor) would show through.
      // Figure out if we in fact have any gaps:

      ImprovedValSet* newUnderlying;

      if(anyGaps || (LHSVals.back().first.second != TotalBytes && RHSVals.back().first.second != TotalBytes))
	newUnderlying = LHSAncestor->getReadableCopy();
      else
	newUnderlying = 0;

      // Get a Multi to populate: either clear an existing one or allocate one.

      ImprovedValSetMulti* newStore;

      if(mergeToStore->store->isWritableMulti()) {
	ImprovedValSetMulti* M = cast<ImprovedValSetMulti>(mergeToStore->store);
	M->Map.clear();
	if(M->Underlying)
	  M->dropReference();
	newStore = M;
      }
      else {
	mergeToStore->store->dropReference();
	newStore = new ImprovedValSetMulti();
      }	

      newStore->Underlying = newUnderlying;

      newStore::MapIt insertit = newStore->Map.end();
      for(SmallVector<IVSRange, 4>::iterator finalit = MergedVals.begin(), finalitend = MergedVals.end();
	  finalit != finalitend; ++finalit) {

	insertit.insert(finalit->first.first, finalit->first.second, finalit->second);
	
      }

      mergeToStore->store = newStore;

    }

  }

  void visit(ShadowBB* BB, void* Ctx, bool mustCopyCtx) {

    if(!seenMaps.insert(BB->localStore)) {
      // We've already seen this exact map as a pred; drop the extra ref.
      return;
    }

    if(!newMapValid) {
      // This is the first predecessor, borrow the incoming block's map / use the base map.
      // Note that the refcount is already correct (blocks assume their map will be taken per default)
      // Also note if the incoming block shadowed nothing this might still leave newMap == 0.
      newMap = BB->localStore;
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

      if(mergeFromMap) {

	if(mergeFromMap->allOthersClobbered) {

	  SmallVector<ShadowValue, 4> keysToRemove;

	  // Remove any existing mappings in mergeMap that do not occur in mergeFromMap:
	  for(DenseMap<ShadowValue, LocStore>::iterator it = mergeMap->store.begin(), itend = mergeMap->store.end();
	      it != itend; ++it) {

	    if(!mergeFromMap->store.count(it->first)) {

	      keysToRemove.push_back(it->first);
	      it->second.store.dropReference();

	    }

	  }

	  for(SmallVector<ShadowValue, 4>::iterator delit = keysToRemove.begin(), delitend = keysToRemove.end();
	      delit != delitend; ++delit) {

	    mergeMap->store.erase(*delit);

	  }

	  mergeMap->allOthersClobbered = true;

	}
	else if(!mergeMap->allOthersClobbered) {

	  // For any locations mentioned in mergeFromMap but not mergeMap,
	  // move them over. We'll still need to merge in the base object below, this
	  // just creates the asymmetry that x in mergeFromMap -> x in mergeMap.
	  
	  SmallVector<ShadowValue, 4> toDelete;

	  for(DenseMap<ShadowValue, LocStore>::iterator it = mergeFromMap->store.begin(),
		itend = mergeFromMap->store.end(); it != itend; ++it) {
	
	    std::pair<DenseMap<ShadowValue, LocStore>::iterator, bool> ins = 
	      mergeMap->insert(it->first, it->second);
	
	    if(it->second)
	      toDelete.push_back(it->first);

	  }
      
	  for(SmallVector<ShadowValue, 4>::iterator delit = toDelete.begin(), delend = toDelete.end();
	      delit != delend; ++delit)
	    mergeFromMap->erase(*delit);

	}

      }

      // mergeMap now contains all information from one or other incoming branch;
      // for each location it mentions merge in the other map's version or the base object.
      // Note that in the mergeMap->allOthersClobbered case this only merges in
      // information from locations explicitly mentioned in mergeMap.

      for(DenseMap<ShadowValue, LocStore>::iterator it = mergeMap->store.begin(),
	    itend = mergeMap->store.end(); it != itend; ++it) {

	LocStore* mergeFromStore;
	if(!mergeFromMap)
	  mergeFromStore = &it->first.getBaseStore();
	else {
	  DenseMap<ShadowValue, LocStore>::iterator found = mergeFromMap->store.find(it->first);
	  if(found != mergeFromMap->store.end())
	    mergeFromStore = &(found->second);
	  else
	    mergeFromStore = &it->first.getBaseStore();
	}

	// Right, merge it->second and mergeFromStore.
	// If the pointers match these are two refs to the same Multi.
	// Refcounting will be caught up when we deref mergeFromMap below:
	if(mergeFromStore->store != it->second->store) {

	  mergeStores(it->first, mergeFromStore, &it->second);

	}

      }

      if(mergeFromMap)
	mergeFromMap->dropReference();

      newMap = mergeMap;

    }

  }

};

void llvm::commitStoreToBase(LocalStoreMap* Map) {

  for(DenseMap<ShadowValue, LocStore>::iterator it = Map->begin(), itend = Map->end(); it != itend; ++it) {

    LocStore* baseStore = it->first.getBaseStore();
    release_assert(baseStore && "No base store?");
    baseStore->store.dropReference();
    baseStore->store = it->second.store->getReadableCopy();

  }

}

void llvm::doBlockStoreMerge(ShadowBB* BB) {

  // We're entering BB; one or more live predecessor blocks exist and we must produce an appropriate
  // localStore from them.

  bool mergeToBase = BB->status == BBSTATUS_CERTAIN;
  // This BB is a merge of all that has gone before; merge to values' base stores
  // rather than a local map.

  MergeBlockVisitor V(mergeToBase);
  BB->IA->visitNormalPredecessorsBW(BB, &V, /* ctx = */0);

  // TODO: do this better
  if(mergeToBase && !V.newMap->allOthersClobbered) {
    commitStoreToBase(V.newMap);
    V.newMap->store.dropReference();
  }
  else
    BB->localStore = V.newMap;

}

void llvm::doCallStoreMerge(ShadowInstruction* SI) {

  bool mergeToBase = SI->parent->status == BBSTATUS_CERTAIN;
  InlineAttempt* CallIA = SI->parent->IA->getInlineAttempt(cast_inst<CallInst>(SI));

  MergeBlockVisitor V(mergeToBase);
  CallIA->visitLiveReturnBlocks(SI);

  if(mergeToBase && !V.newMap->allOthersClobbered) {
    commitStoreToBase(V.newMap);
    V.newMap->dropReference();
    // Blank block-local map.
    SI->parent->localStore = new LocalStoreMap();
  }
  else
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

  if(V1.isVal()) {

    if(!V2.isVal())
      return false;
    else
      return V1.getVal() == V2.getVal();

  }
  else if(V1.isArg()) {

    if(!V2.isArg())
      return false;
    return V1.getArg() == V2.getArg();

  }
  else {

    if(!V2.isInst())
      return false;

    if(V1.getInst()->invar == V2.getInst()->invar) {

      return (V1.getCtx()->ctxContains(V2.getCtx()) || V2.getCtx()->ctxContains(V1.getCtx()));

    }
    else
      return false;

  }
   
}
