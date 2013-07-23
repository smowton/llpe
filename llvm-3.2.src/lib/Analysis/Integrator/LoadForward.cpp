
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

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"

#include <memory>

using namespace llvm;

ImprovedValSetMulti::ImprovedValSetMulti(ShadowValue& V) : ImprovedValSet(true), Map(GlobalIHP->IMapAllocator), MapRefCount(1), Underlying(0), CoveredBytes(0) {

  AllocSize = V.getAllocSize();

}

ImprovedValSetMulti::ImprovedValSetMulti(uint64_t ASize) : ImprovedValSet(true), Map(GlobalIHP->IMapAllocator), MapRefCount(1), Underlying(0), CoveredBytes(0), AllocSize(ASize) { }

ImprovedValSetMulti::ImprovedValSetMulti(const ImprovedValSetMulti& other) : ImprovedValSet(true), Map(GlobalIHP->IMapAllocator), MapRefCount(1), Underlying(other.Underlying), CoveredBytes(other.CoveredBytes), AllocSize(other.AllocSize) {

  if(Underlying)
    Underlying = Underlying->getReadableCopy();

  for(ImprovedValSetMulti::ConstMapIt it = other.Map.begin(), itend = other.Map.end(); it != itend; ++it) {

    Map.insert(it.start(), it.stop(), *it);

  }

}

// Only declare multis equal when the topmost map is trivially equal.
// It still might be possible to flatten the maps to discover they represent the same information.
bool llvm::operator==(ImprovedValSetMulti& PB1, ImprovedValSetMulti& PB2) {

  ImprovedValSetMulti::MapIt 
    it1 = PB1.Map.begin(), it1end = PB1.Map.end(), 
    it2 = PB2.Map.begin(), it2end = PB2.Map.end();

  for(; it1 != it1end && it2 != it2end; ++it1, ++it2) {

    if(it1.start() != it2.start() || it1.stop() != it2.stop() || it1.val() != it2.val())
      return false;

  }

  // Lengths differed?
  if(it1 != it1end || it2 != it2end)
    return false;

  return true;

}

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

bool PartialVal::convertToBytes(uint64_t size, DataLayout* TD, std::string* error) {

  if(isByteArray())
    return true;

  PartialVal conv(size);
  if(!conv.combineWith(*this, 0, size, size, TD, error))
    return false;

  (*this) = conv;

  return true;

}

bool PartialVal::combineWith(PartialVal& Other, uint64_t FirstDef, uint64_t FirstNotDef, uint64_t LoadSize, DataLayout* TD, std::string* error) {

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
      if(error)
	*error = "PP2";
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
      if(error)
	*error = "RDFG";
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

Constant* llvm::PVToConst(PartialVal& PV, raw_string_ostream* RSO, uint64_t Size, LLVMContext& Ctx) {

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
	return extr;

    }
    else {

      if(RSO)
	*RSO << "NonConstBOps";
      return 0;

    }

  }

  // Finally build it from bytes.
  std::auto_ptr<std::string> error(RSO ? new std::string() : 0);
  if(!PV.convertToBytes(Size, GlobalTD, error.get())) {
    if(RSO)
      *RSO << *error;
    return 0;
  }

  assert(PV.isByteArray());

  Type* targetType = Type::getIntNTy(Ctx, Size * 8);
  return constFromBytes((unsigned char*)PV.partialBuf, targetType, GlobalTD);

}

bool IntegrationAttempt::tryResolveLoadFromConstant(ShadowInstruction* LoadI, ImprovedValSet*& Result, std::string* error) {

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
	  if(error)
	    *error = "Const out of range";
	  Result = newOverdefIVS();
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

    if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(SI->i.PB)) {

      if(IVS->Values.size() > 0 && IVS->SetType == ValSetTypePB) {

	bool foundNonNull = false;
	bool foundNonConst = false;
	for(unsigned i = 0; i < IVS->Values.size(); ++i) {

	  Value* BaseV = IVS->Values[i].V.getVal();

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
	  ImprovedValSetSingle* NewIVS = newIVS();
	  Result = NewIVS;
	  NewIVS->set(ResultIV.second, ResultIV.first);
	  return true;

	}
	else if(!foundNonConst) {

	  LPDEBUG("Load cannot presently be resolved, but is rooted on a constant global. Abandoning search\n");
	  if(error)
	    *error = "Const pointer vague";
	  Result = newOverdefIVS();
	  return true;

	}

      }

    }

  }

  return false;

}

static bool shouldMultiload(ImprovedValSetSingle& PB) {

  if(PB.isWhollyUnknown() || PB.Values.size() == 0)
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

static bool tryMultiload(ShadowInstruction* LI, ImprovedValSet*& NewIV, std::string* report) {

  uint64_t LoadSize = GlobalAA->getTypeStoreSize(LI->getType());

  // We already know that LI's IVSet is made up entirely of nulls and definite pointers.
  ImprovedValSetSingle* NewPB = newIVS();
  NewIV = NewPB;

  ImprovedValSetSingle LIPB;
  getImprovedValSetSingle(LI->getOperand(0), LIPB);

  std::auto_ptr<raw_string_ostream> RSO(report ? new raw_string_ostream(*report) : 0);

  for(uint32_t i = 0, ilim = LIPB.Values.size(); i != ilim && !NewPB->Overdef; ++i) {

    if(Value* V = LIPB.Values[i].V.getVal()) {
      if(isa<ConstantPointerNull>(V)) {

	Type* defType = LI->getType();
	Constant* nullVal = Constant::getNullValue(defType);
	std::pair<ValSetType, ImprovedVal> ResultIV = getValPB(nullVal);
	ImprovedValSetSingle NullPB(ResultIV.second, ResultIV.first);
	NewPB->merge(NullPB);
	continue;

      }
    }

    std::auto_ptr<std::string> ThisError(RSO.get() ? new std::string() : 0);
    ImprovedValSetSingle ThisPB;
    ImprovedValSetMulti* ThisMulti = 0;

    // Permit readValRange to allocate and return a multi if appropriate (i.e. if it finds the desired
    // range includes a non-scalar value)
    readValRange(LIPB.Values[i].V, LIPB.Values[i].Offset, LoadSize, LI->parent, ThisPB, LIPB.Values.size() == 1 ? &ThisMulti : 0, ThisError.get());

    // Sharing now contingent on this object!
    if(ThisMulti || !ThisPB.isWhollyUnknown()) {

      LI->parent->IA->noteDependency(LIPB.Values[i].V);

    }

    if(ThisMulti) {

      deleteIVS(NewPB);
      NewIV = ThisMulti;
      return true;

    }

    if(!ThisPB.isWhollyUnknown()) {
      if(!ThisPB.coerceToType(LI->getType(), LoadSize, ThisError.get())) {
	NewPB->setOverdef();
      }
      else {
	NewPB->merge(ThisPB);
      }
    }
    else {
      NewPB->merge(ThisPB);
    }

    if(RSO.get()) {

      if(ThisPB.Overdef) {
	
	*RSO << "Load " << itcache(LIPB.Values[i].V, true) << " -> " << *ThisError;

      }
      else if(NewPB->Overdef) {
	
	*RSO << "Loaded ";
	printPB(*RSO, ThisPB, true);
	*RSO << " -merge-> " << *ThisError;

      }

    }

  }

  return NewPB->isInitialised();

}

// Fish a value out of the block-local or value store for LI.
bool IntegrationAttempt::tryForwardLoadPB(ShadowInstruction* LI, ImprovedValSet*& NewPB, bool& loadedVararg) {

  ImprovedValSetSingle ConstResult;
  std::auto_ptr<std::string> error(pass->verboseOverdef ? new std::string() : 0);

  if(tryResolveLoadFromConstant(LI, NewPB, error.get())) {
    ImprovedValSetSingle* NewIVS = dyn_cast<ImprovedValSetSingle>(NewPB);
    if(NewIVS && NewIVS->Overdef && pass->verboseOverdef)
      optimisticForwardStatus[LI->invar->I] = *error;
    if(NewIVS)
      return NewIVS->isInitialised();
    else
      return true;
  }

  bool ret;

  ImprovedValSetSingle LoadPtrPB;
  getImprovedValSetSingle(LI->getOperand(0), LoadPtrPB);
  if(shouldMultiload(LoadPtrPB)) {

    ret = tryMultiload(LI, NewPB, error.get());
    if(ImprovedValSetSingle* NewIVS = dyn_cast<ImprovedValSetSingle>(NewPB)) {

      if(NewIVS->SetType == ValSetTypeVarArg)
	loadedVararg = true;

      if(NewIVS->SetType == ValSetTypeScalar) {

	release_assert(!val_is<ConstantPointerNull>(NewIVS->Values[0].V));

      }

    }

  }
  else {

    // Load from a vague pointer -> Overdef.
    ret = true;
    if(error.get()) {
      raw_string_ostream RSO(*error);
      RSO << "Load vague ";
      printPB(RSO, LoadPtrPB, true);
    }

    if(LoadPtrPB.isOldValue()) {
      ImprovedValSetSingle* NewIVS = newIVS();
      NewPB = NewIVS;
      NewIVS->SetType = ValSetTypeOldOverdef;
    }
    else {
      NewPB = newOverdefIVS();
    }

  }

  if(error.get())
    optimisticForwardStatus[LI->invar->I] = *error;
   
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
      
  if(PB2.isWhollyUnknown())
    return SVMayAlias;

  if(PB2.SetType != ValSetTypePB)
    return SVMayAlias;

  return tryResolveImprovedValSetSingles(PB1, V1Size, PB2, V2Size, usePBKnowledge);

}

SVAAResult llvm::tryResolveImprovedValSetSingles(ShadowValue V1, uint64_t V1Size, ShadowValue V2, uint64_t V2Size, bool usePBKnowledge) {
      
  ImprovedValSetSingle PB1, PB2;
  if((!getImprovedValSetSingle(V1, PB1)) || (!getImprovedValSetSingle(V2, PB2)))
    return SVMayAlias;
      
  if(PB1.isWhollyUnknown() || PB2.isWhollyUnknown())
    return SVMayAlias;

  if(PB1.SetType != ValSetTypePB || PB2.SetType != ValSetTypePB)
    return SVMayAlias;

  return tryResolveImprovedValSetSingles(PB1, V1Size, PB2, V2Size, usePBKnowledge);
       
}

#define LFV3(x) do {} while(0)
//#define LFV3(x) x

int32_t ShadowValue::getHeapKey() {

  switch(t) {

  case SHADOWVAL_INST:
    return u.I->allocIdx;
  case SHADOWVAL_GV:
    return u.GV->allocIdx;
  case SHADOWVAL_OTHER:
    {
      Function* KeyF = cast<Function>(u.V);
      SpecialLocationDescriptor& sd = GlobalIHP->specialLocations[KeyF];
      return sd.heapIdx;
    }
  case SHADOWVAL_ARG:
    release_assert((u.A->IA->Callers.empty()) && "getHeapKey on arg other than root argv?");
    return GlobalIHP->argStores[u.A->invar->A->getArgNo()].second;
  default:
    return -1;

  }

}

uint64_t ShadowValue::getAllocSize() {

  switch(t) {
  case SHADOWVAL_INST:
    release_assert(u.I->store.store && "getAllocSize on instruction without store");
    return u.I->storeSize;
  case SHADOWVAL_GV:
    return u.GV->storeSize;
  case SHADOWVAL_OTHER:
    return GlobalIHP->specialLocations[cast<Function>(u.V)].storeSize;
  case SHADOWVAL_ARG:
    // Arg objects currently of unknown size
    return ULONG_MAX;
   
  default:
    llvm_unreachable("getAllocSize on non-inst, non-GV value");
  }

}

ShadowValue& llvm::getAllocWithIdx(int32_t idx) {

  return GlobalIHP->heap[idx];

}

int32_t ShadowValue::getFrameNo() {

  ShadowInstruction* SI = getInst();
  if(!SI)
    return -1;

  if(inst_is<AllocaInst>(SI))
    return SI->parent->IA->stack_depth;

  return -1;

}

LocStore* SharedTreeNode::getReadableStoreFor(uint32_t idx, uint32_t height) {

  uint32_t nextChild = (idx >> (height * HEAPTREEORDERLOG2)) & (HEAPTREEORDER-1);

  if(!children[nextChild])
    return 0;

  if(height == 0) {

    // Our children are leaves.
    return (LocStore*)children[nextChild];

  }
  else {

    // Walk further down the tree.
    return ((SharedTreeNode*)children[nextChild])->getReadableStoreFor(idx, height - 1);

  }

}

LocStore* SharedTreeRoot::getReadableStoreFor(ShadowValue& V) {

  // Empty heap?
  if(height == 0)
    return 0;

  // Is a valid allocation instruction?
  int32_t idx = V.getHeapKey();
  if(idx < 0)
    return 0;

  // OK search:
  return root->getReadableStoreFor((uint32_t)idx, height - 1);

}

LocStore* LocalStoreMap::getReadableStoreFor(ShadowValue& V) {
  
  int32_t frameNo = V.getFrameNo();
  if(frameNo == -1)
    return heap.getReadableStoreFor(V);
  else {

    std::vector<LocStore>& frame = frames[frameNo]->store;
    uint32_t frameIdx = V.u.I->allocIdx;
    if(frame.size() <= frameIdx)
      return 0;

    LocStore* ret = &(frame[frameIdx]);
    if(!ret->store)
      return 0;
    else
      return ret;

  }
  
}

LocStore* ShadowBB::getReadableStoreFor(ShadowValue& V) {

  return localStore->getReadableStoreFor(V);

}

LocStore* SharedTreeNode::getOrCreateStoreFor(uint32_t idx, uint32_t height, bool* isNewStore) {

  // This node already known writable.

  uint32_t nextChild = (idx >> (height * HEAPTREEORDERLOG2)) & (HEAPTREEORDER-1);
  
  if(height == 0) {
    
    bool mustCreate = *isNewStore = (children[nextChild] == 0);
    if(mustCreate)
      children[nextChild] = new LocStore();
    return (LocStore*)children[nextChild];

  }
  else {

    SharedTreeNode* child;

    if(!children[nextChild])
      child = new SharedTreeNode();
    else
      child = ((SharedTreeNode*)children[nextChild])->getWritableNode(height - 1);

    children[nextChild] = child;
    return child->getOrCreateStoreFor(idx, height - 1, isNewStore);

  }

}

SharedTreeNode* SharedTreeNode::getWritableNode(uint32_t height) {

  if(refCount == 1)
    return this;

  // COW break this node.
  SharedTreeNode* newNode = new SharedTreeNode();

  if(height == 0) {

    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      if(children[i])
	newNode->children[i] = ((LocStore*)children[i])->getReadableCopy();	
      
    }

  }
  else {

    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      if(children[i]) {
	((SharedTreeNode*)children[i])->refCount++;
	newNode->children[i] = children[i];
      }

    }

  }

  // Drop ref to this node.
  --refCount;

  return newNode;

}

static uint32_t getRequiredHeight(uint32_t idx) {

  uint32_t height = 0;

  do {

    idx >>= HEAPTREEORDERLOG2;
    ++height;

  } while(idx);

  return height;

}

void SharedTreeRoot::growToHeight(uint32_t newHeight) {

  for(uint32_t i = 0, ilim = (newHeight - height); i != ilim; ++i) {

    SharedTreeNode* newNode = new SharedTreeNode();
    newNode->children[0] = root;
    root = newNode;

  }

  height = newHeight;

}

void SharedTreeRoot::grow(uint32_t idx) {

  // Need to make the tree taller first (hopefully the above test is cheaper than getReqdHeight)
  uint32_t newHeight = getRequiredHeight(idx);
  growToHeight(newHeight);

}

bool SharedTreeRoot::mustGrowFor(uint32_t idx) {

  return idx >= (uint32_t)(HEAPTREEORDER << ((height - 1) * HEAPTREEORDERLOG2));

}

LocStore* SharedTreeRoot::getOrCreateStoreFor(ShadowValue& V, bool* isNewStore) {

  int32_t idx = V.getHeapKey();

  if(idx < 0)
    release_assert(0 && "Tried to write to non-allocation?");

  if(!root) {

    // Empty heap.
    root = new SharedTreeNode();
    height = getRequiredHeight(idx);

  }
  else if(mustGrowFor(idx)) {

    grow(idx);

  }
  else {

    root = root->getWritableNode(height - 1);

  }

  return root->getOrCreateStoreFor(idx, height - 1, isNewStore);

}

LocStore* ShadowBB::getOrCreateStoreFor(ShadowValue& V, bool* isNewStore) {

  localStore = localStore->getWritableFrameList();

  int32_t frameNo = V.getFrameNo();
  if(frameNo != -1) {

    std::vector<LocStore>& frameMap = localStore->getWritableFrame(frameNo);
    localStore->frames[frameNo]->empty = false;
    int32_t framePos = V.u.I->allocIdx;
    release_assert(framePos >= 0 && "Stack entry without an index?");
    if(frameMap.size() <= (uint32_t)framePos)
      frameMap.resize(framePos + 1);
    *isNewStore = frameMap[framePos].store == 0;
    return &(frameMap[framePos]);

  }
  else {

    return localStore->heap.getOrCreateStoreFor(V, isNewStore);

  }

}

LocalStoreMap* LocalStoreMap::getWritableFrameList() {

  if(refCount == 1)
    return this;

  LocalStoreMap* newMap = new LocalStoreMap(frames.size());
  newMap->copyFramesFrom(*this);

  newMap->allOthersClobbered = allOthersClobbered;

  // Can't destory, as refCount > 1
  --refCount;

  return newMap;

}

std::vector<LocStore>& LocalStoreMap::getWritableFrame(int32_t frameNo) {

  release_assert(frameNo >= 0 && frameNo < (int32_t)frames.size());
  frames[frameNo] = frames[frameNo]->getWritableStoreMap();
  return frames[frameNo]->store;

}

SharedStoreMap* SharedStoreMap::getWritableStoreMap() {

  // Refcount == 1 means we can just write in place.
  if(refCount == 1) {
    LFV3(errs() << "Local map " << this << " already writable\n");
    return this;
  }

  // COW break: copy the map and either share or copy its entries.
  LFV3(errs() << "COW break local map " << this << " with " << store.size() << " entries\n");
  SharedStoreMap* newMap = new SharedStoreMap(IA, store.size());

  uint32_t i = 0;
  for(std::vector<LocStore>::iterator it = store.begin(), it2 = store.end(); it != it2; ++it, ++i) {
    if(!it->store)
      continue;
    newMap->store[i] = LocStore(it->store->getReadableCopy());
  }

  // Drop reference on the existing map (can't destroy it):
  refCount--;
  
  return newMap;

}

LocStore& ShadowBB::getWritableStoreFor(ShadowValue& V, int64_t Offset, uint64_t Size, bool willWriteSingleObject) {

  // We're about to write to memory location V + Offset -> Offset+Size. 
  // We must return a LocStore for that value that can be updated (i.e. is not shared).

  // Can write direct to the base store if we're sure this write is "for good".
  LocStore* ret = 0;
  if(status == BBSTATUS_CERTAIN && (!inAnyLoop) && (!localStore->allOthersClobbered) && !IA->pass->enableSharing) {
    LFV3(errs() << "Use bsase store for " << IA->F.getName() << " / " << IA->SeqNumber << " / " << invar->BB->getName() << "\n");
    ret = &V.getBaseStore();
  }

  // Otherwise we need to write into the block-local store map. COW break it if necessary:
  bool writeWholeObject = (Offset == 0 && (Size == ULONG_MAX || Size == V.getAllocSize()));
   
  if(!ret) {

    bool isNewStore;
    ret = getOrCreateStoreFor(V, &isNewStore);
  
    if(isNewStore) {

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

      LFV3(errs() << "Use existing store " << ret->store << "\n");

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

bool llvm::addIVSToPartialVal(ImprovedValSetSingle& IVS, uint64_t IVSOffset, uint64_t PVOffset, uint64_t Size, PartialVal* PV, std::string* error) {

  release_assert(PV && PV->type == PVByteArray && "Must allocate PV before calling addIVSToPartialVal");

  // For now we forbid building from bytes when an input is set-typed:
  if(IVS.isWhollyUnknown() || IVS.Values.size() != 1)
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

void llvm::readValRangeFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, ImprovedValSetSingle& Result, PartialVal*& ResultPV, bool& shouldTryMulti, std::string* error) {

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
      
      bool rejectHere = IVS->isWhollyUnknown() || (IVS->SetType != ValSetTypeScalar && IVS->SetType != ValSetTypeScalarSplat);
      if(rejectHere) {
	LFV3(errs() << "Reject: non-scalar\n");
	Result.setOverdef();
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
      Result.setOverdef();

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
      Result.setOverdef();

      if((it.val().SetType == ValSetTypePB || it.val().SetType == ValSetTypeFD) 
	 && FirstReadByte == it.start() 
	 && LastReadByte == it.stop()) {

	// This read would read a whole FD or pointer, but can't because we can't express those
	// as bytes. It's therefore worth trying again with a more expensive multi descriptor.

	shouldTryMulti = true;
      
      }

      return;
    }

  }
  
  if((!ResultPV) || !ResultPV->isComplete()) {
      
    // Try the next linked map (one should exist:)
    release_assert(IVM->Underlying && "Value not complete, but no underlying map?");
    LFV3(errs() << "Defer to next map: " << IVM->Underlying << "\n");
    readValRangeFrom(V, Offset, Size, ReadBB, IVM->Underlying, Result, ResultPV, shouldTryMulti, error);
      
  }

}

void llvm::readValRange(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSetSingle& Result, ImprovedValSetMulti** ResultMulti, std::string* error) {

  // Try to make an IVS representing the block-local value of V+Offset -> Size.
  // Limitations for now: because our output is a single IVS, non-scalar types may only be described
  // if they correspond to a whole object.

  LFV3(errs() << "Start read " << Offset << "-" << (Offset + Size) << "\n");

  LocStore* firstStore = ReadBB->getReadableStoreFor(V);
  if(!firstStore) {
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
  }

  PartialVal* ResultPV = 0;
  bool shouldTryMulti = false;
  readValRangeFrom(V, Offset, Size, ReadBB, firstStore->store, Result, ResultPV, shouldTryMulti, error);

  if(ResultPV) {

    LFV3(errs() << "Read used a PV\n");
    std::auto_ptr<raw_string_ostream> RSO(error ? new raw_string_ostream(*error) : 0);

    Constant* PVConst = PVToConst(*ResultPV, RSO.get(), Size, V.getLLVMContext());
    ShadowValue PVConstV(PVConst);
    addValToPB(PVConstV, Result);

    delete ResultPV;

  }
  else if(shouldTryMulti && ResultMulti) {

    // The read covered an FD or pointer. Try to load a multi instead.
    SmallVector<IVSRange, 4> Results;
    readValRangeMulti(V, Offset, Size, ReadBB, Results);

    // Relabel offsets relative to this read, and check whether we're returning anything worthwhile
    // (i.e. not overdef'd).
    bool anyGoodValues = false;
    for(SmallVector<IVSRange, 4>::iterator it = Results.begin(), itend = Results.end(); it != itend; ++it) {
      
      if(it->second.isInitialised())
	anyGoodValues = true;
      it->first.first -= Offset;
      it->first.second -= Offset;

    }

    if(anyGoodValues) {

      ImprovedValSetMulti* IVM = new ImprovedValSetMulti(Size);
      ImprovedValSetMulti::MapIt it = IVM->Map.begin();

      for(unsigned i = 0, iend = Results.size(); i != iend; ++i) {

	IVSRange& RangeVal = Results[i];
	it.insert(RangeVal.first.first, RangeVal.first.second, RangeVal.second);
	++it;

      }

      *ResultMulti = IVM;

    }
    else {

      Result.setOverdef();
      
    }
    
  }

}

bool ImprovedValSetSingle::coerceToType(Type* Target, uint64_t TargetSize, std::string* error) {

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
    if(error)
      *error = "Non-scalar coercion";
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
	  if(error)
	    *error = "Cast non-zero to pointer";
	  return false;
	}
	
      }

      SetType = ValSetTypePB;

    }

    Values[i].V = ShadowValue(constFromBytes((unsigned char*)PV.partialBuf, Target, GlobalTD));

  }

  return true;

}

#define IVSR(x, y, z) std::make_pair(std::make_pair(x, y), z)
#define AddIVSConst(x, y, z) do { std::pair<ValSetType, ImprovedVal> V = getValPB(z); Dest.push_back(IVSR(x + OffsetAbove, x + y + OffsetAbove, ImprovedValSetSingle(V.second, V.first))); } while(0);

static bool mayContainPointers(ImprovedValSet* IV) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IV)) {

    return IVS->SetType == ValSetTypePB || IVS->SetType == ValSetTypeUnknown;

  }

  ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(IV);

  for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {

    ImprovedValSetSingle& IVS = it.val();
    if(IVS.SetType == ValSetTypePB || IVS.SetType == ValSetTypeUnknown)
      return true;

  }

  return false;

}

static ImprovedValSetSingle getOverdefFor(ImprovedValSet* IV) {

  if(mayContainPointers(IV))
    return ImprovedValSetSingle(ValSetTypePB, true);
  else
    return ImprovedValSetSingle(ValSetTypeScalar, true);

}

void llvm::executeStoreInst(ShadowInstruction* StoreSI) {

  // Get written location:
  ShadowBB* StoreBB = StoreSI->parent;
  ShadowValue Ptr = StoreSI->getOperand(1);
  uint64_t PtrSize = GlobalAA->getTypeStoreSize(StoreSI->invar->I->getOperand(0)->getType());

  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB) 
		 && "Write through non-pointer-typed value?");

  ShadowValue Val = StoreSI->getOperand(0);
  if(ImprovedValSetMulti* IVM = dyn_cast_or_null<ImprovedValSetMulti>(tryGetIVSRef(Val))) {

    if(PtrSet.Values.size() != 1) {

      ImprovedValSetSingle OD = getOverdefFor(IVM);
      executeWriteInst(&Ptr, PtrSet, OD, PtrSize, StoreSI);

    }
    else {

      SmallVector<IVSRange, 4> Vals;
      for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {
	
	Vals.push_back(IVSR(it.start() + PtrSet.Values[0].Offset, it.stop() + PtrSet.Values[0].Offset, it.val()));

      }

      writeExtents(Vals, PtrSet.Values[0].V, PtrSet.Values[0].Offset, PtrSize, StoreBB);
      for(SmallVector<IVSRange, 4>::iterator it = Vals.begin(), itend = Vals.end(); it != itend; ++it) {

	propagateStoreFlags(PtrSet, it->second, StoreBB);

      }

    }

  }
  else {

    ImprovedValSetSingle ValPB;
    getImprovedValSetSingle(Val, ValPB);

    executeWriteInst(&Ptr, PtrSet, ValPB, PtrSize, StoreSI);

  }

}

void llvm::executeMemsetInst(ShadowInstruction* MemsetSI) {

  ShadowValue Ptr = MemsetSI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");
  
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

  executeWriteInst(&Ptr, PtrSet, ValSet, LengthCI ? LengthCI->getLimitedValue() : ULONG_MAX, MemsetSI);
  
}

void llvm::getIVSSubVals(ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest) {

  // Subvals only allowed for scalars:

  if(Src.isWhollyUnknown() || Src.Values.size() == 0) {
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
    Dest.push_back(IVSR(OffsetAbove + Offset, OffsetAbove + Offset + Size, ImprovedValSetSingle(ValSetTypeUnknown, true)));
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
    Dest.push_back(IVSR(FromSize, (Offset + TargetSize) - FromSize, ImprovedValSetSingle(ValSetTypeUnknown, true)));
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
      Dest.push_back(IVSR(Offset, TargetSize, ImprovedValSetSingle(ValSetTypeUnknown, true)));
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

      Dest.push_back(IVSR(Offset, TargetSize, ImprovedValSetSingle(ValSetTypeUnknown, true)));      

    }

  }
  
}

Constant* llvm::valsToConst(SmallVector<IVSRange, 4>& subVals, uint64_t TargetSize, Type* targetType) {

  if(subVals.size() == 0)
    return 0;

  for(SmallVector<IVSRange, 4>::iterator it = subVals.begin(), itend = subVals.end();
      it != itend; ++it) {

    if(it->second.isWhollyUnknown())
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

void llvm::getConstSubVal(Constant* FromC, uint64_t Offset, uint64_t TargetSize, Type* TargetType, ImprovedValSet*& Result) {

  SmallVector<IVSRange, 4> subVals;
  getConstSubVals(FromC, Offset, TargetSize, -((int64_t)Offset), subVals);

  if(subVals.size() != 1) {
    if(Constant* C = valsToConst(subVals, TargetSize, TargetType)) {
      std::pair<ValSetType, ImprovedVal> V = getValPB(C);
      ImprovedValSetSingle* NewIVS = newIVS();
      Result = NewIVS;
      NewIVS->set(V.second, V.first);
    }
    else {
      Result = newOverdefIVS();
    }
  }
  else {
    ImprovedValSetSingle* NewIVS = copyIVS(&(subVals[0].second));
    Result = NewIVS;
    if(TargetType)
      NewIVS->coerceToType(TargetType, TargetSize, 0);
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

    if(Size == ULONG_MAX)
      Size = M->AllocSize - Offset;

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

    release_assert(found.start() < found.stop());

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
    release_assert(found.start() < found.stop());

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

  if(S.isWhollyUnknown())
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

  if(S.isWhollyUnknown())
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
    S.isWhollyUnknown() || 
    S.SetType == ValSetTypeScalar || 
    S.SetType == ValSetTypeScalarSplat;
  
}

void llvm::readValRangeMultiFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ImprovedValSet* store, SmallVector<IVSRange, 4>& Results, ImprovedValSet* ignoreBelowStore) {

  if(ignoreBelowStore && ignoreBelowStore == store) {
    LFV3(errs() << "Leaving a gap due to threshold store " << ignoreBelowStore << "\n");
    return;
  }

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(store)) {

    if(IVS->SetType == ValSetTypeDeallocated) {

      // Read from a certainly-freed object yields overdef.
      Results.push_back(IVSR(Offset, Offset+Size, ImprovedValSetSingle(ValSetTypeUnknown, true)));

    }
    else if(Offset == 0 && Size == V.getAllocSize()) {
      
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
	readValRangeMultiFrom(V, Offset, it.start() - Offset, IVM->Underlying, Results, ignoreBelowStore);
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
      readValRangeMultiFrom(V, Offset, Size, IVM->Underlying, Results, ignoreBelowStore);

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

  LocStore* firstStore = ReadBB->getReadableStoreFor(V);
  if(!firstStore) {
    if(ReadBB->localStore->allOthersClobbered) {
      LFV3(errs() << "Location not in local map and allOthersClobbered\n");
      Results.push_back(IVSR(Offset, Offset+Size, ImprovedValSetSingle(ValSetTypeUnknown, true)));
      return;
    }
    else {
      LFV3(errs() << "Starting at base store\n");
      firstStore = &(V.getBaseStore());
    }
  }
  else {
    LFV3(errs() << "Starting at local store\n");
  }

  readValRangeMultiFrom(V, Offset, Size, firstStore->store, Results, 0);

}

void llvm::executeMemcpyInst(ShadowInstruction* MemcpySI) {

  ShadowValue Ptr = MemcpySI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");

  ConstantInt* LengthCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemcpySI->getCallArgOperand(2)));

  ShadowValue SrcPtr = MemcpySI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  release_assert((SrcPtrSet.isWhollyUnknown() || SrcPtrSet.SetType == ValSetTypePB) && "Memcpy from non-pointer value?");

  executeCopyInst(&Ptr, PtrSet, SrcPtrSet, LengthCI ? LengthCI->getLimitedValue() : ULONG_MAX, MemcpySI);

}

void llvm::executeVaCopyInst(ShadowInstruction* SI) {
  
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");
  
  ShadowValue SrcPtr = SI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  release_assert((SrcPtrSet.isWhollyUnknown() || SrcPtrSet.SetType == ValSetTypePB) && "Memcpy from non-pointer value?");
  
  executeCopyInst(&Ptr, PtrSet, SrcPtrSet, 24, SI);

}

void llvm::executeAllocInst(ShadowInstruction* SI, Type* AllocType, uint64_t AllocSize, bool trackAlloc) {

  // Represent the store by a big undef value at the start, or if !AllocType (implying AllocSize
  // == ULONG_MAX, unknown size), start with a big Overdef.
  release_assert((!SI->store.store) && "Allocation already initialised?");

  ImprovedValSetSingle* initVal;

  if(AllocType) {
    Constant* Undef = UndefValue::get(AllocType);
    ImprovedVal IV(ShadowValue(Undef), 0);
    initVal = new ImprovedValSetSingle(IV, ValSetTypeScalar);
  }
  else {
    initVal = new ImprovedValSetSingle(ValSetTypeUnknown, true);
  }

  if(trackAlloc) {

    // malloc and realloc instructions should also be inserted into the path store,
    // as a flag that the allocation exists here. Their baseStore should be deallocated,
    // to indicate that on other paths the object does not exist.

    SI->store.store = new ImprovedValSetSingle(ValSetTypeDeallocated, false);
   
    ShadowValue AllocSV(SI);
    LocStore& localStore = SI->parent->getWritableStoreFor(AllocSV, 0, AllocSize, /* willWriteSingle = */ true);
    localStore.store->dropReference();
    localStore.store = initVal;

  }
  else {

    SI->store.store = initVal;

  }

  SI->storeSize = AllocSize;

  // Note new object current thread-local and cannot alias old objects.
  SI->parent->localStore = SI->parent->localStore->getWritableFrameList();
  SI->parent->localStore->noAliasOldObjects.insert(ShadowValue(SI));
  SI->parent->localStore->threadLocalObjects.insert(ShadowValue(SI));

  ImprovedValSetSingle* NewIVS = newIVS();
  SI->i.PB = NewIVS;
  NewIVS->set(ImprovedVal(SI, 0), ValSetTypePB);

}

void llvm::executeAllocaInst(ShadowInstruction* SI) {

  // If the store is already initialised this must represent the general case of an allocation
  // within a loop or recursive call.
  if(SI->store.store)
    return;

  AllocaInst* AI = cast_inst<AllocaInst>(SI);
  Type* allocType = AI->getAllocatedType();

  InlineAttempt* parentIA = SI->parent->IA->getFunctionRoot();
  SI->allocIdx = parentIA->localAllocas.size();
  parentIA->localAllocas.push_back(SI);
 
  if(AI->isArrayAllocation()) {

    ConstantInt* N = cast_or_null<ConstantInt>(getConstReplacement(AI->getArraySize()));
    if(!N) 
     allocType = 0;
    else
      allocType = ArrayType::get(allocType, N->getLimitedValue());

  }

  executeAllocInst(SI, allocType, allocType ? GlobalAA->getTypeStoreSize(allocType) : ULONG_MAX, false);

}

void llvm::addHeapAlloc(ShadowInstruction* SI) {

  SI->allocIdx = GlobalIHP->heap.size();
  GlobalIHP->heap.push_back(ShadowValue(SI));

}

void llvm::executeMallocInst(ShadowInstruction* SI) {

  if(SI->store.store)
    return;

  ConstantInt* AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(0)));
  Type* allocType = 0;
  if(AllocSize)
    allocType = ArrayType::get(Type::getInt8Ty(SI->invar->I->getContext()), AllocSize->getLimitedValue());

  if(!SI->store.store)
    SI->parent->IA->noteMalloc(SI);

  addHeapAlloc(SI);
  executeAllocInst(SI, allocType, AllocSize ? AllocSize->getLimitedValue() : ULONG_MAX, true);

}

void llvm::executeFreeInst(ShadowInstruction* SI) {

  ShadowInstruction* FreedPtr = SI->getCallArgOperand(0).getInst();
  if(!FreedPtr)
    return;

  ImprovedValSetSingle* FreedIVS = dyn_cast_or_null<ImprovedValSetSingle>(FreedPtr->i.PB);
  if(!FreedIVS)
    return;

  if(FreedIVS->SetType != ValSetTypePB)
    return;

  if(FreedIVS->Values.size() != 1)
    return;

  ImprovedValSetSingle TagIVS;
  TagIVS.SetType = ValSetTypeDeallocated;

  executeWriteInst(0, *FreedIVS, TagIVS, FreedIVS->Values[0].V.getAllocSize(), SI);

}

void llvm::executeReallocInst(ShadowInstruction* SI) {

  if(!SI->store.store) {

    // Only alloc the first time; always carry out the copy implied by realloc.
    ConstantInt* AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(0)));
    Type* allocType = 0;
    if(AllocSize)
      allocType = ArrayType::get(Type::getInt8Ty(SI->invar->I->getContext()), AllocSize->getLimitedValue());

    SI->parent->IA->noteMalloc(SI);

    addHeapAlloc(SI);
    executeAllocInst(SI, allocType, AllocSize ? AllocSize->getLimitedValue() : ULONG_MAX, true);

  }

  ShadowValue SrcPtr = SI->getCallArgOperand(0);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Realloc from uninitialised PB?");
  release_assert((SrcPtrSet.isWhollyUnknown() || SrcPtrSet.SetType == ValSetTypePB) && "Realloc non-pointer-typed value?");
  uint64_t CopySize = ULONG_MAX;

  if(SrcPtrSet.isWhollyUnknown() || SrcPtrSet.Values.size() > 1) {

    // Overdef the realloc.
    SrcPtrSet.setOverdef();

  }
  else {

    CopySize = SrcPtrSet.Values[0].V.getAllocSize();

  }

  ImprovedValSetSingle ThisInst = ImprovedValSetSingle(ImprovedVal(ShadowValue(SI), 0), ValSetTypePB);

  executeCopyInst(0, ThisInst, SrcPtrSet, CopySize, SI);
  // Release the realloc'd location.
  executeFreeInst(SI);

}

/*
static void checkStore(ImprovedValSet* IV, ShadowValue& V) {

  if(IV->isMulti) {

    ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(IV);

    release_assert(!IVM->Map.empty());

    uint64_t size = V.getAllocSize();
    uint64_t covered = 0;
    uint64_t lastOffset = 0;
    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {
      release_assert(it.start() >= lastOffset);
      lastOffset = it.stop();
      release_assert(it.start() <= it.stop());
      covered += (it.stop() - it.start());
    }

    release_assert(covered == size || IVM->Underlying);

  }

}
*/

static void checkStore(ImprovedValSet* IV, ShadowValue&) { }

void llvm::writeExtents(SmallVector<IVSRange, 4>& copyValues, ShadowValue& Ptr, int64_t Offset, uint64_t Size, ShadowBB* BB) {

  LocStore& Store = BB->getWritableStoreFor(Ptr, Offset, Size, copyValues.size() == 1);
  replaceRangeWithPBs(Store.store, copyValues, (uint64_t)Offset, Size);
  checkStore(Store.store, Ptr);


}

void llvm::executeCopyInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& SrcPtrSet, uint64_t Size, ShadowInstruction* CopySI) {

  ShadowBB* BB = CopySI->parent;

  LFV3(errs() << "Start copy inst\n");

  if(Size == ULONG_MAX || PtrSet.isWhollyUnknown() || PtrSet.Values.size() != 1 || SrcPtrSet.isWhollyUnknown() || SrcPtrSet.Values.size() != 1) {

    // Only support memcpy from single pointer to single pointer for the time being:
    // If we're known to be copying scalars, note that in our overdef to prevent unnecessary clobbers.
    
    ImprovedValSetSingle OD(ValSetTypePB, true);

    if(!SrcPtrSet.isWhollyUnknown()) {
      
      bool foundPointers = false;
      for(uint32_t i = 0; i < SrcPtrSet.Values.size() && !foundPointers; ++i) {

	ShadowValue Obj = SrcPtrSet.Values[i].V;
	ShadowGV* G = Obj.getGV();
	if(G && G->G->isConstant()) {

	  // Pointer to a constant. See if the pointed object itself has pointers:
	  if(containsPointerTypes(G->G->getInitializer()->getType()))
	    foundPointers = true;
	  
	}
	else {

	  LocStore* store = BB->getReadableStoreFor(Obj);
	  if(!store)
	    store = &Obj.getBaseStore();
	  if(mayContainPointers(store->store))
	    foundPointers = true;

	}
	
      }

      if(!foundPointers)
	OD.SetType = ValSetTypeScalar;

    }

    executeWriteInst(Ptr, PtrSet, OD, Size, CopySI);
    return;

  }

  if(val_is<ConstantPointerNull>(SrcPtrSet.Values[0].V))
    return;

  if(val_is<ConstantPointerNull>(PtrSet.Values[0].V))
    return;

  // Now dependent on the source location's value.
  BB->IA->noteDependency(SrcPtrSet.Values[0].V);

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
  writeExtents(copyValues, PtrSet.Values[0].V, PtrSet.Values[0].Offset, Size, BB);

  for(SmallVector<IVSRange, 4>::iterator it = copyValues.begin(),
	itend = copyValues.end(); it != itend; ++it) {

    propagateStoreFlags(PtrSet, it->second, BB);

  }

}

void PeelIteration::applyMemoryPathConditions(ShadowBB* BB) {
  
  return;

}

void InlineAttempt::applyMemoryPathConditions(ShadowBB* BB) {

  if(!isRootMainCall())
    return;

  for(std::vector<PathCondition>::iterator it = pass->rootStringPathConditions.begin(),
	itend = pass->rootStringPathConditions.end(); it != itend; ++it) {

    if(it->fromBlockIdx == BB->invar->idx) {

      ShadowBB* ptrBB = getBB(it->instBlockIdx);
      if(!ptrBB)
	continue;

      ShadowInstruction* ptr = &(ptrBB->insts[it->instIdx]);
      ShadowValue ptrSV(ptr);
      ImprovedValSetSingle* ptrIVS = dyn_cast<ImprovedValSetSingle>(ptr->i.PB);

      GlobalVariable* GV = cast<GlobalVariable>(it->val);
      ConstantDataArray* CDA = cast<ConstantDataArray>(GV->getInitializer());
      uint32_t Size = CDA->getNumElements();

      ShadowGV* SGV = &(pass->shadowGlobals[pass->getShadowGlobalIndex(GV)]);
      
      ImprovedValSetSingle copyFromPointer;
      copyFromPointer.set(ImprovedVal(SGV, 0), ValSetTypePB);

      // Attribute the effect of the write to first instruction in block:
      executeCopyInst(&ptrSV, *ptrIVS, copyFromPointer, Size, &(BB->insts[0]));

    }

  }

}

void llvm::executeVaStartInst(ShadowInstruction* SI) {

  LFV3(errs() << "Start va_start inst\n");

  ShadowBB* BB = SI->parent;
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;

  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  release_assert((PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value?");

  if(PtrSet.isWhollyUnknown() || PtrSet.Values.size() > 1) {

    // va_start writes pointers.
    ImprovedValSetSingle OD(ValSetTypePB, true);
    executeWriteInst(&Ptr, PtrSet, OD, 24, SI);
    return;

  }

  SmallVector<IVSRange, 4> vaStartVals;
  ImprovedValSetSingle nonFPOffset = ImprovedValSetSingle(ImprovedVal(ShadowValue(SI), ImprovedVal::first_nonfp_arg), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(0, 4, nonFPOffset));

  ImprovedValSetSingle FPOffset = ImprovedValSetSingle(ImprovedVal(ShadowValue(SI), ImprovedVal::first_fp_arg), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(4, 8, FPOffset));

  ImprovedValSetSingle AnyPtr = ImprovedValSetSingle(ImprovedVal(ShadowValue(SI), ImprovedVal::first_any_arg), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(8, 16, AnyPtr));
  
  ImprovedValSetSingle StackBase = ImprovedValSetSingle(ImprovedVal(ShadowValue(SI), ImprovedVal::va_baseptr), ValSetTypeVarArg);
  vaStartVals.push_back(IVSR(16, 24, StackBase));

  LocStore& Store = BB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, 24, false);
  replaceRangeWithPBs(Store.store, vaStartVals, (uint64_t)PtrSet.Values[0].Offset, 24);
  checkStore(Store.store, PtrSet.Values[0].V);

}

void llvm::executeReadInst(ShadowInstruction* ReadSI, OpenStatus& OS, uint64_t FileOffset, uint64_t Size) {

  LFV3(errs() << "Start read inst\n");

  ShadowValue Ptr = ReadSI->getCallArgOperand(1);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB (read)?");
  release_assert((PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB) && "Write through non-pointer-typed value (read)?");

  ImprovedValSetSingle WriteIVS;
  
  if(PtrSet.isWhollyUnknown() || PtrSet.Values.size() != 1) {

    WriteIVS.setOverdef();

  }
  else {

    std::vector<Constant*> constBytes;
    std::string errors;
    LLVMContext& Context = Ptr.getLLVMContext();
    if(getFileBytes(OS.Name, FileOffset, Size, constBytes, Context,  errors)) {
      ArrayType* ArrType = ArrayType::get(IntegerType::get(Context, 8), constBytes.size());
      Constant* ByteArray = ConstantArray::get(ArrType, constBytes);
      WriteIVS = ImprovedValSetSingle(ImprovedVal(ByteArray, 0), ValSetTypeScalar);
    }

  }

  executeWriteInst(&Ptr, PtrSet, WriteIVS, Size, ReadSI);

}

enum specialfunctions {

  SF_MALLOC,
  SF_REALLOC,
  SF_FREE,
  SF_VASTART,
  SF_VACOPY

};

static DenseMap<Function*, specialfunctions> SpecialFunctionMap;

void llvm::initSpecialFunctionsMap(Module& M) {

  if(Function* F1 = M.getFunction("malloc"))
    SpecialFunctionMap[F1] = SF_MALLOC;  
  if(Function* F2 = M.getFunction("realloc"))
    SpecialFunctionMap[F2] = SF_REALLOC;
  if(Function* F3 = M.getFunction("free"))
    SpecialFunctionMap[F3] = SF_FREE;
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

    {
      DenseMap<Function*, specialfunctions>::iterator it = SpecialFunctionMap.find(F);
      if(it != SpecialFunctionMap.end()) {
      
	switch(it->second) {
	
	case SF_MALLOC:
	  executeMallocInst(SI);
	  break;
	case SF_REALLOC:
	  executeReallocInst(SI);
	  break;
	case SF_FREE:
	  executeFreeInst(SI);
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
    }

    // Try to spot a special location:
    {
      SmallDenseMap<Function*, SpecialLocationDescriptor>::iterator it = GlobalIHP->specialLocations.find(F);
      if(it != GlobalIHP->specialLocations.end()) {

	if(!SI->i.PB) {
	  ImprovedValSetSingle* init = newIVS();
	  init->SetType = ValSetTypePB;
	  init->Values.push_back(ImprovedVal(ShadowValue(F), 0));
	  SI->i.PB = init;
	}

	return;

      }
    }

    // All unannotated calls return an unknown value:
    if(SI->i.PB)
      deleteIV(SI->i.PB);
    SI->i.PB = newOverdefIVS();

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
	// All currently annotated syscalls write scalar values.
	ImprovedValSetSingle OD(ValSetTypeScalar, true);
	executeWriteInst(&ClobberV, ClobberSet, OD, ClobberSize, SI);

      }

      if(GlobalIHP->yieldFunctions.count(F))
	SI->parent->clobberGlobalObjects();

      return;

    }

  }
  else {

    // Unknown calls return unknown
    if(SI->i.PB)
      deleteIV(SI->i.PB);
    SI->i.PB = newOverdefIVS();

  }

  // Finally clobber all locations; this call is entirely unhandled
  //errs() << "Warning: unhandled call to " << itcache(SI) << " clobbers all locations\n";
  ImprovedValSetSingle OD(ValSetTypeUnknown, true);
  executeWriteInst(0, OD, OD, AliasAnalysis::UnknownSize, SI);

}

static bool containsOldObjects(ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(Ptr.SetType != ValSetTypePB)
    return false;

  for(uint32_t i = 0, ilim = Ptr.Values.size(); i != ilim; ++i) {

    if(!BB->localStore->noAliasOldObjects.count(Ptr.Values[i].V))    
      return true;

  }

  return false;

}

static bool containsGlobalObjects(ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(Ptr.SetType != ValSetTypePB)
    return false;

  for(uint32_t i = 0, ilim = Ptr.Values.size(); i != ilim; ++i) {

    if(!BB->localStore->threadLocalObjects.count(Ptr.Values[i].V))
      return true;
    
  }
  
  return false;

}

struct ReachableObjectVisitor {

  SmallSet<ShadowValue, 8> seenObjects;

  virtual void visitPtr(ImprovedValSetSingle& Ptr, ShadowBB* BB) { }
  virtual bool visitObject(ShadowValue& Obj, ShadowBB* BB) { return true; }
  virtual bool shouldContinue() { return true; }

};

static void visitReachableObjects(ImprovedValSetSingle& Ptr, ShadowBB* BB, ReachableObjectVisitor& V);

static void visitReachableObjects(ImprovedValSet* Obj, ShadowBB* BB, ReachableObjectVisitor& V) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(Obj)) {

    visitReachableObjects(*IVS, BB, V);

  }
  else {

    ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(Obj);
    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {

      visitReachableObjects(it.val(), BB, V);

    }

  }

}

static void visitReachableObjects(ImprovedValSetSingle& Ptr, ShadowBB* BB, ReachableObjectVisitor& V) {

  V.visitPtr(Ptr, BB);
  if(!V.shouldContinue())
    return;

  if(Ptr.isWhollyUnknown() || Ptr.SetType != ValSetTypePB)
    return;

  for(uint32_t i = 0, ilim = Ptr.Values.size(); i != ilim; ++i) {

    ShadowValue& ThisPtr = Ptr.Values[i].V;

    switch(ThisPtr.t) {
    case SHADOWVAL_GV:
      if(ThisPtr.u.GV->G->isConstant())
	continue;
      break;
    case SHADOWVAL_OTHER:
      release_assert(isa<ConstantPointerNull>(ThisPtr.u.V));
      continue;
    default:
      break;
    }

    if(!V.seenObjects.insert(Ptr.Values[i].V))
      continue;

    if(!V.visitObject(Ptr.Values[i].V, BB))
      continue;

    LocStore* store = BB->getReadableStoreFor(Ptr.Values[i].V);
    if(!store)
      store = &Ptr.Values[i].V.getBaseStore();
    visitReachableObjects(store->store, BB, V);

  }

}

struct ReachesAllPointersVisitor : public ReachableObjectVisitor {

  bool mayReachAll;
  bool ignoreOldObjects;
  ReachesAllPointersVisitor(bool ignoreOld) : mayReachAll(false), ignoreOldObjects(ignoreOld) { }

  virtual void visitPtr(ImprovedValSetSingle& Ptr, ShadowBB* BB) {

    if(Ptr.isWhollyUnknown()) {
      if((!ignoreOldObjects) || !Ptr.isOldValue())
	mayReachAll = true;
    }

  }

  virtual bool shouldContinue() {   
    return !mayReachAll;
  }

};

static bool reachesAllPointers(ImprovedValSetSingle& Ptr, ShadowBB* BB, bool ignoreOldObjects) {

  ReachesAllPointersVisitor V(ignoreOldObjects);
  visitReachableObjects(Ptr, BB, V);
  return V.mayReachAll;

}

struct SetMAOVisitor : public ReachableObjectVisitor {

  virtual bool visitObject(ShadowValue& Obj, ShadowBB* BB) { 

    // Don't explore objects reachable this way, it's already known MAO
    if(!BB->localStore->noAliasOldObjects.count(Obj))
      return false;

    BB->localStore = BB->localStore->getWritableFrameList();
    BB->localStore->noAliasOldObjects.erase(Obj);

    return true;

  }

};

void ShadowBB::setAllObjectsMayAliasOld() {

  localStore = localStore->getWritableFrameList();
  localStore->noAliasOldObjects.clear();

}

static void setObjectsMayAliasOld(ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(reachesAllPointers(Ptr, BB, true)) {
    BB->setAllObjectsMayAliasOld();
    return;
  }
  
  SetMAOVisitor V;
  visitReachableObjects(Ptr, BB, V);

}

struct SetTGVisitor : public ReachableObjectVisitor {

  virtual bool visitObject(ShadowValue& Obj, ShadowBB* BB) { 

    // Don't explore objects reachable this way
    if(!BB->localStore->threadLocalObjects.count(Obj))
      return false;
    
    BB->localStore = BB->localStore->getWritableFrameList();
    BB->localStore->threadLocalObjects.erase(Obj);

    return true;

  }

};

void ShadowBB::setAllObjectsThreadGlobal() {

  localStore = localStore->getWritableFrameList();
  localStore->threadLocalObjects.clear();

}

static void setObjectsThreadGlobal(ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(reachesAllPointers(Ptr, BB, false)) {
    BB->setAllObjectsThreadGlobal();
    return;
  }
  
  SetTGVisitor V;
  visitReachableObjects(Ptr, BB, V);

}

void ShadowBB::clobberAllExcept(DenseSet<ShadowValue>& Save, bool verbose) {

  std::vector<std::pair<ShadowValue, ImprovedValSet*> > SaveVals;

  for(DenseSet<ShadowValue>::iterator it = Save.begin(), itend = Save.end(); it != itend; ++it) {

    LocStore* CurrentVal = getReadableStoreFor(*it);
    if(!CurrentVal)
      CurrentVal = &it->getBaseStore();
    SaveVals.push_back(std::make_pair(*it, CurrentVal->store->getReadableCopy()));
    if(verbose)
      errs() << "Sparing " << itcache(*it) << "\n";
    
  }

  localStore = localStore->getEmptyMap();
  localStore->allOthersClobbered = true;

  for(std::vector<std::pair<ShadowValue, ImprovedValSet*> >::iterator it = SaveVals.begin(),
	itend = SaveVals.end(); it != itend; ++it) {
    
    bool isNew;
    LocStore* newStore = getOrCreateStoreFor(it->first, &isNew);
    release_assert(isNew);

    newStore->store = it->second;

  }

}

void ShadowBB::clobberMayAliasOldObjects() {

  bool verbose = false;
  if(verbose)
    errs() << "Clobber old objects " << invar->BB->getName() << ":\n";
  clobberAllExcept(localStore->noAliasOldObjects, verbose);
  if(verbose)
    errs() << "---\n\n";

}

void ShadowBB::clobberGlobalObjects() {
  
  bool verbose = false;
  if(verbose)
    errs() << "Clobber global objects at " << invar->BB->getName() << ":\n";
  clobberAllExcept(localStore->threadLocalObjects, verbose);
  if(verbose)
    errs() << "---\n\n";
  
}

void llvm::noteBarrierInst(ShadowInstruction* SI) {

  GlobalIHP->barrierInstructions.insert(SI);
  SI->parent->IA->barrierState = BARRIER_HERE;

}

bool IntegrationAttempt::noteChildBarriers() {

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    if(it->second->noteChildBarriers() && barrierState == BARRIER_NONE)
      barrierState = BARRIER_CHILD;

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    if(!it->second->isTerminated())
      continue;

    for(std::vector<PeelIteration*>::iterator iterit = it->second->Iterations.begin(),
	  iterend = it->second->Iterations.end(); iterit != iterend; ++iterit) {

      if((*iterit)->noteChildBarriers() && barrierState == BARRIER_NONE)
	barrierState = BARRIER_CHILD;

    }

  }

  return barrierState != BARRIER_NONE;

}

void llvm::executeWriteInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, uint64_t PtrSize, ShadowInstruction* WriteSI) {

  ShadowBB* StoreBB = WriteSI->parent;

  if(!ValPB.isInitialised())
    ValPB.setOverdef();

  // Perform the store

  if(PtrSet.isWhollyUnknown()) {
    
    if(Ptr && GlobalIHP->useDSA) {

      DSGraph* DSG = 0;

      switch(Ptr->t) {
      case SHADOWVAL_ARG:
      case SHADOWVAL_INST:
	{
	  const Function& PtrF = Ptr->getCtx()->F;
	  if(GlobalDSA->hasDSGraph(PtrF))
	    DSG = GlobalDSA->getDSGraph(PtrF);
	  break;
	}
      case SHADOWVAL_GV:
	DSG = GlobalDSA->getGlobalsGraph();
	break;
      default:
	break;
      }

      if(DSG) {

	Value* PtrV = Ptr->getBareVal();
	if(DSG->hasNodeForValue(PtrV)) {

	  DSNode* Node = DSG->getNodeForValue(PtrV).getNode();
	  if(Node) {

	    errs() << "Found node for " << itcache(PtrV) << " (" << Node->isCompleteNode() << ")\n";

	  }

	}

      }

    }

    if(PtrSet.isOldValue()) {

      StoreBB->clobberMayAliasOldObjects();

    }
    else {
      
      // Start with a plain local store map giving no locations.
      // getEmptyMap clears the map if it's writable or makes a new blank one otherwise.
      noteBarrierInst(WriteSI);
      StoreBB->localStore = StoreBB->localStore->getEmptyMap();
      StoreBB->localStore->allOthersClobbered = true;
      LFV3(errs() << "Write through overdef; local map " << StoreBB->localStore << " clobbered\n");

    }

  }
  else if(PtrSet.Values.size() == 1 && PtrSet.Values[0].Offset != LLONG_MAX) {

    LFV3(errs() << "Write through certain pointer\n");
    // Best case: store through a single, certain pointer. Overwrite the location with our new PB.

    if(val_is<ConstantPointerNull>(PtrSet.Values[0].V))
      return;

    LocStore& Store = StoreBB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, PtrSize, true);
    replaceRangeWithPB(Store.store, ValPB, (uint64_t)PtrSet.Values[0].Offset, PtrSize);

    checkStore(Store.store, PtrSet.Values[0].V);

  }
  else {

    for(SmallVector<ImprovedVal, 1>::iterator it = PtrSet.Values.begin(), it2 = PtrSet.Values.end(); it != it2; ++it) {

      if(val_is<ConstantPointerNull>(it->V))
	continue;

      if(it->Offset == LLONG_MAX) {
	LFV3(errs() << "Write through vague pointer; clobber\n");
	LocStore& Store = StoreBB->getWritableStoreFor(it->V, 0, ULONG_MAX, true);
	ImprovedValSetSingle OD(ValSetTypeUnknown, true);
	replaceRangeWithPB(Store.store, OD, 0, ULONG_MAX);

	checkStore(Store.store, it->V);

      }
      else {

	ImprovedValSetSingle oldValSet;
	if(ValPB.Overdef) {

	  // Overdef merges with any other value to make Overdef, so skip the lookup.
	  oldValSet = ValPB;

	}
	else {

	  LFV3(errs() << "Write through maybe pointer; merge\n");
	  readValRange(it->V, (uint64_t)it->Offset, PtrSize, StoreBB, oldValSet, 0, 0);

	  if((!oldValSet.isWhollyUnknown()) && oldValSet.isInitialised()) {

	    if(!ValPB.coerceToType(oldValSet.Values[0].V.getType(), PtrSize, 0)) {
	      LFV3(errs() << "Read-modify-write failure coercing to type " << (*oldValSet.Values[0].V.getType()) << "\n");
	    }

	  }

	  oldValSet.merge(ValPB);

	}

	LocStore& Store = StoreBB->getWritableStoreFor(it->V, it->Offset, PtrSize, true);
	replaceRangeWithPB(Store.store, oldValSet, (uint64_t)it->Offset, PtrSize);

	checkStore(Store.store, it->V);

      }

    }

  }

  propagateStoreFlags(PtrSet, ValPB, StoreBB);

}

void llvm::propagateStoreFlags(ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, ShadowBB* StoreBB)  {

  // Propagate is-thread-local and may-alias-old-objects information

  bool targetMayAliasOld = PtrSet.isWhollyUnknown() || containsOldObjects(PtrSet, StoreBB);
  bool targetIsThreadGlobal = PtrSet.isWhollyUnknown() || containsGlobalObjects(PtrSet, StoreBB);

  if(ValPB.isWhollyUnknown()) {

    // If we know the value is a non-pointer, this has no effect.
    if(ValPB.SetType == ValSetTypeScalar)
      return;

    if(targetMayAliasOld && !ValPB.isOldValue())
      StoreBB->setAllObjectsMayAliasOld();
    if(targetIsThreadGlobal)
      StoreBB->setAllObjectsThreadGlobal();

  }
  else {

    // Apply alias-old or global flags to any objects whose pointers are written in,
    // and any objects recursively reachable from their (current) values.

    if(targetMayAliasOld)
      setObjectsMayAliasOld(ValPB, StoreBB);
    if(targetIsThreadGlobal)
      setObjectsThreadGlobal(ValPB, StoreBB);

  }

}

void SharedStoreMap::clear() {

  release_assert(refCount <= 1 && "clear() against shared map?");

  // Drop references to any maps this points to;
  for(std::vector<LocStore>::iterator it = store.begin(), itend = store.end(); it != itend; ++it) {
    if(!it->store)
      continue;
    LFV3(errs() << "Drop ref to " << it->store << "\n");
    it->store->dropReference();
  }

  store.clear();
  store.resize(IA->invarInfo->frameSize);
  empty = true;

}

void SharedTreeNode::dropReference(uint32_t height) {

  if(!--refCount) {

    LFV3(errs() << "Freeing node " << this << "\n");

    // This node goes away! Drop our children.
    if(height == 0) {

      for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
	if(children[i]) {
	  LocStore* child = ((LocStore*)children[i]);
	  child->store->dropReference();
	  delete child;
	}
      }

    }
    else {

      for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {
	if(children[i])
	  ((SharedTreeNode*)children[i])->dropReference(height - 1);
      }

    }

    delete this;

  }

}

void SharedTreeRoot::clear() {

  if(height == 0)
    return;
  root->dropReference(height - 1);
  root = 0;
  height = 0;

}

void SharedTreeRoot::dropReference() {

  clear();

}

SharedStoreMap* SharedStoreMap::getEmptyMap() {

  if(!store.size())
    return this;
  else if(refCount == 1) {
    clear();
    return this;
  }
  else {
    dropReference();
    return new SharedStoreMap(IA, store.size());
  }

}

void LocalStoreMap::clear() {

  heap.clear();
  for(uint32_t i = 0; i < frames.size(); ++i)
    frames[i] = frames[i]->getEmptyMap();

}

bool LocalStoreMap::empty() {

  if(heap.height != 0)
    return false;

  for(uint32_t i = 0; i < frames.size(); ++i) {
    if(!frames[i]->empty)
      return false;
  }

  return true;

}

LocalStoreMap* LocalStoreMap::getEmptyMap() {

  if(empty())
    return this;
  else if(refCount == 1) {
    clear();
    return this;
  }
  else {
    // Can't free the map (refcount > 1)
    --refCount;
    LocalStoreMap* newMap = new LocalStoreMap(frames.size());
    newMap->copyEmptyFrames(frames);
    return newMap;
  }

}

void LocalStoreMap::copyEmptyFrames(SmallVector<SharedStoreMap*, 4>& copyFrom) {

  // Heap starts in empty state.
  // Copy metadata per frame but don't populate any objects.
  for(uint32_t i = 0; i < frames.size(); ++i)
    frames[i] = new SharedStoreMap(copyFrom[i]->IA, copyFrom[i]->IA->invarInfo->frameSize);

}

void LocalStoreMap::copyFramesFrom(const LocalStoreMap& other) {

  // Frames array already allocated. Borrow all the other side's frames.

  heap = other.heap;
  if(heap.root)
    heap.root->refCount++;

  for(uint32_t i = 0; i < frames.size(); ++i) {

    frames[i] = other.frames[i];
    frames[i]->refCount++;

  }
  
  threadLocalObjects = other.threadLocalObjects;
  noAliasOldObjects = other.noAliasOldObjects;

}

void SharedStoreMap::dropReference() {

  if(!--refCount) {

    LFV3(errs() << "Local map " << this << " freed\n");
    clear();

    delete this;

  }
  else {

    LFV3(errs() << "Local map " << this << " refcount down to " << refCount << "\n");

  }

}

void LocalStoreMap::dropReference() {

  if(!--refCount) {

    LFV3(errs() << "Local map " << this << " freed\n");
    heap.dropReference();
    for(uint32_t i = 0; i < frames.size(); ++i)
      frames[i]->dropReference();

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

void MergeBlockVisitor::mergeValues(ImprovedValSetSingle& consumeVal, ImprovedValSetSingle& otherVal) {

  if(useVarargMerge && 
     consumeVal.SetType == ValSetTypeVarArg && 
     otherVal.SetType == ValSetTypeVarArg && 
     consumeVal.Values.size() == 1 && 
     otherVal.Values.size() == 1) {

    if(otherVal.Values[0].Offset > consumeVal.Values[0].Offset)
      consumeVal = otherVal;

  }
  else {
		
    consumeVal.merge(otherVal);

  }

}

void MergeBlockVisitor::mergeStores(LocStore* mergeFromStore, LocStore* mergeToStore, ShadowValue& MergeV) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(mergeToStore->store)) {

    LFV3(errs() << "Merge in store " << mergeFromStore << " -> " << mergeToStore << "\n");

    if(IVS->Overdef) {
      LFV3(errs() << "Target already clobbered\n");
      return;
    }

    // Deallocated is always overridden by a definition from the other side.
    if(IVS->SetType == ValSetTypeDeallocated) {
      mergeToStore->store->dropReference();
      mergeToStore->store = mergeFromStore->store->getReadableCopy();
      return;
    }

    if(ImprovedValSetSingle* IVS2 = dyn_cast<ImprovedValSetSingle>(mergeFromStore->store)) {
      LFV3(errs() << "Merge in another single\n");
      IVS->merge(*IVS2);
      return;
    }

  }

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(mergeFromStore->store)) {

    // Deallocated yields to existing definition.
    if(IVS->SetType == ValSetTypeDeallocated)
      return;

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

    readValRangeMultiFrom(MergeV, 0, TotalBytes, mergeToStore->store, LHSVals, LHSAncestor);
    readValRangeMultiFrom(MergeV, 0, TotalBytes, mergeFromStore->store, RHSVals, RHSAncestor);
	  
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
		
	LFV3(errs() << "Gap " << LastOffset << "-" << consumeit->first.first << "\n");
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
	readValRangeMultiFrom(MergeV, LastOffset, stopAt - LastOffset, LHSAncestor, baseVals, 0);
		
	for(SmallVector<IVSRange, 4>::iterator baseit = baseVals.begin(), baseend = baseVals.end();
	    baseit != baseend; ++baseit) {

	  ImprovedValSetSingle subVal;
	  getIVSSubVal(consumeit->second, baseit->first.first - consumeit->first.first, baseit->first.second - baseit->first.first, subVal);
	  mergeValues(subVal, baseit->second);
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

	mergeValues(consumeVal, otherVal);
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

    // Gap at the RHS?
    if((LHSVals.empty() || LHSVals.back().first.second != TotalBytes) &&
       (RHSVals.empty() || RHSVals.back().first.second != TotalBytes))
      anyGaps = true;

    if(anyGaps) {
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

static bool derefLT(void** a, void** b) {
  if(!a)
    return !!b;
  else if(!b)
    return false;
  else
    return *a < *b;
}

static bool derefEQ(void** a, void** b) {

  if(!a)
    return !b;
  else if(!b)
    return false;
  else
    return (*a == *b);

}

static bool storeVLT(void** a, void** b) {
  if(!a)
    return !!b;
  else if(!b)
    return false;
  else
    return ((LocStore*)*a)->store < ((LocStore*)*b)->store;
}

static bool storeVEQ(void** a, void** b) {

  if(!a)
    return !b;
  else if(!b)
    return false;
  else
    return (((LocStore*)*a)->store == ((LocStore*)*b)->store);

}

void SharedTreeNode::mergeHeaps(SmallVector<SharedTreeNode*, 4>& others, bool allOthersClobbered, uint32_t height, uint32_t idx, MergeBlockVisitor* visitor) {

  // All members of others are known to differ from this node. This node is writable already.
  // Like the frames case, merge in base objects when objects are missing from this or the other tree
  // if !allOthersClobbered; otherwise intersect the trees.
  // Note the special case that others might contain a null pointer, which describes the empty tree.

  if(allOthersClobbered) {

    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      for(SmallVector<SharedTreeNode*, 4>::iterator it = others.begin(), itend = others.end();
	  it != itend && children[i]; ++it) {

	if((!*it) || !((*it)->children[i])) {

	  if(height == 0)
	    delete ((LocStore*)children[i]);
	  else
	    ((SharedTreeNode*)children[i])->dropReference(height - 1);
	  children[i] = 0;

	}

      }

    }

  }
  else {

    // Populate this node with base versions of nodes that are missing but present in any other tree. 
    // Just add blank nodes for now and then the recursion will catch the rest.
    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      for(SmallVector<SharedTreeNode*, 4>::iterator it = others.begin(), itend = others.end();
	  it != itend && !children[i]; ++it) {

	if((*it) && (*it)->children[i]) {

	  if(height == 0)
	    children[i] = getAllocWithIdx(idx + i).getBaseStore().getReadableCopy();
	  else
	    children[i] = new SharedTreeNode();

	}

      }

    }

  }

  // OK now merge each child that exists according to the same rules.

  for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

    if(!children[i])
      continue;

    // Unique children regardless of whether they're further levels of TreeNode
    // or ImprovedValSets. In the former case this avoids merges of identical subtrees
    // in the latter it skips merging ValSetMultis that are shared.
    // In either case refcounting is caught up when unused maps are released at the top level.
    SmallVector<void**, 4> incomingPtrs;
    incomingPtrs.reserve(std::distance(others.begin(), others.end()) + 1);

    incomingPtrs.push_back(&(children[i]));

    for(SmallVector<SharedTreeNode*, 4>::iterator it = others.begin(), itend = others.end();
	it != itend; ++it) {

      if((!*it) || !(*it)->children[i])
	incomingPtrs.push_back(0);
      else
	incomingPtrs.push_back(&((*it)->children[i]));

    }

    if(height == 0) {

      std::sort(incomingPtrs.begin(), incomingPtrs.end(), storeVLT);
      SmallVector<void**, 4>::iterator uniqend = std::unique(incomingPtrs.begin(), incomingPtrs.end(), storeVEQ);
      
      // This subtree never differs?
      if(std::distance(incomingPtrs.begin(), uniqend) == 1)
	continue;

      // Merge each child value.
      for(SmallVector<void**, 4>::iterator it = incomingPtrs.begin(); it != uniqend; ++it) {
	
	if(*it == &(children[i]))
	  continue;

	ShadowValue& MergeV = getAllocWithIdx(idx + i);

	LocStore* mergeFromStore;
	if(!*it)
	  mergeFromStore = &(MergeV.getBaseStore());
	else
	  mergeFromStore = (LocStore*)(**it);

	// mergeStores takes care of CoW break if necessary.
	visitor->mergeStores(mergeFromStore, (LocStore*)children[i], MergeV);
	checkStore(((LocStore*)children[i])->store, MergeV);
      
      }

    }
    else {

      std::sort(incomingPtrs.begin(), incomingPtrs.end(), derefLT);
      SmallVector<void**, 4>::iterator uniqend = std::unique(incomingPtrs.begin(), incomingPtrs.end(), derefEQ);
      
      // This subtree never differs?
      if(std::distance(incomingPtrs.begin(), uniqend) == 1)
	continue;

      // Recursively merge this child.
      // CoW break this subtree if necessary.
      children[i] = ((SharedTreeNode*)children[i])->getWritableNode(height - 1);

      uint32_t newIdx = idx | (i << (HEAPTREEORDERLOG2 * height));
      SmallVector<SharedTreeNode*, 4> otherChildren;
      for(SmallVector<void**, 4>::iterator it = incomingPtrs.begin(), itend = incomingPtrs.end();
	  it != itend; ++it) {
	
	if(!*it)
	  otherChildren.push_back(0);
	else
	  otherChildren.push_back((SharedTreeNode*)**it);

      }

      ((SharedTreeNode*)children[i])->mergeHeaps(otherChildren, allOthersClobbered, height - 1, newIdx, visitor);

    }

  }

}

// Comparator for finding the best target heap: we want the tallest heap, and of those, we favour a writable one. Finally compare pointers.
static bool rootTallerThan(const LocalStoreMap* r1, const LocalStoreMap* r2) {

  if(r1->heap.height != r2->heap.height)
    return r1->heap.height > r2->heap.height;

  return r1->heap.root > r2->heap.root;
  
}

static bool rootsEqual(const LocalStoreMap* r1, const LocalStoreMap* r2) {

  return r1->heap.root == r2->heap.root && r1->heap.height == r2->heap.height;

}

void MergeBlockVisitor::mergeHeaps(LocalStoreMap* toMap, SmallVector<LocalStoreMap*, 4>::iterator fromBegin, SmallVector<LocalStoreMap*, 4>::iterator fromEnd) {

  SmallVector<LocalStoreMap*, 4> incomingRoots;
  incomingRoots.reserve(std::distance(fromBegin, fromEnd) + 1);

  incomingRoots.push_back(toMap);
  for(SmallVector<LocalStoreMap*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
    incomingRoots.push_back(*it);

  /*
  errs() << "Target heap:\n";
  if(toMap->heap.root)
    toMap->heap.root->print(errs(), false, toMap->heap.height - 1, 0);

  for(SmallVector<LocalStoreMap*, 4>::iterator it = fromBegin; it != fromEnd; ++it) {
    errs() << "Merging in:\n";
    if((*it)->heap.root)
      (*it)->heap.root->print(errs(), false, (*it)->heap.height - 1, 0);
  }
  */

  // This sorts first by heap height, then by pointer address, so it also finds the tallest heap.
  std::sort(incomingRoots.begin(), incomingRoots.end(), rootTallerThan);
  SmallVector<LocalStoreMap*, 4>::iterator uniqend = std::unique(incomingRoots.begin(), incomingRoots.end(), rootsEqual);
  
  // Heaps never differ?
  if(std::distance(incomingRoots.begin(), uniqend) == 1)
    return;

  release_assert(incomingRoots[0]->heap.height != 0 && "If heaps differ at least one must be initialised!");

  if(!toMap->heap.root) {

    // Target has no heap at all yet -- make one.
    toMap->heap.root = new SharedTreeNode();
    toMap->heap.height = 1;

  }
  else {

    // If necessary, CoW break the target heap.
    toMap->heap.root = toMap->heap.root->getWritableNode(toMap->heap.height - 1);

  }

  // Grow the target heap to the tallest height seen.
  if(toMap->heap.height != incomingRoots[0]->heap.height)
    toMap->heap.growToHeight(incomingRoots[0]->heap.height);

  // Start the tree merge:
  SmallVector<SharedTreeNode*, 4> roots;
  for(SmallVector<LocalStoreMap*, 4>::iterator it = incomingRoots.begin(); it != uniqend; ++it) {

    if(toMap->heap.root == (*it)->heap.root)
      continue;

    LocalStoreMap* thisMap = *it;

    // Temporarily grow heaps that are shorter than the target to make the merge easier to code.
    // Leave their height attribute unchanged as an indicator we need to undo this shortly.
    // These maps might be shared so it's important they are seen unmodified ouside this function.
    if(thisMap->heap.height != 0 && thisMap->heap.height < toMap->heap.height) {
      uint32_t oldHeight = thisMap->heap.height;
      thisMap->heap.growToHeight(toMap->heap.height);
      thisMap->heap.height = oldHeight;
    }

    roots.push_back(thisMap->heap.root);

  }

  toMap->heap.root->mergeHeaps(roots, toMap->allOthersClobbered, toMap->heap.height - 1, 0, this);

  for(SmallVector<LocalStoreMap*, 4>::iterator it = incomingRoots.begin(); it != uniqend; ++it) {

    if((*it)->heap.height == 0)
      continue;

    LocalStoreMap* thisMap = *it;
    uint32_t tempFramesToRemove = incomingRoots[0]->heap.height - thisMap->heap.height;

    for(uint32_t i = 0; i < tempFramesToRemove; ++i) {
      SharedTreeNode* removeNode = thisMap->heap.root;
      thisMap->heap.root = (SharedTreeNode*)thisMap->heap.root->children[0];
      release_assert(removeNode->refCount == 1 && "Removing shared node in post-treemerge cleanup?");
      delete removeNode;
    }

  }  

}

static bool storeLT(const LocStore* a, const LocStore* b) {

  return a->store < b->store;

}

static bool storeEQ(const LocStore* a, const LocStore* b) {

  return a->store == b->store;

}

void MergeBlockVisitor::mergeFrames(LocalStoreMap* toMap, SmallVector<LocalStoreMap*, 4>::iterator fromBegin, SmallVector<LocalStoreMap*, 4>::iterator fromEnd, uint32_t idx) {

  SmallVector<SharedStoreMap*, 4> incomingFrames;
  incomingFrames.reserve(std::distance(fromBegin, fromEnd) + 1);

  incomingFrames.push_back(toMap->frames[idx]);
  for(SmallVector<LocalStoreMap*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
    incomingFrames.push_back((*it)->frames[idx]);

  std::sort(incomingFrames.begin(), incomingFrames.end());
  SmallVector<SharedStoreMap*, 4>::iterator uniqend = std::unique(incomingFrames.begin(), incomingFrames.end());

  // Frames never differ?
  if(std::distance(incomingFrames.begin(), uniqend) == 1)
    return;

  // CoW break stack frame if necessary
  SharedStoreMap* mergeToFrame = toMap->frames[idx] = toMap->frames[idx]->getWritableStoreMap();
  std::vector<LocStore>& mergeToStore = mergeToFrame->store;

  InlineAttempt* thisFrameIA = mergeToFrame->IA;

  // Merge in each other frame. Note toMap->allOthersClobbered has been set to big-or over all maps already.
  for(SmallVector<SharedStoreMap*, 4>::iterator it = incomingFrames.begin(); it != uniqend; ++it) {

    SharedStoreMap* mergeFromFrame = *it;
    if(mergeFromFrame == mergeToFrame)
      continue;
    std::vector<LocStore>& mergeFromStore = mergeFromFrame->store;

    if(toMap->allOthersClobbered) {
      
      // Incremental big intersection of the incoming frames
      // Remove any in mergeTo that do not occur in mergeFrom.

      // Remove any existing mappings in mergeToFrame that do not occur in mergeFromFrame:

      for(uint32_t i = 0, ilim = mergeToStore.size(); i != ilim; ++i) {

	if(mergeToStore[i].store && (i > mergeFromStore.size() || !mergeFromStore[i].store)) {
	  mergeToStore[i].store->dropReference();
	  mergeToStore[i].store = 0;
	}

      }

      if(mergeToStore.size() > mergeFromStore.size())
	mergeToStore.resize(mergeFromStore.size());

    }
    else {

      LFV3(errs() << "Both maps don't have allOthersClobbered; reading through allowed\n");

      // For any locations mentioned in mergeFromFrame but not mergeToFrame,
      // add a copy of the base object to mergeToFrame. This will get overwritten below but
      // creates the asymmetry that x in mergeFromFrame -> x in mergeToFrame.

      if(mergeFromStore.size() > mergeToStore.size())
	mergeToStore.resize(mergeFromStore.size());

      for(uint32_t i = 0, ilim = mergeFromStore.size(); i != ilim; ++i) {
	  
	if(mergeFromStore[i].store && !mergeToStore[i].store) {
	  mergeToStore[i] = LocStore(thisFrameIA->getAllocaWithIdx(i)->store);
	  mergeToStore[i].store = mergeToStore[i].store->getReadableCopy();
	}
	
      }
      
    }

  }

  // mergeToFrame now contains all objects that should be merged.
  // Note that in the allOthersClobbered case this only merges in
  // information from locations explicitly mentioned in all incoming frames.

  for(uint32_t i = 0, ilim = mergeToStore.size(); i != ilim; ++i) {

    if(!mergeToStore[i].store)
      continue;

    LocStore* mergeToLoc = &(mergeToStore[i]);

    ShadowValue mergeSV = ShadowValue(thisFrameIA->getAllocaWithIdx(i));

    SmallVector<LocStore*, 4> incomingStores;

    for(SmallVector<SharedStoreMap*, 4>::iterator incit = incomingFrames.begin(); incit != uniqend; ++incit) {

      SharedStoreMap* mergeFromFrame = *incit;
      if(mergeFromFrame == mergeToFrame)
	continue;

      LocStore* mergeFromLoc;

      if(mergeFromFrame->store.size() > i && mergeFromFrame->store[i].store)
	mergeFromLoc = &(mergeFromFrame->store[i]);
      else
	mergeFromLoc = &((*incit)->IA->getAllocaWithIdx(i)->store);

      incomingStores.push_back(mergeFromLoc);

    }

    std::sort(incomingStores.begin(), incomingStores.end(), storeLT);
    SmallVector<LocStore*, 4>::iterator storeuniqend = 
      std::unique(incomingStores.begin(), incomingStores.end(), storeEQ);

    for(SmallVector<LocStore*, 4>::iterator incit = incomingStores.begin(), incitend = incomingStores.end();
	incit != incitend; ++incit) {

      LocStore* mergeFromLoc = *incit;

      // Right, merge it->second and mergeFromLoc.
      if(mergeFromLoc->store != mergeToLoc->store) {
      
	mergeStores(mergeFromLoc, mergeToLoc, mergeSV);
	checkStore(mergeToLoc->store, mergeSV);

      }

    }

  }

}

// mergeBegin -> mergeEnd are already listed smallest set first.
static void intersectSets(DenseSet<ShadowValue>* Target, SmallVector<DenseSet<ShadowValue>*, 4>::iterator mergeBegin, SmallVector<DenseSet<ShadowValue>*, 4>::iterator mergeEnd) {

  SmallVector<ShadowValue, 8> toKeep;

  if(Target->size() < (*mergeBegin)->size()) {

    for(DenseSet<ShadowValue>::iterator it = Target->begin(), itend = Target->end(); it != itend; ++it) {

      bool keepThis = true;
      for(SmallVector<DenseSet<ShadowValue>*, 4>::iterator findit = mergeBegin; findit != mergeEnd && keepThis; ++findit) {

	if(!(*findit)->count(*it))
	  keepThis = false;

      }

      if(keepThis)
	toKeep.push_back(*it);

    }

  }
  else {

    SmallVector<DenseSet<ShadowValue>*, 4>::iterator othersBegin = mergeBegin;
    ++othersBegin;

    for(DenseSet<ShadowValue>::iterator it = (*mergeBegin)->begin(), 
	  itend = (*mergeBegin)->end(); it != itend; ++it) {

      bool keepThis = Target->count(*it);
      for(SmallVector<DenseSet<ShadowValue>*, 4>::iterator findit = othersBegin; findit != mergeEnd && keepThis; ++findit) {

	if(!(*findit)->count(*it))
	  keepThis = false;

      }

      if(keepThis)
	toKeep.push_back(*it);
      
    }
    
  }

  Target->clear();
  Target->insert(toKeep.begin(), toKeep.end());

}

static bool sizeLT(const DenseSet<ShadowValue>* a, const DenseSet<ShadowValue>* b) {

  return a->size() < b->size();

}

void MergeBlockVisitor::mergeFlags(LocalStoreMap* toMap, SmallVector<LocalStoreMap*, 4>::iterator fromBegin, SmallVector<LocalStoreMap*, 4>::iterator fromEnd) {

  // Both the threadLocalObjects and noAliasOldObjects sets should be big-intersected.
  
  {
    SmallVector<DenseSet<ShadowValue>*, 4> NAOSets;
    std::sort(NAOSets.begin(), NAOSets.end(), sizeLT);
    for(SmallVector<LocalStoreMap*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
      NAOSets.push_back(&(*it)->noAliasOldObjects);
    intersectSets(&toMap->noAliasOldObjects, NAOSets.begin(), NAOSets.end());
    if(verbose) {
      errs() << "Not-old:\n";
      for(DenseSet<ShadowValue>::iterator it = toMap->noAliasOldObjects.begin(), itend = toMap->noAliasOldObjects.end(); it != itend; ++it) {

	errs() << itcache(*it) << "\n";

      }
      errs() << "\n\n";
    }
  }

  {
    SmallVector<DenseSet<ShadowValue>*, 4> TLSets;
    std::sort(TLSets.begin(), TLSets.end(), sizeLT);
    for(SmallVector<LocalStoreMap*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
      TLSets.push_back(&(*it)->threadLocalObjects);
    intersectSets(&toMap->threadLocalObjects, TLSets.begin(), TLSets.end());
    if(verbose) {
      errs() << "Thread-local:\n";
      for(DenseSet<ShadowValue>::iterator it = toMap->threadLocalObjects.begin(), itend = toMap->threadLocalObjects.end(); it != itend; ++it) {

	errs() << itcache(*it) << "\n";

      }
      errs() << "\n\n";
    }
  }

}

void MergeBlockVisitor::doMerge() {

  if(incomingBlocks.empty())
    return;

  // Discard wholesale block duplicates:
  SmallVector<LocalStoreMap*, 4> incomingStores;
  incomingStores.reserve(std::distance(incomingBlocks.begin(), incomingBlocks.end()));

  for(SmallVector<ShadowBB*, 4>::iterator it = incomingBlocks.begin(), itend = incomingBlocks.end();
      it != itend; ++it) {

    incomingStores.push_back((*it)->localStore);

  }

  std::sort(incomingStores.begin(), incomingStores.end());
  SmallVector<LocalStoreMap*, 4>::iterator uniqend = std::unique(incomingStores.begin(), incomingStores.end());

  LocalStoreMap* retainMap;
  
  if(std::distance(incomingStores.begin(), uniqend) > 1) {

    // At least some stores differ; need to make a new one.

    // See if we can avoid a CoW break by using a writable incoming store as the target.
    for(SmallVector<LocalStoreMap*, 4>::iterator it = incomingStores.begin(); it != uniqend; ++it) {
      
      if((*it)->refCount == 1) {

	if(it != incomingStores.begin())
	  std::swap(incomingStores[0], *it);
	break;

      }

    }

    // Position 0 is the target; the rest should be merged in. CoW break if still necessary:
    // Note retainMap is set to the original map rather than the new one as the CoW break drops
    // a reference to it so it should not be unref'd again below.
    retainMap = incomingStores[0];
    LocalStoreMap* mergeMap = incomingStores[0] = incomingStores[0]->getWritableFrameList();
    LFV3(errs() << "Merge target will be " << mergeMap << "\n");

    SmallVector<LocalStoreMap*, 4>::iterator firstMergeFrom = incomingStores.begin();
    ++firstMergeFrom;

    for(SmallVector<LocalStoreMap*, 4>::iterator it = firstMergeFrom; 
	it != uniqend && !mergeMap->allOthersClobbered; ++it) {

      if((*it)->allOthersClobbered)
	mergeMap->allOthersClobbered = true;

    }
   
    // Merge each frame, passing the InlineAttempt corresponding to each frame in turn.
    for(uint32_t i = 0; i < mergeMap->frames.size(); ++i)
      mergeFrames(mergeMap, firstMergeFrom, uniqend, i);

    mergeHeaps(mergeMap, firstMergeFrom, uniqend);

    mergeFlags(mergeMap, firstMergeFrom, uniqend);

    newMap = mergeMap;

  }
  else {

    // No stores differ; just use #0
    newMap = incomingStores[0];
    retainMap = newMap;

    if(verbose) {

      errs() << "Not-old:\n";
      for(DenseSet<ShadowValue>::iterator it = newMap->noAliasOldObjects.begin(), itend = newMap->noAliasOldObjects.end(); it != itend; ++it) {

	errs() << itcache(*it) << "\n";

      }
      errs() << "\n\n";

      errs() << "Thread-local:\n";
      for(DenseSet<ShadowValue>::iterator it = newMap->threadLocalObjects.begin(), itend = newMap->threadLocalObjects.end(); it != itend; ++it) {

	errs() << itcache(*it) << "\n";

      }
      errs() << "\n\n";
      
    }

  }

  // Drop refs against each incoming store apart from the store that was either used or
  // implicitly unref'd as part of the CoW break at getWritableFrameMap.

  for(SmallVector<ShadowBB*, 4>::iterator it = incomingBlocks.begin(), itend = incomingBlocks.end();
      it != itend; ++it) {

    LocalStoreMap* thisMap = (*it)->localStore;
    if(thisMap == retainMap)
      retainMap = 0;
    else
      thisMap->dropReference();

  }

}

void llvm::commitFrameToBase(SharedStoreMap* Map) {

  uint32_t i = 0;
  for(std::vector<LocStore>::iterator it = Map->store.begin(), itend = Map->store.end(); it != itend; ++it, ++i) {

    if(!it->store)
      continue;

    LocStore& baseStore = Map->IA->getAllocaWithIdx(i)->store;
    baseStore.store->dropReference();
    baseStore = *it;
    baseStore.store = baseStore.store->getReadableCopy();

  }  

}

void SharedTreeNode::commitToBase(uint32_t height, uint32_t idx) {

  if(height == 0) {

    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      if(!children[i])
	continue;
      LocStore& baseStore = getAllocWithIdx(idx + i).getBaseStore();
      baseStore.store->dropReference();
      baseStore = *((LocStore*)children[i]);
      baseStore.store = baseStore.store->getReadableCopy();

    }

  }
  else {
    
    for(uint32_t i = 0; i < HEAPTREEORDER; ++i) {

      if(!children[i])
	continue;
      uint32_t newIdx = idx | (i << (HEAPTREEORDERLOG2 * height));
      ((SharedTreeNode*)children[i])->commitToBase(height - 1, newIdx);

    }    

  }

}

void llvm::commitStoreToBase(LocalStoreMap* Map) {

  if(Map->heap.root)
    Map->heap.root->commitToBase(Map->heap.height - 1, 0);
  for(uint32_t i = 0; i < Map->frames.size(); ++i)
    commitFrameToBase(Map->frames[i]);

}

// Return false if this block turns out to have no live predecessors at the moment.
// This is possible in the unusual case that a per-iteration loop exploration has
// created the block to find invariants but it isn't yet reachable according to the
// fixed point analyser -- e.g. this block only becomes reachable on iteration 2.
// TODO: invariants like that have been removed, so could probably drop the return value
// and tests on same.
bool llvm::doBlockStoreMerge(ShadowBB* BB) {

  // We're entering BB; one or more live predecessor blocks exist and we must produce an appropriate
  // localStore from them.

  LFV3(errs() << "Start block store merge\n");

  bool mergeToBase = BB->status == BBSTATUS_CERTAIN && (!BB->inAnyLoop) && !BB->IA->pass->enableSharing;
  if(mergeToBase) {

    LFV3(errs() << "MERGE to base store for " << BB->IA->F.getName() << " / " << BB->IA->SeqNumber << " / " << BB->invar->BB->getName() << "\n");

  }
  // This BB is a merge of all that has gone before; merge to values' base stores
  // rather than a local map.

  MergeBlockVisitor V(mergeToBase, BB->useSpecialVarargMerge, /* verbose = */ false);
  BB->IA->visitNormalPredecessorsBW(BB, &V, /* ctx = */0);
  V.doMerge();

  if(!V.newMap) {
    BB->localStore = 0;
    return false;
  }

  // TODO: do this better; currently creates an intermediate block-local map for no good reason.
  if(mergeToBase && !V.newMap->allOthersClobbered) {
    commitStoreToBase(V.newMap);
    V.newMap = V.newMap->getEmptyMap();
  }

  BB->localStore = V.newMap;

  return true;

}

void LocalStoreMap::popStackFrame() {

  release_assert(frames.size() && "Pop from empty stack?");
  frames.back()->dropReference();
  frames.pop_back();

}

void ShadowBB::popStackFrame() {

  localStore = localStore->getWritableFrameList();
  localStore->popStackFrame();  

}

void LocalStoreMap::pushStackFrame(InlineAttempt* IA) {

  frames.push_back(new SharedStoreMap(IA, IA->invarInfo->frameSize));

}

void ShadowBB::pushStackFrame(InlineAttempt* IA) {

  localStore = localStore->getWritableFrameList();
  localStore->pushStackFrame(IA);

}

// Merge the stores presented at SI's callee's return blocks into a single store
// to analyse the remainder of the program.
// Note that the callee has already popped the top stack frame from each one.
void llvm::doCallStoreMerge(ShadowInstruction* SI) {

  LFV3(errs() << "Start call-return store merge\n");

  bool mergeToBase = SI->parent->status == BBSTATUS_CERTAIN && (!SI->parent->inAnyLoop) && !SI->parent->IA->pass->enableSharing;
  if(mergeToBase) {

    LFV3(errs() << "MERGE to base store for " << SI->parent->IA->F.getName() << " / " << SI->parent->IA->SeqNumber << " / " << SI->parent->invar->BB->getName() << "\n");

  }

  InlineAttempt* CallIA = SI->parent->IA->getInlineAttempt(SI);

  MergeBlockVisitor V(mergeToBase);
  CallIA->visitLiveReturnBlocks(V);
  V.doMerge();
  
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
