//===-- LoadForward.cpp ---------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

// This file contains most logic relating to symbolic memory, and evaluating
// load and store instructions against it.

#define DEBUG_TYPE "LoadForward"

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LLPECopyPaste.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

#include <memory>

using namespace llvm;

// Bug check: make sure null pointer values haven't been accidentally annotated as scalars.
static void checkIVSNull(ImprovedValSetSingle& IVS) {

  for(uint32_t i = 0, ilim = IVS.Values.size(); i != ilim; ++i) {

    if(IVS.Values[i].V.isNullPointer())
      release_assert(IVS.SetType == ValSetTypePB);

  }

}

// An ImprovedValSetMulti represents a composite improved value -- for example,
// { i32 flags, i32 fd }, which cannot be represented as a constant since the fd
// is a symbolic object whilst the flags are a simple constant.
// We use an IntervalMap (named Map) to describe how component IVSes are laid out.
// They might describe a whole object, or if Underlying is set describe an overlay
// atop that map.
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
bool llvm::operator==(const ImprovedValSetMulti& PB1, const ImprovedValSetMulti& PB2) {

  ImprovedValSetMulti::ConstMapIt 
    it1 = PB1.Map.begin(), it1end = PB1.Map.end(), 
    it2 = PB2.Map.begin(), it2end = PB2.Map.end();

  for(; it1 != it1end && it2 != it2end; ++it1, ++it2) {

    if(it1.start() != it2.start() || it1.stop() != it2.stop() || it1.value() != it2.value())
      return false;

  }

  // Lengths differed?
  if(it1 != it1end || it2 != it2end)
    return false;

  return true;

}

// Check if Ty is a pointer, or a structure, tuple or similar with a pointer member.
static bool containsPointerTypes(Type* Ty) {

  if(Ty->isPointerTy())
    return true;

  for(Type::subtype_iterator it = Ty->subtype_begin(), it2 = Ty->subtype_end(); it != it2; ++it) {

    if(containsPointerTypes(*it))
      return true;

  }

  return false;

}

// Try to resolve a load from the symbolic varargs pointer.
bool IntegrationAttempt::tryResolveLoadFromVararg(ShadowInstruction* LoadI, ImprovedValSet*& Result) {

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

  return false;

}

// Check if the load address (Ptr) refers to a cosntant; if so populate Result.
bool IntegrationAttempt::tryResolveLoadFromConstant(ShadowInstruction* LoadI, ImprovedVal Ptr, ImprovedValSetSingle& Result) {

  // We already know Ptr has a known offset (i.e. Ptr.Offset != LLONG_OFFSET).

  if(ShadowGV* SGV = Ptr.V.getGV()) {

    GlobalVariable* GV = SGV->G;
    
    if(GV->isConstant()) {

      uint64_t LoadSize = GlobalTD->getTypeStoreSize(LoadI->getType());
      Type* FromType = GV->getInitializer()->getType();
      uint64_t FromSize = GlobalTD->getTypeStoreSize(FromType);

      if(Ptr.Offset < 0 || Ptr.Offset + LoadSize > FromSize) {
	Result.setOverdef();
	return true;
      }
      
      // getConstSubVal does the merge with Result.
      getConstSubVal(ShadowValue(GV->getInitializer()), Ptr.Offset, LoadSize, LoadI->getType(), Result);
      return true;

    }

  }

  return false;
  
}

// Check if PB is a set of definite pointers, potentially including nulls.
static bool shouldMultiload(ImprovedValSetSingle& PB) {

  if(PB.isWhollyUnknown() || PB.Values.size() == 0)
    return false;

  // One or more non-pointers in PB?
  if(PB.SetType != ValSetTypePB)
    return false;

  uint32_t numNonNulls = 0;

  for(uint32_t i = 0, ilim = PB.Values.size(); i != ilim; ++i) {

    if(Value* V = PB.Values[i].V.getVal()) {
      if(isa<ConstantPointerNull>(V))
	continue;
      if(isa<UndefValue>(V))
	continue;
    }

    // Pointer with unknown offset?
    if(PB.Values[i].Offset == LLONG_MAX)
      return false;

    ++numNonNulls;

  }

  return numNonNulls >= 1;

}

// Try to execute load LI which reads from a set of 2+ pointers.
static bool tryMultiload(ShadowInstruction* LI, ImprovedValSet*& NewIV, std::string* report) {

  uint64_t LoadSize = GlobalTD->getTypeStoreSize(LI->getType());

  // We already know that LI's IVSet is made up entirely of nulls and definite pointers.
  ImprovedValSetSingle* NewPB = newIVS();
  NewIV = NewPB;

  ImprovedValSetSingle LIPB;
  getImprovedValSetSingle(LI->getOperand(0), LIPB);

  std::unique_ptr<raw_string_ostream> RSO(report ? new raw_string_ostream(*report) : 0);

  LI->isThreadLocal = TLS_NEVERCHECK;

  for(uint32_t i = 0, ilim = LIPB.Values.size(); i != ilim && !NewPB->Overdef; ++i) {

    if(Value* V = LIPB.Values[i].V.getVal()) {

      if(isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
	continue;

    }

    if(LI->parent->IA->tryResolveLoadFromConstant(LI, LIPB.Values[i], *NewPB))
      continue;

    if(!LI->parent->localStore->es.threadLocalObjects.count(LIPB.Values[i].V))
      LI->isThreadLocal = TLS_MUSTCHECK;

    std::unique_ptr<std::string> ThisError(RSO.get() ? new std::string() : 0);
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
  std::unique_ptr<std::string> error(pass->verboseOverdef ? new std::string() : 0);

  if(tryResolveLoadFromVararg(LI, NewPB))
    return true;

  bool ret;

  ImprovedValSetSingle LoadPtrPB;
  getImprovedValSetSingle(LI->getOperand(0), LoadPtrPB);
  if(shouldMultiload(LoadPtrPB)) {

    ret = tryMultiload(LI, NewPB, error.get());
    if(ImprovedValSetSingle* NewIVS = dyn_cast<ImprovedValSetSingle>(NewPB)) {

      if(NewIVS->SetType == ValSetTypeVarArg)
	loadedVararg = true;

      if(NewIVS->SetType == ValSetTypeScalar && !NewIVS->Overdef) {

	release_assert(!NewIVS->Values[0].V.isNullPointer());

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
    pass->optimisticForwardStatus[LI] = *error;
   
  return ret;

}

// Get the heap object ID for this ShadowValue. Only applies if this is a pointer or special (symbolic) object.
// Return -1 if this is a non-pointer or unknown pointer.
int32_t ShadowValue::getHeapKey() const {

  switch(t) {

  case SHADOWVAL_GV:
    release_assert(!u.GV->G->isConstant());
    return u.GV->allocIdx;
  case SHADOWVAL_OTHER:
    {
      Function* KeyF = cast<Function>(u.V);
      SpecialLocationDescriptor& sd = GlobalIHP->specialLocations[KeyF];
      return sd.heapIdx;
    }
  case SHADOWVAL_ARG:
    release_assert((u.A->IA->isRootMainCall()) && "getHeapKey on arg other than root argv?");
    return GlobalIHP->argStores[u.A->invar->A->getArgNo()].heapIdx;
  case SHADOWVAL_INST:
    release_assert(0 && "Unsafe reference to heap key of instruction");
    llvm_unreachable("Unsafe reference to heap key of instruction");
  case SHADOWVAL_PTRIDX:
  case SHADOWVAL_FDIDX:
  case SHADOWVAL_FDIDX64:
    return u.PtrOrFd.idx;
  default:
    return -1;

  }

}

uint64_t ShadowValue::getAllocSize(OrdinaryLocalStore* M) const {

  switch(t) {
  case SHADOWVAL_PTRIDX:
    return getAllocData(M)->storeSize;
  case SHADOWVAL_GV:
    return u.GV->storeSize;
  case SHADOWVAL_OTHER:
    return GlobalIHP->specialLocations[cast<Function>(u.V)].storeSize;
  case SHADOWVAL_ARG:
    // Arg objects currently of unknown size
    return ULONG_MAX;
   
  default:
    llvm_unreachable("Bad SV for getAllocSize");
  }

}

uint64_t llvm::getHeapAllocSize(ShadowValue V) {

  // Don't actually need the map to find a heap location
  return V.getAllocSize((OrdinaryLocalStore*)0);

}

uint64_t llvm::getAllocSize(InlineAttempt* IA, uint32_t idx) {

  return IA->localAllocas[idx].storeSize;

}

uint64_t ShadowValue::getAllocSize(IntegrationAttempt* IA) const {

  switch(t) {
  case SHADOWVAL_PTRIDX:
    if(u.PtrOrFd.frame == -1) // Heap or special object?
      return getAllocSize((OrdinaryLocalStore*)0);
    else { // Stack object?
      uint32_t i;
      InlineAttempt* InA;
      release_assert(u.PtrOrFd.frame <= IA->stack_depth);
      for(i = 0, InA = IA->getFunctionRoot(); 
	  u.PtrOrFd.frame < InA->stack_depth; 
	  ++i, InA = InA->activeCaller->parent->IA->getFunctionRoot()) { }
      return InA->localAllocas[u.PtrOrFd.idx].storeSize;
    }
  default:
    return getAllocSize((OrdinaryLocalStore*)0);
  }

}

ShadowValue& llvm::getAllocWithIdx(int32_t idx) {

  // Warning: need to be sure the allocation still exists, really only for debugging.
  return GlobalIHP->heap[idx].allocValue;

}

// Check this is a pointer and get the frame number it refers to (stack index, or -1 if heap allocated or special)
int32_t ShadowValue::getFrameNo() const {

  release_assert((!isInst()) && "Unsafe reference to alloc instruction");
  if(isPtrIdx())
    return u.PtrOrFd.frame;
  else
    return -1;

}

// Get a readable / writable symbolic object for V
LocStore* ShadowBB::getReadableStoreFor(const ShadowValue& V) {

  return localStore->getReadableStoreFor(V);

}

LocStore* ShadowBB::getOrCreateStoreFor(ShadowValue& V, bool* isNewStore) {

  localStore = localStore->getWritableFrameList();
  return localStore->getOrCreateStoreFor(V, isNewStore);

}

uint64_t ShadowBB::getAllocSize(ShadowValue V) {

  return V.getAllocSize(localStore);

}

// Verbose printout of how many layers of stacked ImprovedValSetMultis are involved in IVS.
static int logReadDepth(ImprovedValSet* IVS, uint32_t depth) {

  ImprovedValSetMulti* IVM = dyn_cast<ImprovedValSetMulti>(IVS);
  if((!IVM) || !IVM->Underlying) {
    
    if(depth >= 2)
      errs() << "RD " << depth << "\n";
    return depth;
    
  }
  else {
    
    return logReadDepth(IVM->Underlying, depth + 1);

  }
  
}

// Get a writable symbolic object for V, to be written at Offset - Offset+Size.
// willWriteSingleObject permits a shortcut in which we allocate space for a single object instead of an extent-list
// as needed for structs etc.
LocStore* ShadowBB::getWritableStoreFor(ShadowValue& V, int64_t Offset, uint64_t Size, bool willWriteSingleObject) {

  // Check if the location is not writable:
  if(V.isNullPointer())
    return 0;

  if(V.isVal()) {

    if(isa<UndefValue>(V.u.V))
      return 0;

  }
  else if(V.isGV()) {

    if(V.u.GV->G->isConstant())
      return 0;

  }

  // We're about to write to memory location V + Offset -> Offset+Size. 
  // We must return a LocStore for that value that can be updated (i.e. is not shared).
  // We need to write into the block-local store map. COW break it if necessary:
  uint64_t ASize = getAllocSize(V);
  bool writeWholeObject = (Offset == 0 && (Size == ULONG_MAX || Size == ASize));
   
  bool isNewStore;
  LocStore* ret = getOrCreateStoreFor(V, &isNewStore);

  if(isNewStore) {

    // There wasn't an entry in the local map. Make a Single or Multi store depending on
    // whether we're about to cover the whole store or not:
    if(writeWholeObject && willWriteSingleObject) {
      LFV3(errs() << "Create new store with blank single\n");
      ret->store = new ImprovedValSetSingle();
    }
    else {
      // Defer the rest of the multimap to the base object.
      ImprovedValSetMulti* M = new ImprovedValSetMulti(ASize);
      if(writeWholeObject) {
	M->Underlying = 0;
      }
      else if(localStore->allOthersClobbered) {
	M->Underlying = new ImprovedValSetSingle(ValSetTypeUnknown, true);
      }
      else {
	M->Underlying = 0;
	LFV3(errs() << "Create new store with multi based on " << M->Underlying << "\n");
	LFV3(M->print(errs()));
      }
      ret->store = M;
    }

    return ret;

  }
  else {

    LFV3(errs() << "Use existing store " << ret->store << "\n");

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

      ImprovedValSetMulti* NewIMap = new ImprovedValSetMulti(ASize);
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

  return ret;
  
}

// Try to retrieve part of maybe-composite-typed constant FromC.
Constant* llvm::extractAggregateMemberAt(Constant* FromC, int64_t Offset, Type* Target, uint64_t TargetSize, const DataLayout* TD) {

  Type* FromType = FromC->getType();
  uint64_t FromSize = (TD->getTypeSizeInBits(FromType) + 7) / 8;

  if(Offset == 0 && TargetSize == FromSize) {
    if(!Target)
      return FromC;
    if(allowTotalDefnImplicitCast(FromType, Target))
      return (FromC);
    else if(allowTotalDefnImplicitPtrToInt(FromType, Target, TD))
      return ConstantExpr::getPtrToInt(FromC, Target);
    LLVM_DEBUG(dbgs() << "Can't use simple element extraction because load implies cast from " << (*(FromType)) << " to " << (*Target) << "\n");
    return 0;
  }

  if(Offset < 0 || Offset + TargetSize > FromSize) {

    LLVM_DEBUG(dbgs() << "Can't use element extraction because offset " << Offset << " and size " << TargetSize << " are out of bounds for object with size " << FromSize << "\n");
    return 0;

  }

  if(isa<ConstantAggregateZero>(FromC) && Offset + TargetSize <= FromSize) {

    // Wholly subsumed within a zeroinitialiser:
    if(!Target) {
      Target = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
    }
    return (Constant::getNullValue(Target));

  }

  if(isa<UndefValue>(FromC)) {

    if(!Target)
      Target = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
    return UndefValue::get(Target);

  }

  uint64_t StartE, StartOff, EndE, EndOff;
  bool mightWork = false;

  if(ConstantArray* CA = dyn_cast<ConstantArray>(FromC)) {

    mightWork = true;
    
    Type* EType = CA->getType()->getElementType();
    uint64_t ESize = (TD->getTypeSizeInBits(EType) + 7) / 8;
    
    StartE = Offset / ESize;
    StartOff = Offset % ESize;
    EndE = (Offset + TargetSize) / ESize;
    EndOff = (Offset + TargetSize) % ESize;

  }
  else if(ConstantStruct* CS = dyn_cast<ConstantStruct>(FromC)) {

    mightWork = true;

    const StructLayout* SL = TD->getStructLayout(CS->getType());
    if(!SL) {
      LLVM_DEBUG(dbgs() << "Couldn't get struct layout for type " << *(CS->getType()) << "\n");
      return 0;
    }

    StartE = SL->getElementContainingOffset(Offset);
    StartOff = Offset - SL->getElementOffset(StartE);
    EndE = SL->getElementContainingOffset(Offset + TargetSize);
    EndOff = (Offset + TargetSize) - SL->getElementOffset(EndE);

  }

  if(mightWork) {
    if(StartE == EndE || (StartE + 1 == EndE && !EndOff)) {
      // This is a sub-access within this element.
      return extractAggregateMemberAt(cast<Constant>(FromC->getOperand(StartE)), StartOff, Target, TargetSize, TD);
    }
    LLVM_DEBUG(dbgs() << "Can't use simple element extraction because load spans multiple elements\n");
  }
  else {
    LLVM_DEBUG(dbgs() << "Can't use simple element extraction because load requires sub-field access\n");
  }

  return 0;

}

// Try to read V[Offset:Offset+Size], which has symbolic object 'store', in the context of ReadBB.
// The result is written to Result, or to ResultPV if it is necessary to build the result bytewise, e.g. because the read type doesn't match the write type
// or the read is fed by multiple stores.
// Set shouldTryMulti if we note a case where an ImprovedValSetMulti (extent list) could accommodate the result but ImprovedValSetSingle cannot.
// That usually happens when reading struct types, vector types and similar that contain pointers and so can't be expressed as bytes.
// In debug builds, give a verbose reason why the read failed in 'error'.
void llvm::readValRangeFrom(ShadowValue& V, uint64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSet* store, ImprovedValSetSingle& Result, PartialVal*& ResultPV, bool& shouldTryMulti, std::string* error) {

  const ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(store);
  uint64_t IVSSize = ReadBB->getAllocSize(V);
  ImprovedValSetMulti* IVM;
  ImprovedValSetMulti::MapIt it;

  LFV3(errs() << "Read range " << Offset << "-" << (Offset+Size) << "\n");

  if(!IVS) {

    // Check for a multi-member that wholly defines the target value:

    IVM = cast<ImprovedValSetMulti>(store);
    it = IVM->Map.find(Offset);

    if(it != IVM->Map.end() && it.start() <= Offset && it.stop() >= (Offset + Size)) {

      IVS = &it.value();
      IVSSize = it.stop() - it.start();
      Offset -= it.start();
      LFV3(errs() << "Read fully defined by multi subval " << it.start() << "-" << it.stop() << "\n");

    }

  }

  if(IVS) {

    if(!ResultPV) {

      // Try to extract the entire value. Scalar splat values need expanding anyway, so fall through
      // in that case.
      if(IVSSize == Size && Offset == 0 && IVS->SetType != ValSetTypeScalarSplat) {
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
	
	  Constant* bigConst = getSingleConstant(IVS->Values[i].V);
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

    if(!addIVSToPartialVal(it.value(), FirstReadByte - it.start(), FirstReadByte - Offset, LastReadByte - FirstReadByte, ResultPV, error)) {
      delete ResultPV;
      ResultPV = 0;
      Result.setOverdef();

      if(it.value().SetType == ValSetTypePB || it.value().SetType == ValSetTypeFD) {
	if(FirstReadByte == it.start() && LastReadByte == it.stop()) {

	  // This read would read a whole FD or pointer, but can't because we can't express those
	  // as bytes. It's therefore worth trying again with a more expensive multi descriptor.
	  
	  shouldTryMulti = true;
	  
	}
      }
      else if(!it.value().isWhollyUnknown()) {

	shouldTryMulti = true;
	  
      }

      return;
    }

  }
  
  if((!ResultPV) || !ResultPV->isComplete()) {
      
    // If this is an out-of-bounds read it's legitimate to reach the bottom without resolution:
    if(!IVM->Underlying) {

      if(ResultPV) {
	delete ResultPV;
	ResultPV = 0;
      }

      Result.setOverdef();

    }
    else {

      LFV3(errs() << "Defer to next map: " << IVM->Underlying << "\n");
      readValRangeFrom(V, Offset, Size, ReadBB, IVM->Underlying, Result, ResultPV, shouldTryMulti, error);

    }
      
  }

}

// Try to read V[Offset:Offset+Size], in the context of ReadBB, storing the result in Result or ResultMulti if an extent-list is necessary.
// In debug builds, give a verbose error report as 'error'.
void llvm::readValRange(ShadowValue& V, int64_t Offset, uint64_t Size, ShadowBB* ReadBB, ImprovedValSetSingle& Result, ImprovedValSetMulti** ResultMulti, std::string* error) {

  // Try to make an IVS representing the block-local value of V+Offset -> Size.
  // Limitations for now: because our output is a single IVS, non-scalar types may only be described
  // if they correspond to a whole object.

  LFV3(errs() << "Start read " << Offset << "-" << (Offset + Size) << "\n");

  // Reads from a negative offset are always out of bounds.
  if(Offset < 0) {
    Result.setOverdef();
    return;
  }

  LocStore* firstStore = ReadBB->getReadableStoreFor(V);
  if(!firstStore) {
    if(ReadBB->localStore->allOthersClobbered) {
      LFV3(errs() << "Location not in local map and allOthersClobbered\n");
      Result.setOverdef();
      return;
    }
    else {
      Value* UD = UndefValue::get(Type::getIntNTy(ReadBB->invar->BB->getContext(), Size));
      Result.set(ImprovedVal(ShadowValue(UD)), ValSetTypeScalar);
      return;
    }
  }
  else {
    LFV3(errs() << "Starting at local store\n");
  }

  PartialVal* ResultPV = 0;
  bool shouldTryMulti = false;

  /*  
  if(logReadDepth(firstStore->store, 1) >= 10) {
  
    errs() << "Deep read for " << itcache(V, true) << " from " << ReadBB->invar->BB->getName() << " / " << ReadBB->IA->SeqNumber << "\n";
    firstStore->store->print(errs(), false);

  }
  */

  LocStore::simplifyStore(firstStore);
  
  readValRangeFrom(V, Offset, Size, ReadBB, firstStore->store, Result, ResultPV, shouldTryMulti, error);

  if(ResultPV) {

    LFV3(errs() << "Read used a PV\n");
    Constant* PVConst = PVToConst(*ResultPV, Size, V.getLLVMContext());
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

      ImprovedValSetMulti* IVM = new ImprovedValSetMulti(ReadBB->getAllocSize(V));
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

// Permit implicit pointer typecasts via memory:
bool llvm::allowTotalDefnImplicitCast(Type* From, Type* To) {

  if(From == To)
    return true;

  if(From->isPointerTy() && To->isPointerTy())
    return true;

  return false;

}

// Permit widening ptr-to-int via memory:
bool llvm::allowTotalDefnImplicitPtrToInt(Type* From, Type* To, const DataLayout* TD) {

  return From->isPointerTy() && To->isIntegerTy() && TD->getTypeSizeInBits(To) >= TD->getTypeSizeInBits(From);

}

// Check if we can coerce this value to Target type.
// TODO: Discover problems without running the whole check twice.
bool ImprovedValSetSingle::canCoerceToType(Type* Target, uint64_t TargetSize, std::string* error, bool allowImplicitPtrToInt) {

  ImprovedValSetSingle Copy(*this);
  return Copy.coerceToType(Target, TargetSize, error, allowImplicitPtrToInt);

}

bool ImprovedValSetSingle::coerceToType(Type* Target, uint64_t TargetSize, std::string* error, bool allowImplicitPtrToInt) {

  // All casts ignored for VAs:
  if(SetType == ValSetTypeVarArg)
    return true;
  if(SetType == ValSetTypePB && !onlyContainsNulls())
    return true;

  Type* Source = Values[0].V.getNonPointerType();
  
  // Allow implicit ptrtoint and bitcast between pointer types
  // without modifying anything:
  if(allowTotalDefnImplicitCast(Source, Target))
    return true;
  if(allowImplicitPtrToInt && allowTotalDefnImplicitPtrToInt(Source, Target, GlobalTD))
    return true;

  bool mightWork = (SetType == ValSetTypeScalar || (SetType == ValSetTypePB && onlyContainsNulls()));

  if(!mightWork) {
    if(error)
      *error = "Coercion of value without known bit pattern";
    return false;
  }

  // Finally reinterpret cast each member:
  for(uint32_t i = 0, iend = Values.size(); i != iend; ++i) {

    Constant* FromC = getSingleConstant(Values[i].V);
    if(FromC->getType() == Target)
      continue;

    if(isa<UndefValue>(FromC)) {

      Values[i].V.u.V = UndefValue::get(Target);
      if(Target->isPointerTy())
	SetType = ValSetTypePB;
      else
	SetType = ValSetTypeScalar;
      continue;

    }

    PartialVal PV(TargetSize);
    if(!PV.combineWith(FromC, 0, 0, TargetSize, error))
      return false;

    if(containsPointerTypes(Target)) {

      // If we're trying to synthesise a pointer from raw bytes, only a null pointer is allowed.
      unsigned char* checkBuf = (unsigned char*)PV.partialBuf;
      for(unsigned j = 0; j < PV.partialBufBytes; ++j) {
	
	if(checkBuf[j]) {
	  if(error)
	    *error = "Cast non-zero to pointer";
	  return false;
	}
	
      }

      Values[i].Offset = 0;
      SetType = ValSetTypePB;

    }

    Values[i].V = ShadowValue(constFromBytes((unsigned char*)PV.partialBuf, Target, GlobalTD));

  }

  return true;

}

// Helper to build an IVSRange.
#define IVSR(x, y, z) std::make_pair(std::make_pair(x, y), z)

// Helper to add z[x:x+y] to IVSRange list 'Dest'.
#define AddIVSSV(x, y, z) do { Dest.push_back(IVSR(x + OffsetAbove, x + y + OffsetAbove, ImprovedValSetSingle(ImprovedVal(z), ValSetTypeScalar))); } while(0);

// As above, but turn a constant into a symbolic object first.
#define AddIVSConst(x, y, z) do { std::pair<ValSetType, ImprovedVal> V = getValPB(z); Dest.push_back(IVSR(x + OffsetAbove, x + y + OffsetAbove, ImprovedValSetSingle(V.second, V.first))); } while(0);

static bool mayContainPointers(ImprovedValSet* IV) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IV)) {

    return IVS->SetType == ValSetTypePB || IVS->SetType == ValSetTypeUnknown;

  }

  ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(IV);

  for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {

    const ImprovedValSetSingle& IVS = it.value();
    if(IVS.SetType == ValSetTypePB || IVS.SetType == ValSetTypeUnknown)
      return true;

  }

  return false;

}

// Differentiate the cases of "any scalar" and "any scalar or pointer".
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
  uint64_t PtrSize = GlobalTD->getTypeStoreSize(StoreSI->invar->I->getOperand(0)->getType());

  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();

  ShadowValue Val = StoreSI->getOperand(0);

  // TODO: do better than marking a value as escaped whenever a pointer to it is stored.
  valueEscaped(Val, StoreSI->parent);

  if(ImprovedValSetMulti* IVM = dyn_cast_or_null<ImprovedValSetMulti>(tryGetIVSRef(Val))) {

    if(PtrSet.Values.size() != 1) {

      ImprovedValSetSingle OD = getOverdefFor(IVM);
      executeWriteInst(&Ptr, PtrSet, OD, PtrSize, StoreSI);

    }
    else {

      SmallVector<IVSRange, 4> Vals;
      for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {
	
	Vals.push_back(IVSR(it.start() + PtrSet.Values[0].Offset, it.stop() + PtrSet.Values[0].Offset, it.value()));

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
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();
  
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

bool llvm::executeAtomicRMW(ShadowInstruction* SI, ImprovedValSet*& OldPB, bool& loadedVararg) {
  
  bool ret;

  SI->isThreadLocal = TLS_NEVERCHECK;

  OldPB = newOverdefIVS();

  ShadowValue Ptr = SI->getOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();

  ShadowValue Val = SI->getOperand(1);
  valueEscaped(Val, SI->parent);

  ImprovedValSetSingle ValPB;
  getImprovedValSetSingle(Val, ValPB);

  if(PtrSet.isWhollyUnknown()) {

    // Just clobber everything:
    executeWriteInst(&Ptr, PtrSet, ValPB, Val.getValSize(), SI);
    return true;

  }
  else if(ValPB.isWhollyUnknown() || ValPB.SetType != ValSetTypeScalar) {

    // Overwrite location with overdef:
    executeWriteInst(&Ptr, PtrSet, ValPB, Val.getValSize(), SI);
    return true;

  }

  // Attempt a proper RMW:
  deleteIV(OldPB);
  OldPB = 0;
  ret = SI->parent->IA->tryForwardLoadPB(SI, OldPB, loadedVararg);

  // The tryForwardLoad call may set SI->isThreadLocal if the object we're reading
  // may be global.

  // OldPB is the old value, and what we will return. Now do the RMW:
  if((!isa<ImprovedValSetSingle>(OldPB)) || 
     cast<ImprovedValSetSingle>(OldPB)->isWhollyUnknown() ||
     cast<ImprovedValSetSingle>(OldPB)->SetType != ValSetTypeScalar) {

    ImprovedValSetSingle OD;
    OD.setOverdef();
    executeWriteInst(&Ptr, PtrSet, OD, Val.getValSize(), SI);
    return true;

  }

  ImprovedValSetSingle& LoadedPB = *cast<ImprovedValSetSingle>(OldPB);
  ImprovedValSetSingle StorePB;
  AtomicRMWInst::BinOp Op = cast_inst<AtomicRMWInst>(SI)->getOperation();

  // Constant fold. Ideally I would re-use the code for normal instruction
  // constant folding, but atomicrmw's instruction set is slightly different,
  // e.g. it contains nand, max and min which are not llvm primitives.
  for(uint32_t i = 0, ilim = LoadedPB.Values.size(); i != ilim; ++i) {

    uint64_t op1Val;
    if(!tryGetConstantInt(LoadedPB.Values[i].V, op1Val)) {
      StorePB.setOverdef();
      break;
    }
	 
    for(uint32_t j = 0, jlim = ValPB.Values.size(); j != jlim; ++j) {

      uint64_t op2Val;
      if(!tryGetConstantInt(ValPB.Values[j].V, op2Val)) {
	StorePB.setOverdef();
	break;
      }

      uint64_t newVal;

      switch(Op) {
      case AtomicRMWInst::Xchg:
	newVal = op2Val; break;
      case AtomicRMWInst::Add:
	newVal = op1Val + op2Val; break;
      case AtomicRMWInst::Sub:
	newVal = op1Val - op2Val; break;
      case AtomicRMWInst::And:
	newVal = op1Val & op2Val; break;
      case AtomicRMWInst::Nand:
	newVal = ~(op1Val & op2Val); break;
      case AtomicRMWInst::Or:
	newVal = op1Val | op2Val; break;
      case AtomicRMWInst::Xor:
	newVal = op1Val ^ op2Val; break;
      case AtomicRMWInst::Max: 
      case AtomicRMWInst::Min:
	{
	  int64_t op1S = 0, op2S = 0;
	  tryGetConstantSignedInt(LoadedPB.Values[i].V, op1S);
	  tryGetConstantSignedInt(ValPB.Values[j].V, op2S);
	  if(Op == AtomicRMWInst::Max)
	    newVal = (uint64_t)std::max(op1S, op2S);
	  else
	    newVal = (uint64_t)std::min(op1S, op2S);		
	  break;
	}
      case AtomicRMWInst::UMax:
	newVal = std::max(op1Val, op2Val); break;
      case AtomicRMWInst::UMin:
	newVal = std::min(op1Val, op2Val); break;
      default:
	release_assert(0 && "AtomicRMW doesn't handle all cases!");
	llvm_unreachable("AtomicRMW doesn't handle all cases!");
      }

      ShadowValue NewSV = ShadowValue::getInt(SI->getType(), newVal);
      StorePB.mergeOne(ValSetTypeScalar, ImprovedVal(NewSV));

    }

  }

  executeWriteInst(&Ptr, PtrSet, StorePB, Val.getValSize(), SI);

  return ret;

}

bool llvm::executeCmpXchg(ShadowInstruction* SI, ImprovedValSet*& OldPB, bool& loadedVararg) {

  bool ret;

  SI->isThreadLocal = TLS_NEVERCHECK;
  OldPB = newOverdefIVS();

  ShadowValue Ptr = SI->getOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();

  uint64_t WriteSize = SI->getOperand(2).getValSize();

  if(PtrSet.isWhollyUnknown()) {

    // Just clobber everything:
    ImprovedValSetSingle OD(ValSetTypePB, true);
    executeWriteInst(&Ptr, PtrSet, OD, WriteSize, SI);
    return true;

  }

  deleteIV(OldPB);
  OldPB = 0;
  ret = SI->parent->IA->tryForwardLoadPB(SI, OldPB, loadedVararg);

  // OldPB is now our return value (like atomicrmw, cmpx returns the old value)

  ImprovedValSetSingle StorePB;
  ImprovedValSetSingle* OldIVS = dyn_cast<ImprovedValSetSingle>(OldPB);

  if((!OldIVS) || OldIVS->isWhollyUnknown()) {

    ImprovedValSetSingle OD(ValSetTypePB, true);
    executeWriteInst(&Ptr, PtrSet, OD, WriteSize, SI);
    return ret;

  }

  ImprovedValSetSingle NewIVS;
  ImprovedValSetSingle CmpIVS;
  release_assert(getImprovedValSetSingle(SI->getOperand(1), CmpIVS));

  if(CmpIVS.Values.size() == 1 && OldIVS->Values.size() == 1) {

    if(CmpIVS.Values[0] == OldIVS->Values[0]) {
      
      // Cmpxchg succeeds: write the new value!
      release_assert(getImprovedValSetSingle(SI->getOperand(2), NewIVS));

    }
    else {

      // Cmpxchg fails: nothing to write.
      return ret;

    }
     
  }
  else {

    // Cmpxchg may or may not succeed. Merge values.
    ImprovedValSetSingle ReplIVS;
    release_assert(getImprovedValSetSingle(SI->getOperand(2), ReplIVS));
    NewIVS = *OldIVS;
    NewIVS.merge(ReplIVS);

  }

  executeWriteInst(&Ptr, PtrSet, NewIVS, WriteSize, SI);
  return ret;

}

uint64_t ShadowValue::getValSize() const {

  switch(t) {

  case SHADOWVAL_FDIDX: // int32
    return 4;
  case SHADOWVAL_FDIDX64: // int64
    return 8;
  case SHADOWVAL_PTRIDX:
    return GlobalTD->getPointerSize();
  default:
    Type* SrcTy = getNonPointerType();
    return GlobalTD->getTypeStoreSize(SrcTy);

  }

}

// Read Src[Offset:Offset+Size] into Dest, a list of extents, adding OffsetAbove to all extent offsets.
// This usually means a single extent, but might disintegrate a composite constant into multiple extents.
void llvm::getIVSSubVals(const ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest) {

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
      uint64_t SrcSize = Src.Values[0].V.getValSize();
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
    getConstSubVals(Src.Values[0].V, Offset, Size, OffsetAbove, Dest);

  }
  else {

    // Punt on the tricky business of merging potentially misaligned sets of constants for now; only allow
    // subvalues expressible as a single constant.

    ImprovedValSetSingle DestSingle;

    for(uint32_t i = 0, endi = Src.Values.size(); i != endi; ++i) {
	
      Constant* bigConst = getSingleConstant(Src.Values[i].V);
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

// Try to extract Src[Offset:Offset+Size] into Dest.
void llvm::getIVSSubVal(const ImprovedValSetSingle& Src, uint64_t Offset, uint64_t Size, ImprovedValSetSingle& Dest) {

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
void llvm::getConstSubVals(ShadowValue FromSV, uint64_t Offset, uint64_t TargetSize, int64_t OffsetAbove, SmallVector<IVSRange, 4>& Dest) {

  release_assert(FromSV.isVal() || FromSV.isConstantInt());

  uint64_t FromSize = GlobalTD->getTypeStoreSize(FromSV.getNonPointerType());

  if(Offset == 0 && TargetSize == FromSize) {
    AddIVSSV(0, TargetSize, FromSV);
    return;
  }

  Constant* FromC = getSingleConstant(FromSV);

  if(Offset + TargetSize > FromSize) {

    // Out of bounds read on the right. Define as much as we can:
    getConstSubVals(FromSV, Offset, FromSize - Offset, OffsetAbove, Dest);
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

      getConstSubVals(ShadowValue(CA->getAggregateElement(StartE)), StartOff, ThisReadSize, OffsetAbove + (ESize * StartE), Dest);

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
      getConstSubVals(ShadowValue(CA->getAggregateElement(EndE)), 0, EndOff, OffsetAbove + (ESize * EndE), Dest);

  }
  else if(ConstantStruct* CS = dyn_cast<ConstantStruct>(FromC)) {

    const StructLayout* SL = GlobalTD->getStructLayout(CS->getType());
    if(!SL) {
      LLVM_DEBUG(dbgs() << "Couldn't get struct layout for type " << *(CS->getType()) << "\n");
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
      uint64_t StartCSize = GlobalTD->getTypeStoreSize(StartC->getType());
      uint64_t ThisReadSize;

      if(EndE == StartE)
	ThisReadSize = EndOff - StartOff;
      else
	ThisReadSize = StartCSize - StartOff;

      getConstSubVals(ShadowValue(StartC), StartOff, ThisReadSize, OffsetAbove + SL->getElementOffset(StartE), Dest);

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
      uint64_t ESize = GlobalTD->getTypeStoreSize(E->getType());
      uint64_t ThisOff = SL->getElementOffset(StartE);
      AddIVSConst(ThisOff, ESize, E);

      // Padding?
      if(StartE + 1 < CS->getType()->getNumElements()) {
	uint64_t NextOff = SL->getElementOffset(StartE + 1);
	uint64_t PaddingBytes = (NextOff - (ThisOff + ESize));
	if(PaddingBytes) {

	  Type* PaddingType = Type::getIntNTy(FromC->getContext(), PaddingBytes * 8);
	  Constant* Padding = UndefValue::get(PaddingType);
	  AddIVSConst(ThisOff + ESize, PaddingBytes, Padding);

	}
      }

    }

    // Read final subelement
    if(EndOff) {
      Constant* E = CS->getAggregateElement(EndE);
      getConstSubVals(ShadowValue(E), 0, EndOff, OffsetAbove + SL->getElementOffset(EndE), Dest);
    }

  }
  else if(isa<UndefValue>(FromC)) {

    Type* Target = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
    Constant* SubC = UndefValue::get(Target);
    AddIVSConst(Offset, TargetSize, SubC);

  }
  else {

    // C is a primitive, constant-aggregate-zero, constant-data-array or similar.
    // Attempt bytewise extraction and present as a CDA.
    SmallVector<uint8_t, 16> Buffer(TargetSize);
    if(XXXReadDataFromGlobal(FromC, Offset, Buffer.data(), TargetSize, *GlobalTD)) {

      Constant* SubC;
      if(TargetSize <= 8) {
	Type* Target = Type::getIntNTy(FromC->getContext(), TargetSize * 8);
	SubC = constFromBytes((uint8_t*)Buffer.data(), Target, GlobalTD);
      }
      else
	SubC = ConstantDataArray::get(FromC->getContext(), ArrayRef<uint8_t>(Buffer));

      AddIVSConst(Offset, TargetSize, SubC);
      
    }
    else {

      Dest.push_back(IVSR(Offset, TargetSize, ImprovedValSetSingle(ValSetTypeUnknown, true)));      

    }

  }
  
}

// Try to cast a list of extents into a single constant of type targetType.
Constant* llvm::valsToConst(SmallVector<IVSRange, 4>& subVals, uint64_t TargetSize, Type* targetType) {

  if(subVals.size() == 0)
    return 0;

  for(SmallVector<IVSRange, 4>::iterator it = subVals.begin(), itend = subVals.end();
      it != itend; ++it) {

    if(it->second.isWhollyUnknown())
      return 0;

  }

  if(subVals.size() == 1)
    return getSingleConstant(subVals[0].second.Values[0].V);

  // Otherwise attempt a big synthesis from bytes.
  SmallVector<uint8_t, 16> buffer(TargetSize);

  for(SmallVector<IVSRange, 4>::iterator it = subVals.begin(), itend = subVals.end();
      it != itend; ++it) {

    uint8_t* ReadPtr = &(buffer.data()[it->first.first]);
    if(!XXXReadDataFromGlobal(getSingleConstant(it->second.Values[0].V), 0, ReadPtr, it->first.second - it->first.first, *GlobalTD))
      return 0;

  }

  LLVMContext& Ctx = subVals[0].second.Values[0].V.getLLVMContext();

  if(!targetType) {
    if(TargetSize > 8)
      targetType = ArrayType::get(Type::getInt8Ty(Ctx), TargetSize);
    else
      targetType = Type::getIntNTy(Ctx, TargetSize * 8);
  }

  return constFromBytes((uint8_t*)buffer.data(), targetType, GlobalTD);

}

// Try to extract FromSV[Offset:Offset+TargetSize] into Result, which should have type TargetType.
void llvm::getConstSubVal(ShadowValue FromSV, uint64_t Offset, uint64_t TargetSize, Type* TargetType, ImprovedValSetSingle& Result) {

  release_assert(FromSV.isVal() || FromSV.isConstantInt());

  SmallVector<IVSRange, 4> subVals;
  getConstSubVals(FromSV, Offset, TargetSize, -((int64_t)Offset), subVals);

  if(subVals.size() != 1) {

    if(Constant* C = valsToConst(subVals, TargetSize, TargetType)) {

      std::pair<ValSetType, ImprovedVal> V = getValPB(C);
      Result.mergeOne(V.first, V.second);

    }
    else {

      Result.setOverdef();

    }

  }
  else {

    if(TargetType)
      subVals[0].second.coerceToType(TargetType, TargetSize, 0);

    Result.merge(subVals[0].second);

  }

}

// Try to extract a sub-constant at FromC[Offset:Offset+TargetSize], usually a struct member.
Constant* llvm::getSubConst(Constant* FromC, uint64_t Offset, uint64_t TargetSize, Type* targetType) {
  
  SmallVector<IVSRange, 4> subVals;
  getConstSubVals(ShadowValue(FromC), Offset, TargetSize, -((int64_t)Offset), subVals);

  return valsToConst(subVals, TargetSize, targetType);

}

// Overwrite Target[Offset:Offset+Size] with NewVal. Target is a symbolic memory object;
// ensuring it is writable and resolving pointers etc has already been taken care of here.
void llvm::replaceRangeWithPB(ImprovedValSet* Target, const ImprovedValSetSingle& NewVal, int64_t Offset, uint64_t Size) {

  if(ImprovedValSetSingle* S = dyn_cast<ImprovedValSetSingle>(Target)) {
    *S = NewVal;
  }
  else {
    
    ImprovedValSetMulti* M = cast<ImprovedValSetMulti>(Target);

    if(Size == ULONG_MAX) {

      release_assert(NewVal.Overdef && "Indefinite write with non-clobber value?");
      
    }

    // Out of bounds access? Grow our perception of allocation size.
    if(Offset + Size > M->AllocSize)
      M->AllocSize = Offset + Size;

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

// M is a symbolic memory object. Clear M[Offset:Offset+Size].
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

    // Back up the stop() value here, are some truncateRight paths will adjust it.
    // Also back up start() as the iterator will be moved.
    uint64_t oldStart = found.start();
    uint64_t oldStop = found.stop();

    if(canTruncate(found.value()))
      truncateRight(found, Offset - found.start());
    else {
      ImprovedValSetSingle OD(found.value().SetType, true);
      found.erase();
      M->Map.insert(oldStart, oldStop, OD);
      found = M->Map.find(oldStart);
    }

    // Some truncate paths don't update the value's stop index (e.g. the setOverdef just above)
    // so ensure it is correct here:
    M->CoveredBytes -= (oldStop - Offset);
    found.setStopUnchecked(Offset);

    release_assert(found.start() < found.stop());

    if(RHS.isInitialised()) {

      ImprovedValSetMulti::MapIt replacementStart;      

      ++found;

      // Insert the original value with its original value. This will temporarily produce an invalid
      // interval map (e.g. 0-16: [i32 1, i32 2, i32 3, i32 4] where we're replacing 4-8 will have
      // become 0-4: i32 1, (4-8 blanked), 0-16: [i32 1, i32 2, i32 3, i32 4]; therefore truncateLeft
      // -> truncateConstVal must not do any imap searches.
      // The setStartUnchecked command below will make the map well-formed again.

      found.insert(LastByte, oldStop, RHS);
      found.setStartUnchecked(oldStart);      
      truncateLeft(found, oldStop - LastByte, replacementStart);
      replacementStart.setStartUnchecked(LastByte);
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

    ImprovedValSetMulti::MapIt replacementStart = found;
    uint64_t oldStart = found.start();

    if(canTruncate(found.value()))
      truncateLeft(found, found.stop() - LastByte, replacementStart);
    else {
      ImprovedValSetSingle OD(found.value().SetType, true);
      uint64_t oldStop = found.stop();
      found.erase();
      found.insert(oldStart, oldStop, OD);
      replacementStart = found;
    }

    M->CoveredBytes -= (LastByte - oldStart);
    replacementStart.setStartUnchecked(LastByte);
    release_assert(found.start() < found.stop());

  }

}

// Target is a symbolic memory object. Overwrite Target[Offset:Offset+Size] with extent-list NewVals.
void llvm::replaceRangeWithPBs(ImprovedValSet* Target, const SmallVector<IVSRange, 4>& NewVals, uint64_t Offset, uint64_t Size) {

  if(ImprovedValSetSingle* S = dyn_cast<ImprovedValSetSingle>(Target)) {
    release_assert(NewVals.size() == 1 && Offset == 0);
    *S = NewVals[0].second;
  }
  else {
    
    ImprovedValSetMulti* M = cast<ImprovedValSetMulti>(Target);

    clearRange(M, Offset, Size);
    ImprovedValSetMulti::MapIt it = M->Map.find(Offset);

    for(unsigned i = 0, iend = NewVals.size(); i != iend; ++i) {

      const IVSRange& RangeVal = NewVals[i];
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

// 'it' points to a scalar which is part of some symbolic memory object. Truncate it to leave byte range off - off+size.
// Leave firstPtr pointing to the start and 'it' pointing to the last newly-inserted range.
void llvm::truncateConstVal(ImprovedValSetMulti::MapIt& it, uint64_t off, uint64_t size, ImprovedValSetMulti::MapIt& firstPtr) {

  const ImprovedValSetSingle& S = it.value();
  firstPtr = it;

  // Dodge problem of taking e.g. { complex_val, other_complex_val } that
  // split into multiple values and then recombining: only allow value splitting for singleton sets.
  if(S.Values.size() == 1) {

    SmallVector<IVSRange, 4> SubVals;
    Constant* OldC = getSingleConstant(S.Values[0].V);
    getConstSubVals(ShadowValue(OldC), off, size, /* reporting offset = */ it.start(), SubVals);
    if(SubVals.size() == 1) {
      uint64_t oldStart = it.start(), oldStop = it.stop();
      it.erase();
      it.insert(oldStart, oldStop, SubVals[0].second);
    }
    else {

      // Replace single with several:
      it.erase();

      for(SmallVector<IVSRange, 4>::iterator valit = SubVals.begin(), valend = SubVals.end();
	  valit != valend; ++valit) {

	it.insert(valit->first.first, valit->first.second, valit->second);

	// Record an iterator pointing to the start of the replacement sequence if our caller needs it.
	if(valit == SubVals.begin())
	  firstPtr = it;

	++it;

      }

      --it;
      // Pointer ends up aimed at the last part of the replacement.

    }

    return;

  }

  ImprovedValSetSingle newVal = S;

  for(uint32_t i = 0; i < newVal.Values.size(); ++i) {

    Constant* OldC = getSingleConstant(newVal.Values[i].V);
    Constant* NewC = getSubConst(OldC, off, size);
    if(NewC)
      newVal.Values[i].V = ShadowValue(NewC);
    else {
      newVal.setOverdef();
      break;
    }

  }

  uint64_t oldStart = it.start(), oldStop = it.stop();
  it.erase();
  it.insert(oldStart, oldStop, newVal);

}

// 'it' points into a symbolic memory object. Trim it on the right-hand side to have length 'n'.
void llvm::truncateRight(ImprovedValSetMulti::MapIt& it, uint64_t n) {

  // Remove bytes from the RHS, leaving a value of size n bytes.
  // it points at the current value that should be altered.

  const ImprovedValSetSingle& S = it.value();

  if(S.isWhollyUnknown())
    return;
  if(S.SetType == ValSetTypeScalarSplat) {
    release_assert(S.Values.size() == 1 && "Splat set can't be multivalued");
    ImprovedValSetSingle newVal = S;
    newVal.Values[0].Offset = (int64_t)n;
    uint64_t oldStart = it.start(), oldStop = it.stop();
    it.erase(); // Moves iterator to the right
    it.insert(oldStart, oldStop, newVal); // Moves iterator to point at new entry
    return;
  }

  ImprovedValSetMulti::MapIt ign;
  truncateConstVal(it, 0, n, ign);
  
}

// 'it' points into a symbolic memory object. Trim it on the left-hand side to have length 'n'.
// Leave 'it' pointing at the last and 'firstPtr' pointing at the first new entry in the IVSMulti.
// They can differ e.g. when we break a struct value into fields.
void llvm::truncateLeft(ImprovedValSetMulti::MapIt& it, uint64_t n, ImprovedValSetMulti::MapIt& firstPtr) {

  // Remove bytes from the LHS, leaving a value of size n bytes.
  // it points at the current value that should be altered.

  // On most paths we'll just modify it in place, and so firstPtr will continue to point to the
  // start of the truncated value; however truncateConstVal might break 'it' into several smaller
  // extents and set firstPtr appropriately.
  firstPtr = it;

  const ImprovedValSetSingle& S = it.value();

  if(S.isWhollyUnknown())
    return;
  if(S.SetType == ValSetTypeScalarSplat) {
    release_assert(S.Values.size() == 1 && "Splat value must be single-valued");
    ImprovedValSetSingle newVal = S;
    newVal.Values[0].Offset = (int64_t)n;
    uint64_t oldStart = it.start(), oldStop = it.stop();
    it.erase(); // Moves iterator to the right
    it.insert(oldStart, oldStop, newVal); // Moves iterator to point at new entry    
    return;
  }

  Constant* C = getSingleConstant(S.Values[0].V);
  uint64_t CSize = GlobalTD->getTypeStoreSize(C->getType());
  truncateConstVal(it, CSize - n, n, firstPtr);

}

// Is S suitable to be truncated? For example truncating a pointer is meaningless.
bool llvm::canTruncate(const ImprovedValSetSingle& S) {

  return 
    S.isWhollyUnknown() || 
    S.SetType == ValSetTypeScalar || 
    S.SetType == ValSetTypeScalarSplat;
  
}

// 'store' is a symbolic memory object.
// Read store[Offset:Offset+Size] into extent-list 'Results'.
// ASize is the total size of 'store'. If 'ignoreBelowStore' is set and 'store' is an IVSMulti
//   (which can be a stack of overlaid extent lists), treat 'ignoreBelowStore' as the bottom of the stack.
void llvm::readValRangeMultiFrom(uint64_t Offset, uint64_t Size, ImprovedValSet* store, SmallVector<IVSRange, 4>& Results, ImprovedValSet* ignoreBelowStore, uint64_t ASize) {

  if(!store) {
    
    Value* UD = UndefValue::get(Type::getIntNTy(GInt8->getContext(), Size));
    Results.push_back(IVSR(Offset, Offset + Size, ImprovedValSetSingle(ImprovedVal(ShadowValue(UD)), ValSetTypeScalar)));
    return;

  }

  if(ignoreBelowStore && ignoreBelowStore == store) {
    LFV3(errs() << "Leaving a gap due to threshold store " << ignoreBelowStore << "\n");
    return;
  }

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(store)) {

    if(IVS->SetType == ValSetTypeDeallocated) {

      // Read from a certainly-freed object yields overdef.
      Results.push_back(IVSR(Offset, Offset+Size, ImprovedValSetSingle(ValSetTypeUnknown, true)));

    }
    else if(Offset == 0 && Size == ASize) {
      
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
      
      getIVSSubVals(it.value(), SubvalOffset, SubvalSize, it.start(), Results);
      Offset += SubvalSize;
      Size -= SubvalSize;
      ++it;
		     
    }

    // Process vals that don't overlap on the left, but may on the right:
    while(it != IVM->Map.end() && it.start() < (Offset + Size)) {

      if(it.start() != Offset) {

	release_assert(it.start() > Offset && "Overlapping-on-left should be caught already");
	// Gap -- defer this bit to our parent map. If there is none, the value is undefined here.

	if(!IVM->Underlying) {

	  uint64_t UndefSize = it.start() - Offset;
	  Type* UndefType = IntegerType::get(GInt8Ptr->getContext(), UndefSize * 8);
	  Value* UD = UndefValue::get(UndefType);
	  Results.push_back(IVSR(Offset, Offset + UndefSize, ImprovedValSetSingle(ImprovedVal(UD), ValSetTypeScalar)));

	}
	else {

	  LFV3(errs() << "Defer to underlying map " << IVM->Underlying << " for range " << Offset << "-" << it.start() << "\n");
	  readValRangeMultiFrom(Offset, it.start() - Offset, IVM->Underlying, Results, ignoreBelowStore, ASize);

	}

	Size -= (it.start() - Offset);
	Offset = it.start();
	
      }

      if(it.stop() > (Offset + Size)) {

	LFV3(errs() << "Add val at " << it.start() << "-" << it.stop() << " subval " << "0-" << Size << "\n");

	// Overlap on the right: extract sub-val.
	getIVSSubVals(it.value(), 0, Size, it.start(), Results);
	Offset += Size;
	Size = 0;
	break;

      }
      else {

	LFV3(errs() << "Add whole val at " << it.start() << "-" << it.stop() << "\n");

	// No overlap: use whole value.
	Results.push_back(IVSR(it.start(), it.stop(), it.value()));
	Offset += (it.stop() - it.start());
	Size -= (it.stop() - it.start());
	++it;

      }

    }

    // Check for gap on the right:
    if(Size != 0) {

      if(!IVM->Underlying) {

	// No underlying map means undefined value below.
	uint64_t UndefSize = Size - Offset;
	Type* UndefType = IntegerType::get(GInt8Ptr->getContext(), UndefSize * 8);
	Value* UD = UndefValue::get(UndefType);
	Results.push_back(IVSR(Offset, Offset + Size, ImprovedValSetSingle(ImprovedVal(UD), ValSetTypeScalar)));	
	
      }
      else {

	LFV3(errs() << "Defer to underlying map " << IVM->Underlying << " for range " << Offset << "-" << (Offset+Size) << " (end path)\n");      
	readValRangeMultiFrom(Offset, Size, IVM->Underlying, Results, ignoreBelowStore, ASize);

      }

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

      getConstSubVals(ShadowValue(G->G->getInitializer()), Offset, Size, 0, Results);
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
      Value* UD = UndefValue::get(Type::getIntNTy(ReadBB->invar->BB->getContext(), Size));
      Results.push_back(IVSR(Offset, Offset+Size, ImprovedValSetSingle(ImprovedVal(ShadowValue(UD)), ValSetTypeScalar)));
      return;
    }
  }
  else {
    LFV3(errs() << "Starting at local store\n");
  }

  readValRangeMultiFrom(Offset, Size, firstStore->store, Results, 0, ReadBB->getAllocSize(V));

}

void llvm::executeMemcpyInst(ShadowInstruction* MemcpySI) {

  ShadowValue Ptr = MemcpySI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();

  ConstantInt* LengthCI = dyn_cast_or_null<ConstantInt>(getConstReplacement(MemcpySI->getCallArgOperand(2)));

  ShadowValue SrcPtr = MemcpySI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  if(!(SrcPtrSet.isWhollyUnknown() || SrcPtrSet.SetType == ValSetTypePB))
    SrcPtrSet.setOverdef();

  executeCopyInst(&Ptr, PtrSet, SrcPtrSet, LengthCI ? LengthCI->getLimitedValue() : ULONG_MAX, MemcpySI);

}

void llvm::executeVaCopyInst(ShadowInstruction* SI) {
  
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();
  
  ShadowValue SrcPtr = SI->getCallArgOperand(1);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Memcpy from uninitialised PB?");
  if(!(SrcPtrSet.isWhollyUnknown() || SrcPtrSet.SetType == ValSetTypePB))
    SrcPtrSet.setOverdef();
  
  executeCopyInst(&Ptr, PtrSet, SrcPtrSet, 24, SI);

}

void llvm::executeAllocInst(ShadowInstruction* SI, AllocData& AD, Type* AllocType, uint64_t AllocSize, int32_t frame, uint32_t idx) {

  // Represent the store by a big undef value at the start, or if !AllocType (implying AllocSize
  // == ULONG_MAX, unknown size), start with a big Overdef.
 
  ImprovedValSetSingle* initVal;

  if(AllocType) {
    Constant* Undef = UndefValue::get(AllocType);
    ImprovedVal IV(ShadowValue(Undef), 0);
    initVal = new ImprovedValSetSingle(IV, ValSetTypeScalar);
  }
  else {
    initVal = new ImprovedValSetSingle(ValSetTypeUnknown, true);
  }
  
  ShadowValue AllocSV = ShadowValue::getPtrIdx(frame, idx);
  LocStore& localStore = *SI->parent->getWritableStoreFor(AllocSV, 0, AllocSize, /* willWriteSingle = */ true);
  localStore.store->dropReference();
  localStore.store = initVal;

  AD.storeSize = AllocSize;
  // AD.allocIdx was already set by our caller.
  AD.allocVague = false;
  AD.allocTested = AllocUnchecked;
  AD.allocValue = ShadowValue(SI);
  AD.isCommitted = false;
  AD.allocType = SI->getType();

  // Note that the new object is unreachable from old objects, thread-local and unescaped.
  SI->parent->localStore = SI->parent->localStore->getWritableFrameList();
  SI->parent->localStore->es.noAliasOldObjects.insert(AllocSV);
  SI->parent->localStore->es.threadLocalObjects.insert(AllocSV);
  SI->parent->localStore->es.unescapedObjects.insert(AllocSV);

  ImprovedValSetSingle* NewIVS = newIVS();
  SI->i.PB = NewIVS;
  NewIVS->set(ImprovedVal(AllocSV, 0), ValSetTypePB);

}

static void markVagueAllocation(ShadowInstruction* SI) {

  ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(SI->i.PB);
  release_assert(SI->i.PB && isa<ImprovedValSetSingle>(SI->i.PB) && IVS->SetType == ValSetTypePB);
  IVS->Values[0].V.getAllocData(SI->parent->localStore)->allocVague = true;
  //errs() << "Allocation " << itcache(SI) << " in " << SI->parent->IA->SeqNumber << " vague\n";

}

void llvm::executeAllocaInst(ShadowInstruction* SI) {

  // If the store is already initialised this must represent the general case of an allocation
  // within a loop or recursive call.

  // Don't mark allocas vague unless they occur within a function-local loop:
  // because they are deallocated on function exit, a pointer always refers to the latest
  // version of this instruction.
  // Compare a malloc in a similar situation: if we have while(dyn) { f(); } where f() calls malloc,
  // that object may refer to any f in the unbounded loop, not just the most recent call.
  
  if(SI->i.PB) {
    if(SI->parent->invar->naturalScope != 0)
      markVagueAllocation(SI);
    return;
  }

  AllocaInst* AI = cast_inst<AllocaInst>(SI);
  Type* allocType = AI->getAllocatedType();

  if(AI->isArrayAllocation()) {

    ConstantInt* N = cast_or_null<ConstantInt>(getConstReplacement(AI->getArraySize()));
    if(!N) 
      allocType = 0;
    else
      allocType = ArrayType::get(allocType, N->getLimitedValue());

  }

  InlineAttempt* parentIA = SI->parent->IA->getFunctionRoot();
  uint32_t allocIdx = parentIA->localAllocas.size();
  parentIA->localAllocas.push_back(AllocData());  
  AllocData& AD = parentIA->localAllocas.back();
  AD.allocIdx = allocIdx;
  
  executeAllocInst(SI, AD, allocType, allocType ? GlobalTD->getTypeStoreSize(allocType) : ULONG_MAX, parentIA->stack_depth, allocIdx);

}

AllocData& llvm::addHeapAlloc(ShadowInstruction* SI) {

  uint32_t allocIdx = GlobalIHP->heap.size();
  GlobalIHP->heap.push_back(AllocData());
  GlobalIHP->heap.back().allocIdx = allocIdx;
  return GlobalIHP->heap.back();

}

static void executeMallocInst2(ShadowInstruction* SI, AllocatorFn& param) {

  if(SI->i.PB) {
    markVagueAllocation(SI);
    return;
  }

  ConstantInt* AllocSize;
  if(param.isConstantSize)
    AllocSize = param.allocSize;
  else
    AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(param.sizeArg)));
  Type* allocType = 0;
  if(AllocSize)
    allocType = ArrayType::get(Type::getInt8Ty(SI->invar->I->getContext()), AllocSize->getLimitedValue());

  SI->parent->IA->noteMalloc(SI);

  AllocData& AD = addHeapAlloc(SI);
  executeAllocInst(SI, AD, allocType, AllocSize ? AllocSize->getLimitedValue() : ULONG_MAX, -1, GlobalIHP->heap.size() - 1);
  
}

void llvm::executeMallocLikeInst(ShadowInstruction* SI) {

  Function* F = getCalledFunction(SI);
  return executeMallocInst2(SI, GlobalIHP->allocatorFunctions[F]);

}

void llvm::executeFreeInst(ShadowInstruction* SI, Function* FreeF) {

  DeallocatorFn& De = GlobalIHP->deallocatorFunctions[FreeF];

  ShadowInstruction* FreedPtr = SI->getCallArgOperand(De.arg).getInst();
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

  executeWriteInst(0, *FreedIVS, TagIVS, SI->parent->getAllocSize(FreedIVS->Values[0].V), SI);

}

void llvm::executeReallocInst(ShadowInstruction* SI, Function* F) {

  ReallocatorFn& Re = GlobalIHP->reallocatorFunctions[F];

  if(!SI->i.PB) {
    
    // Only alloc the first time; always carry out the copy implied by realloc.
    ConstantInt* AllocSize = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(Re.sizeArg)));
    Type* allocType = 0;
    if(AllocSize)
      allocType = ArrayType::get(Type::getInt8Ty(SI->invar->I->getContext()), AllocSize->getLimitedValue());

    SI->parent->IA->noteMalloc(SI);

    AllocData& AD = addHeapAlloc(SI);
    executeAllocInst(SI, AD, allocType, AllocSize ? AllocSize->getLimitedValue() : ULONG_MAX, -1, GlobalIHP->heap.size() - 1);

  }
  else {

    markVagueAllocation(SI);

  }

  ShadowValue SrcPtr = SI->getCallArgOperand(Re.ptrArg);
  ImprovedValSetSingle SrcPtrSet;
  release_assert(getImprovedValSetSingle(SrcPtr, SrcPtrSet) && "Realloc from uninitialised PB?");
  if(!(SrcPtrSet.isWhollyUnknown() || SrcPtrSet.SetType == ValSetTypePB))
    SrcPtrSet.setOverdef();
  uint64_t CopySize = ULONG_MAX;

  if(SrcPtrSet.isWhollyUnknown() || SrcPtrSet.Values.size() > 1) {

    // Overdef the realloc.
    SrcPtrSet.setOverdef();

  }
  else {

    CopySize = SI->parent->getAllocSize(SrcPtrSet.Values[0].V);

  }

  ImprovedValSetSingle* ThisInst = cast<ImprovedValSetSingle>(SI->i.PB);

  executeCopyInst(0, *ThisInst, SrcPtrSet, CopySize, SI);
  // Release the realloc'd location.
  executeFreeInst(SI, getCalledFunction(SI));

}

// Could reintroduce this for more robust consistency-checking.

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

// Write extent-list copyValues through to (*Ptr)[Offset:Offset+Size], in the context of BB.

void llvm::writeExtents(SmallVector<IVSRange, 4>& copyValues, ShadowValue& Ptr, int64_t Offset, uint64_t Size, ShadowBB* BB) {

  LocStore* Store = BB->getWritableStoreFor(Ptr, Offset, Size, copyValues.size() == 1);
  release_assert(Store && "Non-writable location in writeExtents?");
  replaceRangeWithPBs(Store->store, copyValues, (uint64_t)Offset, Size);
  checkStore(Store->store, Ptr);


}

void llvm::executeCopyInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& SrcPtrSet, uint64_t Size, ShadowInstruction* CopySI) {

  ShadowBB* BB = CopySI->parent;

  LFV3(errs() << "Start copy inst\n");

  GlobalIHP->memcpyValues.erase(CopySI);

  // No need to check the copy instruction is as expected in any of the coming failure cases.
  CopySI->isThreadLocal = TLS_NEVERCHECK;

  if(Size == ULONG_MAX || 
     PtrSet.isWhollyUnknown() || 
     PtrSet.Values.size() != 1 ||
     PtrSet.Values[0].Offset == LLONG_MAX ||
     SrcPtrSet.isWhollyUnknown() || 
     SrcPtrSet.Values.size() != 1 || 
     SrcPtrSet.Values[0].Offset == LLONG_MAX) {

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

	  if(SrcPtrSet.Values[i].V.isNullPointer())
	    continue;

	  LocStore* store = BB->getReadableStoreFor(Obj);
	  if(store && mayContainPointers(store->store))
	    foundPointers = true;

	}
	
      }

      if(!foundPointers)
	OD.SetType = ValSetTypeScalar;

    }

    executeWriteInst(Ptr, PtrSet, OD, Size, CopySI);
    return;

  }

  if(SrcPtrSet.Values[0].V.isNullPointer())
    return;

  if(PtrSet.Values[0].V.isNullPointer())
    return;

  // Now dependent on the source location's value.
  BB->IA->noteDependency(SrcPtrSet.Values[0].V);

  CopySI->isThreadLocal = 
    BB->localStore->es.threadLocalObjects.count(SrcPtrSet.Values[0].V) ? 
    TLS_NEVERCHECK : TLS_MUSTCHECK;

  SmallVector<IVSRange, 4>& copyValues = GlobalIHP->memcpyValues[CopySI];

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

void llvm::executeVaStartInst(ShadowInstruction* SI) {

  LFV3(errs() << "Start va_start inst\n");

  ShadowBB* BB = SI->parent;
  ShadowValue Ptr = SI->getCallArgOperand(0);
  ImprovedValSetSingle PtrSet;

  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB?");
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();

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

  LocStore* Store = BB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, 24, false);
  release_assert(Store && "Non-writable location in executeVaStartInst?");
  replaceRangeWithPBs(Store->store, vaStartVals, (uint64_t)PtrSet.Values[0].Offset, 24);
  checkStore(Store->store, PtrSet.Values[0].V);

}

void llvm::executeReadInst(ShadowInstruction* ReadSI, std::string& Filename, uint64_t FileOffset, uint64_t Size) {

  LFV3(errs() << "Start read inst\n");

  ShadowValue Ptr = ReadSI->getCallArgOperand(1);
  ImprovedValSetSingle PtrSet;
  release_assert(getImprovedValSetSingle(Ptr, PtrSet) && "Write through uninitialised PB (read)?");
  if(!(PtrSet.isWhollyUnknown() || PtrSet.SetType == ValSetTypePB))
    PtrSet.setOverdef();

  ImprovedValSetSingle WriteIVS;
  
  if(PtrSet.isWhollyUnknown() || PtrSet.Values.size() != 1) {

    WriteIVS.setOverdef();

  }
  else {

    std::vector<Constant*> constBytes;
    std::string errors;
    LLVMContext& Context = Ptr.getLLVMContext();
    if(getFileBytes(Filename, FileOffset, Size, constBytes, Context,  errors)) {
      ArrayType* ArrType = ArrayType::get(IntegerType::get(Context, 8), constBytes.size());
      Constant* ByteArray = ConstantArray::get(ArrType, constBytes);
      WriteIVS = ImprovedValSetSingle(ImprovedVal(ByteArray, 0), ValSetTypeScalar);
    }

  }

  executeWriteInst(&Ptr, PtrSet, WriteIVS, Size, ReadSI);

}

DenseMap<Function*, specialfunctions> llvm::SpecialFunctionMap;

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
  if(Function* F6 = M.getFunction("integrator_same_object"))
    SpecialFunctionMap[F6] = SF_SAMEOBJECT;

}

// Can Ptr alias objects that existed before the specialisation root was entered?
static bool containsOldObjects(ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(Ptr.SetType != ValSetTypePB)
    return false;

  for(uint32_t i = 0, ilim = Ptr.Values.size(); i != ilim; ++i) {

    if(!BB->localStore->es.noAliasOldObjects.count(Ptr.Values[i].V))    
      return true;

  }

  return false;

}

// Can Ptr alias objects visible to other threads?
static bool containsGlobalObjects(ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(Ptr.SetType != ValSetTypePB)
    return false;

  for(uint32_t i = 0, ilim = Ptr.Values.size(); i != ilim; ++i) {

    if(!BB->localStore->es.threadLocalObjects.count(Ptr.Values[i].V))
      return true;
    
  }
  
  return false;

}

// A visitor that walks over objects reachable through a particular pointer, set of pointers or extent-list containing pointers.
struct ReachableObjectVisitor {

  SmallSet<ShadowValue, 8> seenObjects;

  virtual void visitPtr(const ImprovedValSetSingle& Ptr, ShadowBB* BB) { }
  virtual bool visitObject(const ShadowValue& Obj, ShadowBB* BB) { return true; }
  virtual bool shouldContinue() { return true; }

};

static void visitReachableObjects(const ImprovedValSetSingle& Ptr, ShadowBB* BB, ReachableObjectVisitor& V);

static void visitReachableObjects(const ImprovedValSet* Obj, ShadowBB* BB, ReachableObjectVisitor& V) {

  if(const ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(Obj)) {

    visitReachableObjects(*IVS, BB, V);

  }
  else {

    const ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(Obj);
    for(ImprovedValSetMulti::ConstMapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it) {

      visitReachableObjects(it.value(), BB, V);

    }

  }

}

static bool isFunction(const Value* V) {

  if(const GlobalValue* GV = dyn_cast<GlobalValue>(V))
    return isa<Function>(getUnderlyingGlobal(GV));
  else
    return false;

}

static void visitReachableObjects(const ImprovedValSetSingle& Ptr, ShadowBB* BB, ReachableObjectVisitor& V) {

  V.visitPtr(Ptr, BB);
  if(!V.shouldContinue())
    return;

  if(Ptr.isWhollyUnknown() || Ptr.SetType != ValSetTypePB)
    return;

  for(uint32_t i = 0, ilim = Ptr.Values.size(); i != ilim; ++i) {

    const ShadowValue& ThisPtr = Ptr.Values[i].V;

    switch(ThisPtr.t) {
    case SHADOWVAL_GV:
      if(ThisPtr.u.GV->G->isConstant())
	continue;
      break;
    case SHADOWVAL_OTHER:
      release_assert(ThisPtr.isNullPointer() || isa<UndefValue>(ThisPtr.u.V) || isFunction(ThisPtr.u.V));
      continue;
    default:
      break;
    }

    if(!V.seenObjects.insert(Ptr.Values[i].V).second)
      continue;

    if(!V.visitObject(Ptr.Values[i].V, BB))
      continue;

    LocStore* store = BB->getReadableStoreFor(Ptr.Values[i].V);
    if(store)
      visitReachableObjects(store->store, BB, V);

  }

}

// Visitor that determines whether Ptr could point to anything allocated since the specialisation root was entered
// (informally, 'new' objects, cf. 'old' objects that were allocated beforehand and are reachable
// through arguments to the root function or globals).
// If 'ignoreOldObjects' is set, determine whether it could refer to any object new or old.
struct ReachesAllPointersVisitor : public ReachableObjectVisitor {

  bool mayReachAll;
  bool ignoreOldObjects;
  ReachesAllPointersVisitor(bool ignoreOld) : mayReachAll(false), ignoreOldObjects(ignoreOld) { }

  virtual void visitPtr(const ImprovedValSetSingle& Ptr, ShadowBB* BB) {

    if(Ptr.isWhollyUnknown()) {
      if((!ignoreOldObjects) || !Ptr.isOldValue())
	mayReachAll = true;
    }

  }

  virtual bool shouldContinue() {   
    return !mayReachAll;
  }

};

static bool reachesAllPointers(const ImprovedValSetSingle& Ptr, ShadowBB* BB, bool ignoreOldObjects) {

  ReachesAllPointersVisitor V(ignoreOldObjects);
  visitReachableObjects(Ptr, BB, V);
  return V.mayReachAll;

}

// Visitor that notes anything reachable from Obj may alias old allocations.
struct SetMAOVisitor : public ReachableObjectVisitor {

  virtual bool visitObject(const ShadowValue& Obj, ShadowBB* BB) { 

    // Don't explore objects reachable this way, it's already known MAO
    if(!BB->localStore->es.noAliasOldObjects.count(Obj))
      return false;

    BB->localStore = BB->localStore->getWritableFrameList();
    BB->localStore->es.noAliasOldObjects.erase(Obj);

    return true;

  }

};

static void setObjectsMayAliasOld(const ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(reachesAllPointers(Ptr, BB, true)) {
    BB->setAllObjectsMayAliasOld();
    return;
  }
  
  SetMAOVisitor V;
  visitReachableObjects(Ptr, BB, V);

}

static void setValueMayAliasOld(ShadowValue V, ShadowBB* BB) {

  if(ImprovedValSetMulti* IVM = dyn_cast_or_null<ImprovedValSetMulti>(tryGetIVSRef(V))) {

    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it)
      setObjectsMayAliasOld(it.value(), BB);

  }
  else {
    
    ImprovedValSetSingle IVS;
    getImprovedValSetSingle(V, IVS);
    setObjectsMayAliasOld(IVS, BB);

  }

}

// Visitor and associated functions to set objects thread-global.
struct SetTGVisitor : public ReachableObjectVisitor {

  virtual bool visitObject(const ShadowValue& Obj, ShadowBB* BB) { 

    // Don't explore objects reachable this way
    if(!BB->localStore->es.threadLocalObjects.count(Obj))
      return false;
    
    BB->localStore = BB->localStore->getWritableFrameList();
    BB->localStore->es.threadLocalObjects.erase(Obj);

    return true;

  }

};

static void setObjectsThreadGlobal(const ImprovedValSetSingle& Ptr, ShadowBB* BB) {

  if(reachesAllPointers(Ptr, BB, false)) {
    BB->setAllObjectsThreadGlobal();
    return;
  }
  
  SetTGVisitor V;
  visitReachableObjects(Ptr, BB, V);

}


static void setValueThreadGlobal(ShadowValue V, ShadowBB* BB) {

  if(ImprovedValSetMulti* IVM = dyn_cast_or_null<ImprovedValSetMulti>(tryGetIVSRef(V))) {

    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it)
      setObjectsThreadGlobal(it.value(), BB);

  }
  else {
    
    ImprovedValSetSingle IVS;
    getImprovedValSetSingle(V, IVS);
    setObjectsThreadGlobal(IVS, BB);

  }

}

// Clobber syscall F's written arguments.
bool llvm::clobberSyscallModLocations(Function* F, ShadowInstruction* SI) {

  if(const IHPFunctionInfo* FI = GlobalIHP->getMRInfo(F)) {

    // System calls cannot throw
    release_assert(inst_is<CallInst>(SI));

    if(FI->NoModRef)
      return true;
      
    const IHPLocationMRInfo *Details = 0;

    if(FI->LocationDetails)
      Details = FI->LocationDetails;
    else if(FI->getLocationDetailsFor)
      Details = FI->getLocationDetailsFor(ShadowValue(SI));

    if(!Details)
      return false;

    for (unsigned i = 0; Details[i].Location; ++i) {

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

    CallInst * CI;
    if((CI = dyn_cast_inst<CallInst>(SI)) && GlobalIHP->pessimisticLocks.count(CI)) {

      // A pessimistic lock clobbers the domain over which it operates.
      // If one is specified, clobber those objects; otherwise just return false
      // to clobber everything.
      // Optimistic locks have no effect here and are accounted for in the
      // tentative loads phase.

      SmallDenseMap<CallInst*, std::vector<GlobalVariable*>, 4>::iterator findit =
	GlobalIHP->lockDomains.find(CI);
      if(findit != GlobalIHP->lockDomains.end()) {

	ImprovedValSetSingle OD(ValSetTypeUnknown, true);

	for(std::vector<GlobalVariable*>::iterator it = findit->second.begin(),
	      itend = findit->second.end(); it != itend; ++it) {

	  ShadowGV* SGV = &GlobalIHP->shadowGlobals[GlobalIHP->getShadowGlobalIndex(*it)];
	  ShadowValue ClobberV(SGV);
	  ImprovedValSetSingle ClobberIVS;
	  ClobberIVS.set(ImprovedVal(ClobberV, LLONG_MAX), ValSetTypePB);
	  executeWriteInst(0, ClobberIVS, OD, MemoryLocation::UnknownSize, SI);

	}

      }
      else {

	// Clobber all objects.
	return false;

      }

    }

    // TODO: introduce a category for functions that actually do this.
    /*
      if(GlobalIHP->yieldFunctions.count(F))
      SI->parent->clobberGlobalObjects();
    */

    return true;

  }
  else if(GlobalIHP->yieldFunctions.count(F)) {

    // Temporary hack: unannotated yields don't clobber.
    return true;

  }

  return false;

}

// Run call instruction SI which refers to a callee not available as bitcode.
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
	  executeMallocLikeInst(SI);
	  break;
	case SF_REALLOC:
	  executeReallocInst(SI, F);
	  break;
	case SF_FREE:
	  executeFreeInst(SI, F);
	  break;
	case SF_VASTART:
	  executeVaStartInst(SI);
	  break;
	case SF_VACOPY:
	  executeVaCopyInst(SI);
	  break;
	case SF_SAMEOBJECT:
	  executeSameObject(SI);
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

    if(SI->i.PB)
      deleteIV(SI->i.PB);

    std::pair<ValSetType, ImprovedVal> PathVal;
    if(SI->parent->IA->tryGetAsDefPathValue(ShadowValue(SI), SI->parent, PathVal)) {
      // Even unexpandable calls like syscalls can have path values:
      ImprovedValSetSingle* NewIVS = newIVS();
      NewIVS->set(PathVal.second, PathVal.first);
      SI->i.PB = NewIVS;
    }
    else {
      // All other annotated calls return an unknown value:
      SI->i.PB = newOverdefIVS();
    }

    // See if we can discard the call because it's annotated read-only:
    if(F->onlyReadsMemory())
      return;

    // The function might cause unwinding if it isn't explicitly annotated to the contrary:
    if(!F->doesNotThrow())
      SI->parent->IA->mayUnwind = true;

    // Do selective clobbering for annotated syscalls:

    if(clobberSyscallModLocations(F, SI))
      return;

  }
  else {

    // Unknown calls return unknown
    if(SI->i.PB)
      deleteIV(SI->i.PB);
    SI->i.PB = newOverdefIVS();

  }

  bool clobbersMemory = true;
  
  // An assembly section is harmless if it doesn't clobber memory, or if it
  // doesn't contain any instructions and is thus just a fence.

  InlineAsm* ASM;
  if(inst_is<CallInst>(SI) && 
     (ASM = dyn_cast_or_null<InlineAsm>(cast<CallInst>(SI->invar->I)->getCalledValue())) && 
     ((!ASM->hasSideEffects()) || ASM->getAsmString().size() == 0)) {

    clobbersMemory = false;

  }

  if(clobbersMemory) {

    // Finally clobber all locations; this call is entirely unhandled
    //errs() << "Warning: unhandled call to " << itcache(SI) << " clobbers all locations\n";
    ImprovedValSetSingle OD(ValSetTypeUnknown, true);
    executeWriteInst(0, OD, OD, MemoryLocation::UnknownSize, SI);
    // Functions that clobber FD state happen to be the same.
    FDStore* FDS = SI->parent->getWritableFDStore();
    FDS->fds.clear();
    
  }
    
  // Args to an unhandled call escape, may be stored in old object, and may be visible from other threads.
  for(uint32_t i = 0, ilim = SI->getNumArgOperands(); i != ilim; ++i) {
    
    ShadowValue Op = SI->getCallArgOperand(i);
    valueEscaped(Op, SI->parent);
    setValueMayAliasOld(Op, SI->parent);
    setValueThreadGlobal(Op, SI->parent);

  }

}

void ShadowBB::setAllObjectsMayAliasOld() {

  localStore = localStore->getWritableFrameList();

  DenseSet<ShadowValue>* preservePtr[1] = { &localStore->es.unescapedObjects };

  intersectSets(&localStore->es.noAliasOldObjects,
		MutableArrayRef<DenseSet<ShadowValue>* >(preservePtr));

}

void ShadowBB::setAllObjectsThreadGlobal() {

  localStore = localStore->getWritableFrameList();

  // Preserve unescaped objects from losing their thread-local status.
  
  DenseSet<ShadowValue>* preservePtr[1] = { &localStore->es.unescapedObjects };

  intersectSets(&localStore->es.threadLocalObjects, 
		MutableArrayRef<DenseSet<ShadowValue>* >(preservePtr));

}

// Clobber (overwrite with unknown) everything except the object-set Save.
// This is used when e.g. writing through an unknown pointer, but one which is known
// not to alias objects that predate specialistion, or not to alias unescaped
// thread-local objects, or...
void ShadowBB::clobberAllExcept(DenseSet<ShadowValue>& Save, bool verbose) {

  std::vector<std::pair<ShadowValue, ImprovedValSet*> > SaveVals;

  for(DenseSet<ShadowValue>::iterator it = Save.begin(), itend = Save.end(); it != itend; ++it) {

    LocStore* CurrentVal = getReadableStoreFor(*it);
    if(!CurrentVal)
      CurrentVal = &LocStore::getEmptyStore();
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
  clobberAllExcept(localStore->es.noAliasOldObjects, verbose);
  if(verbose)
    errs() << "---\n\n";

}

void ShadowBB::clobberGlobalObjects() {
  
  bool verbose = false;
  if(verbose)
    errs() << "Clobber global objects at " << invar->BB->getName() << ":\n";
  clobberAllExcept(localStore->es.threadLocalObjects, verbose);
  if(verbose)
    errs() << "---\n\n";
  
}

// Has V escaped? At the moment this means has it been written anywhere
// but the initial allocation site?
static void pointerEscaped(const ShadowValue V, ShadowBB* BB) {

  if(BB->localStore->es.unescapedObjects.count(V)) {

    BB->localStore = BB->localStore->getWritableFrameList();
    BB->localStore->es.unescapedObjects.erase(V);

  }

}

static void IVSEscaped(const ImprovedValSetSingle* IVS, ShadowBB* BB) {

  if(IVS->isWhollyUnknown() || IVS->SetType != ValSetTypePB)
    return;
  
  for(uint32_t i = 0, ilim = IVS->Values.size(); i != ilim; ++i)
    pointerEscaped(IVS->Values[i].V, BB);
  
}

void llvm::valueEscaped(ShadowValue V, ShadowBB* BB) {

  std::pair<ValSetType, ImprovedVal> IV;
  ImprovedValSet* IVS;
  getIVOrSingleVal(V, IVS, IV);

  if(IVS) {

    if(ImprovedValSetSingle* IVSS = dyn_cast<ImprovedValSetSingle>(IVS)) {
      
      IVSEscaped(IVSS, BB);

    }
    else {

      ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(IVS);
      for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end(); it != itend; ++it)
	IVSEscaped(&(it.value()), BB);

    }
  
  }
  else {

    if(IV.first == ValSetTypePB)
      pointerEscaped(IV.second.V, BB);

  }

}

// Note that SI is a barrier to specialisation, usually because it
// might clobber all of memory. This is used in the GUI to highlight
// specialisation obstacles.
void llvm::noteBarrierInst(ShadowInstruction* SI) {

  GlobalIHP->barrierInstructions.insert(SI);
  SI->parent->IA->barrierState = BARRIER_HERE;

}

// 'Other' is a child context of this one. Inherit problems from it
// (potential clobbering instructions, thread yield points, exception sources)
void IntegrationAttempt::inheritDiagnosticsFrom(IntegrationAttempt* Other) {

  if(Other->barrierState != BARRIER_NONE && barrierState == BARRIER_NONE)
    barrierState = BARRIER_CHILD;
  if(Other->yieldState != BARRIER_NONE && yieldState == BARRIER_NONE)
    yieldState = BARRIER_CHILD;
  mayUnwind |= Other->mayUnwind;

}

// Is V a 'vague' allocation? This means might instruction instance V run more than once,
// e.g. if it is an allocation instruction within an unexpanded loop?
// (compare the case where the loop is unrolled and each iteration considered individually)
static bool isVagueAllocation(ShadowValue V, ShadowBB* CtxBB) {

  switch(V.t) {

  case SHADOWVAL_ARG:
  case SHADOWVAL_OTHER:
  case SHADOWVAL_GV:
    // Always single objects, or non-object pointers such as nulls.
    return false;

  case SHADOWVAL_PTRIDX:
    return V.getAllocData(CtxBB->localStore)->allocVague;
    
  default:
    llvm_unreachable("Bad SV type in isVagueAllocation");
    return false;

  }

}

// Top write-instruction entry point. ValPB is written through PtrSet by instruction WriteSI
// (which may be null if the write does not orginate from an instruction)
void llvm::executeWriteInst(ShadowValue* Ptr, ImprovedValSetSingle& PtrSet, ImprovedValSetSingle& ValPB, uint64_t PtrSize, ShadowInstruction* WriteSI) {

  ShadowBB* StoreBB = WriteSI->parent;

  if(!ValPB.isInitialised())
    ValPB.setOverdef();

  checkIVSNull(ValPB);

  // Perform the store

  if(PtrSet.isWhollyUnknown()) {
    
    if(PtrSet.isOldValue()) {

      StoreBB->clobberMayAliasOldObjects();

    }
    else {
      
      // Start with a plain local store map giving no locations except unescaped objects that cannot alias this one.
      noteBarrierInst(WriteSI);
      StoreBB->clobberAllExcept(StoreBB->localStore->es.unescapedObjects, false);
      LFV3(errs() << "Write through overdef; local map " << StoreBB->localStore << " clobbered\n");

    }

  }
  else if(PtrSet.Values.size() == 1 && 
	  PtrSet.Values[0].Offset != LLONG_MAX && 
	  !isVagueAllocation(PtrSet.Values[0].V, WriteSI->parent)) {

    LFV3(errs() << "Write through certain pointer\n");
    // Best case: store through a single, certain pointer. Overwrite the location with our new PB.

    LocStore* Store = StoreBB->getWritableStoreFor(PtrSet.Values[0].V, PtrSet.Values[0].Offset, PtrSize, true);
    if(!Store)
      return;

    replaceRangeWithPB(Store->store, ValPB, (uint64_t)PtrSet.Values[0].Offset, PtrSize);
    checkStore(Store->store, PtrSet.Values[0].V);
 
  }
  else {

    for(SmallVector<ImprovedVal, 1>::iterator it = PtrSet.Values.begin(), it2 = PtrSet.Values.end(); it != it2; ++it) {

      LocStore* Store;

      if(it->Offset == LLONG_MAX) {
	LFV3(errs() << "Write through vague pointer; clobber\n");

	Store = StoreBB->getWritableStoreFor(it->V, 0, ULONG_MAX, true);
	if(!Store)
	    continue;

	ImprovedValSetSingle OD(ValSetTypeUnknown, true);
	replaceRangeWithPB(Store->store, OD, 0, ULONG_MAX);

      }
      else {

	Store = StoreBB->getWritableStoreFor(it->V, it->Offset, PtrSize, true);
	if(!Store)
	  continue;
	
	ImprovedValSetSingle oldValSet;
	if(ValPB.Overdef) {

	  // Overdef merges with any other value to make Overdef, so skip the lookup.
	  oldValSet = ValPB;

	}
	else {

	  LFV3(errs() << "Write through maybe pointer; merge\n");
	  readValRange(it->V, it->Offset, PtrSize, StoreBB, oldValSet, 0, 0);

	  if((!oldValSet.isWhollyUnknown()) && oldValSet.isInitialised()) {

	    Type* oldType = WriteSI->parent->IA->getValueType(oldValSet.Values[0].V);
	    Type* newType = WriteSI->parent->IA->getValueType(ValPB.Values[0].V);

	    if(ValPB.canCoerceToType(oldType, PtrSize, 0, false)) {

	      ValPB.coerceToType(oldType, PtrSize, 0, false);
	      LFV3(errs() << "Read-modify-write failure coercing to type " << (*oldType) << "\n");

	    }
	    else if((!ValPB.isWhollyUnknown()) && ValPB.Values.size() > 0 && oldValSet.canCoerceToType(newType, PtrSize, 0, false)) {
		
	      oldValSet.coerceToType(newType, PtrSize, 0, false);

	    }
	    else {
	      ValPB.setOverdef();
	    }

	  }

	  oldValSet.merge(ValPB);

	}

	replaceRangeWithPB(Store->store, oldValSet, (uint64_t)it->Offset, PtrSize);

      }

      checkStore(Store->store, it->V);

    }

  }

  propagateStoreFlags(PtrSet, ValPB, StoreBB);

}

// If ValPB might be an unknown pointer, note that all objects might have leaked
// as of StoreBB. If ValPB is a particular pointer and PtrSet has itself leaked / escaped,
// propagate that status to pointers in ValPB.
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

// Given extent-lists LHS and RHS, find a common ancestor if one exists.
// For IVSSingles a common base is identified by value equality; for IVSMultis it is only identified by pointer equality,
// so Multis that describe the same values may go unnoticed.
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

// Expand a scalar-splat value (e.g. i8 0 x 256) into a concrete constant.
static void scalarSplatToScalar(ImprovedValSetSingle& IVS, Type* targetType) {

  for(uint32_t i = 0, ilim = IVS.Values.size(); i != ilim; ++i) {

    uint64_t Size = GlobalTD->getTypeStoreSize(targetType);
    PartialVal PV(Size);
    uint8_t SplatVal = (uint8_t)cast<ConstantInt>(IVS.Values[i].V.getVal())->getLimitedValue();
    memset(PV.partialBuf, SplatVal, Size);
    for(uint64_t i = 0; i != Size; ++i)
      PV.partialValidBuf[i] = true;
    PV.loadFinished = true;
    Constant* PVC = PVToConst(PV, Size, targetType->getContext());
    IVS.Values[i] = ImprovedVal(ShadowValue(PVC));

  }

  IVS.SetType = ValSetTypeScalar;
  IVS.coerceToType(targetType, GlobalTD->getTypeStoreSize(targetType), 0);

}

// Merge otherVal into consumeVal, using parameters expressed through Visitor
static void mergeValues(ImprovedValSetSingle& consumeVal, ImprovedValSetSingle& otherVal, OrdinaryMerger* Visitor) {

  if(Visitor->useVarargMerge && 
     consumeVal.SetType == ValSetTypeVarArg && 
     otherVal.SetType == ValSetTypeVarArg && 
     consumeVal.Values.size() == 1 && 
     otherVal.Values.size() == 1) {

    if(otherVal.Values[0].Offset > consumeVal.Values[0].Offset)
      consumeVal = otherVal;
    
  }
  else {

    // Expand scalar splats if the other argument is not a splat.
    if(consumeVal.SetType == ValSetTypeScalarSplat && consumeVal.Values.size() && otherVal.SetType == ValSetTypeScalar && otherVal.Values.size()) {

      scalarSplatToScalar(consumeVal, otherVal.Values[0].V.getNonPointerType());
      // Fall through to merge

    }
    else if(consumeVal.SetType == ValSetTypeScalar && consumeVal.Values.size() && otherVal.SetType == ValSetTypeScalarSplat && otherVal.Values.size()) {

      ImprovedValSetSingle Copy(otherVal);
      scalarSplatToScalar(Copy, consumeVal.Values[0].V.getNonPointerType());
      consumeVal.merge(Copy);
      return;

    }

    // Convert scalar zeroes to null pointers if appropriate.
    else if(((consumeVal.SetType == ValSetTypeScalar || consumeVal.SetType == ValSetTypeScalarSplat) && 
	     consumeVal.Values.size() && 
	     otherVal.SetType == ValSetTypePB && 
	     otherVal.Values.size()) ||
	    
	    ((otherVal.SetType == ValSetTypeScalar || otherVal.SetType == ValSetTypeScalarSplat) && 
	     otherVal.Values.size() && 
	     consumeVal.SetType == ValSetTypePB && 
	     consumeVal.Values.size())) {

      // Asymmetry to avoid altering the read-only otherVal (consumeVal is mutable).
      if(consumeVal.onlyContainsZeroes()) {

	Constant* newNull = Constant::getNullValue(Visitor->originContext->getValueType(otherVal.Values[0].V));
	if(newNull->getType()->isPointerTy())
	  consumeVal.set(ImprovedVal(newNull, 0), ValSetTypePB);
	else
	  consumeVal.set(ImprovedVal(newNull), ValSetTypeScalar);

	// Fall through to merge.

      }
      else if(otherVal.onlyContainsZeroes()) {

	Constant* newNull = Constant::getNullValue(Visitor->originContext->getValueType(consumeVal.Values[0].V));	
	if(newNull->getType()->isPointerTy())
	  consumeVal.mergeOne(ValSetTypePB, ImprovedVal(newNull, 0));
	else
	  consumeVal.mergeOne(ValSetTypeScalar, ImprovedVal(newNull));
	checkIVSNull(consumeVal);
	return;

      }

      // Otherwise fall through to certain doom.

    }
	
    consumeVal.merge(otherVal);

  }

  checkIVSNull(consumeVal);

}

// Merge whole block-local stores mergeFrom and mergeTo.
void LocStore::mergeStores(LocStore* mergeFromStore, LocStore* mergeToStore, uint64_t ASize, OrdinaryMerger* Visitor) {

  if(mergeFromStore->store == mergeToStore->store)
    return;

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
    if(!getCommonAncestor(mergeToStore->store, mergeFromStore->store, LHSAncestor, RHSAncestor, Seen)) {

      LHSAncestor = 0;
      RHSAncestor = 0;
	      
    }
    LFV3(errs() << "Merging multi stores; use common ancestor " << LHSAncestor << "/" << RHSAncestor << "\n");
  }

  {
    SmallVector<IVSRange, 4> LHSVals;
    SmallVector<IVSRange, 4> RHSVals;

    readValRangeMultiFrom(0, ASize, mergeToStore->store, LHSVals, LHSAncestor, ASize);
    readValRangeMultiFrom(0, ASize, mergeFromStore->store, RHSVals, RHSAncestor, ASize);
	  
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

	readValRangeMultiFrom(LastOffset, stopAt - LastOffset, LHSAncestor, baseVals, 0, ASize);

	for(SmallVector<IVSRange, 4>::iterator baseit = baseVals.begin(), baseend = baseVals.end();
	    baseit != baseend; ++baseit) {

	  ImprovedValSetSingle subVal;
	  getIVSSubVal(consumeit->second, baseit->first.first - consumeit->first.first, baseit->first.second - baseit->first.first, subVal);
	  mergeValues(subVal, baseit->second, Visitor);
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

	mergeValues(consumeVal, otherVal, Visitor);
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
    if((LHSVals.empty() || LHSVals.back().first.second != ASize) &&
       (RHSVals.empty() || RHSVals.back().first.second != ASize))
      anyGaps = true;

    if(anyGaps) {
      LFV3(errs() << "Using ancestor " << LHSAncestor << "\n");
      newUnderlying = LHSAncestor;
      if(newUnderlying)
	newUnderlying = newUnderlying->getReadableCopy();
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
      newStore = new ImprovedValSetMulti(ASize);
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

// If store merging has left a common base store with only single reference, merge down.
void LocStore::simplifyStore(LocStore* LS) {

  ImprovedValSetMulti* IVM;
  ImprovedValSetMulti* IVM2;

  while((IVM = dyn_cast_or_null<ImprovedValSetMulti>(LS->store)) &&
	(IVM2 = dyn_cast_or_null<ImprovedValSetMulti>(IVM->Underlying)) &&
	IVM->MapRefCount == 1 && IVM2->MapRefCount == 1) {
    
    /*
    errs() << "Simplify:\n";
    IVM->print(errs(), false);
    */

    // Write IVM members over IVM2

    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(),
	  itend = IVM->Map.end(); it != itend; ++it) {

      replaceRangeWithPB(IVM2, it.value(), it.start(), it.stop() - it.start());
	  
    }

    // IVM2 becomes the new head.
    LS->store = IVM2;
    delete IVM;

    /*
    errs() << "Result:\n";
    IVM2->print(errs(), false);
    */

  }

}

static bool sizeLT(const DenseSet<ShadowValue>* a, const DenseSet<ShadowValue>* b) {

  return a->size() < b->size();

}

// mergeBegin -> mergeEnd are already listed smallest set first.
void llvm::intersectSets(DenseSet<ShadowValue>* Target, MutableArrayRef<DenseSet<ShadowValue>* > Merge) {

  SmallVector<ShadowValue, 8> toKeep;

  MutableArrayRef<DenseSet<ShadowValue>* >::iterator mergeBegin = Merge.begin(), mergeEnd = Merge.end();
  std::sort(mergeBegin, mergeEnd, sizeLT);

  if(Target->size() < (*mergeBegin)->size()) {

    for(DenseSet<ShadowValue>::iterator it = Target->begin(), itend = Target->end(); it != itend; ++it) {

      bool keepThis = true;
      for(MutableArrayRef<DenseSet<ShadowValue>* >::iterator findit = mergeBegin; findit != mergeEnd && keepThis; ++findit) {

	if(!(*findit)->count(*it))
	  keepThis = false;

      }

      if(keepThis)
	toKeep.push_back(*it);

    }

  }
  else {

    MutableArrayRef<DenseSet<ShadowValue>* >::iterator othersBegin = mergeBegin;
    ++othersBegin;

    for(DenseSet<ShadowValue>::iterator it = (*mergeBegin)->begin(), 
	  itend = (*mergeBegin)->end(); it != itend; ++it) {

      bool keepThis = Target->count(*it);
      for(MutableArrayRef<DenseSet<ShadowValue>* >::iterator findit = othersBegin; findit != mergeEnd && keepThis; ++findit) {

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

// Debug dump functions:

static void dumpSets(OrdinaryLocalStore* Map) {

  errs() << "Not-old:\n";
  for(DenseSet<ShadowValue>::iterator it = Map->es.noAliasOldObjects.begin(), itend = Map->es.noAliasOldObjects.end(); it != itend; ++it) {

    errs() << itcache(*it) << "\n";
    
  }
  errs() << "\n\n";

  errs() << "Thread-local:\n";
  for(DenseSet<ShadowValue>::iterator it = Map->es.threadLocalObjects.begin(), itend = Map->es.threadLocalObjects.end(); it != itend; ++it) {

    errs() << itcache(*it) << "\n";

  }
  errs() << "\n\n";


  errs() << "Unescaped:\n";
  for(DenseSet<ShadowValue>::iterator it = Map->es.unescapedObjects.begin(), itend = Map->es.unescapedObjects.end(); it != itend; ++it) {
	
    errs() << itcache(*it) << "\n";
	
  }
  errs() << "\n\n";

}

void OrdinaryStoreExtraState::dump(OrdinaryLocalStore* Map) {
  
  dumpSets(Map);

}

// Merge the sets of objects known not to escape from this thread, not to be written
// to global memory, and so on. In all current cases an object only has the desired
// property if it has it in all predecessor blocks.

void OrdinaryStoreExtraState::doMerge(OrdinaryLocalStore* toMap, 
				      SmallVector<OrdinaryLocalStore*, 4>::iterator fromBegin, 
				      SmallVector<OrdinaryLocalStore*, 4>::iterator fromEnd,
				      bool verbose) {
  
  // All flag sets should be big-intersected.
  
  {

    SmallVector<DenseSet<ShadowValue>*, 4> NAOSets;
    for(SmallVector<OrdinaryLocalStore*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
      NAOSets.push_back(&(*it)->es.noAliasOldObjects);
    intersectSets(&toMap->es.noAliasOldObjects, NAOSets);

  }

  {

    SmallVector<DenseSet<ShadowValue>*, 4> TLSets;
    for(SmallVector<OrdinaryLocalStore*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
      TLSets.push_back(&(*it)->es.threadLocalObjects);
    intersectSets(&toMap->es.threadLocalObjects, TLSets);



  }

  {

    SmallVector<DenseSet<ShadowValue>*, 4> EscSets;
    for(SmallVector<OrdinaryLocalStore*, 4>::iterator it = fromBegin; it != fromEnd; ++it)
      EscSets.push_back(&(*it)->es.unescapedObjects);
    intersectSets(&toMap->es.unescapedObjects, EscSets);

  }

  if(verbose)
    dumpSets(toMap);

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

  // This BB is a merge of all that has gone before; merge to values' base stores
  // rather than a local map.

  bool verbose = false;
  if(verbose) {

    errs() << "Dump at block " << BB->invar->BB->getName() << "\n";

  }

  OrdinaryMerger V(BB->IA, BB->useSpecialVarargMerge, /* verbose = */ verbose);

  if(verbose)
    errs() << "\n\n";

  BB->IA->visitNormalPredecessorsBW(BB, &V, /* ctx = */0);
  V.doMerge();

  if(!V.newMap) {
    BB->localStore = 0;
    return false;
  }

  BB->localStore = V.newMap;

  doBlockFDStoreMerge(BB);

  return true;

}

// Stack-maintenance functions, adding and removing frames as needed.
void PeelIteration::popAllocas(OrdinaryLocalStore*) { }

void InlineAttempt::popAllocas(OrdinaryLocalStore* map) {

  for(uint32_t i = 0, ilim = localAllocas.size(); i != ilim; ++i) {

    ShadowValue SV = ShadowValue::getPtrIdx(stack_depth, i);
    map->es.unescapedObjects.erase(SV);
    map->es.noAliasOldObjects.erase(SV);
    map->es.threadLocalObjects.erase(SV);

  }
 
}

void ShadowBB::popStackFrame() {

  localStore = localStore->getWritableFrameList();
  localStore->popStackFrame();
  IA->popAllocas(localStore);

}

void ShadowBB::pushStackFrame(InlineAttempt* IA) {

  localStore = localStore->getWritableFrameList();
  localStore->pushStackFrame(IA);

}

// Merge the stores presented at SI's callee's return blocks into a single store
// to analyse the remainder of the program.
// Note that the callee has already popped the top stack frame from each one.
void llvm::doCallStoreMerge(ShadowInstruction* SI) {

  doCallStoreMerge(SI->parent, SI->parent->IA->getInlineAttempt(SI));
  
}

void llvm::doCallStoreMerge(ShadowBB* CallerBB, InlineAttempt* CallIA) {

  LFV3(errs() << "Start call-return store merge\n");

  OrdinaryMerger V(CallerBB->IA);
  CallIA->visitLiveReturnBlocks(V);
  V.doMerge();

  CallerBB->localStore = V.newMap;

  doCallFDStoreMerge(CallerBB, CallIA);

}

// Is IA a child of this context, down to the nearest function scope (InlineAttempt)?
bool InlineAttempt::ctxContains(IntegrationAttempt* IA) {

  return this == IA;

}

bool PeelIteration::ctxContains(IntegrationAttempt* IA) {

  if(this == IA)
    return true;
  return parent->ctxContains(IA);

}

AllocData* ShadowValue::getAllocData(OrdinaryLocalStore* Map) const {

  release_assert(isPtrIdx());
  if(u.PtrOrFd.frame == -1)
    return &GlobalIHP->heap[u.PtrOrFd.idx];
  else
    return &Map->frames[u.PtrOrFd.frame]->IA->localAllocas[u.PtrOrFd.idx];

}

AllocData* IntegrationAttempt::getAllocData(ShadowValue V) {

  release_assert(V.isPtrIdx());
  
  if(V.u.PtrOrFd.frame == -1)
    return &GlobalIHP->heap[V.u.PtrOrFd.idx];
  else
    return &getFunctionRoot()->getStackFrameCtx(V.u.PtrOrFd.frame)->localAllocas[V.u.PtrOrFd.idx];

}

ShadowInstruction* IntegrationAttempt::getAllocInst(ShadowValue V) {

  AllocData* AD = getAllocData(V);
  release_assert(!AD->isCommitted);
  return AD->allocValue.u.I;

}

static ImprovedValSetSingle NormalEmptyMap(ValSetTypeDeallocated, false);
LocStore llvm::NormalEmptyMapPtr(&NormalEmptyMap);
