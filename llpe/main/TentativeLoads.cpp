//===- TentativeLoads.cpp -------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

// A mini-analysis that spots tentative loads and memcpy instructions.
// These are loads whose incoming dataflow (a) crosses a /yield point/, a point where we must assume
// that another thread got a chance to run and messed with our state, (b) is not dominated
// by other loads or stores that will check the incoming state / overwrite it with known state,
// and (c) is not known to be thread-local regardless.

// The main phase has already taken care of part (c) for us by setting ShadowInstruction::u.load.isThreadLocal
// when the load was known to be from a thread-private object. We will set the same flag wherever
// it's clear that checking this load would be redundant.

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/DataLayout.h"

using namespace llvm;

// Simple progress bar.

static uint32_t TLProgressN = 0;
const uint32_t TLProgressLimit = 1000;

static void TLProgress() {

  TLProgressN++;
  if(TLProgressN == TLProgressLimit) {

    errs() << ".";
    TLProgressN = 0;

  }

}

// Allocator and shared empty-store object.
static TLMapTy::Allocator TLMapAllocator;
static TLMapTy TLEmptyMap(TLMapAllocator);
TLMapPointer llvm::TLEmptyMapPtr(&TLEmptyMap);

TLLocalStore* TLMapPointer::getMapForBlock(ShadowBB* BB) {

  return BB->tlStore;

}

// Copy the store entries. The entries themselves may still be shared.
TLMapPointer TLMapPointer::getReadableCopy() {

  TLMapTy* newMap = new TLMapTy(TLMapAllocator);
  for(TLMapTy::iterator it = M->begin(), itend = M->end(); it != itend; ++it)
    newMap->insert(it.start(), it.stop(), *it);

  return TLMapPointer(newMap);

}

// Maps themselves are not shared at the moment, so just delete it.
bool TLMapPointer::dropReference() {

  delete M;
  M = 0;

  return true;

}

// Merge two is-known-good arrays. An offset is good if it's good in both parents.
void TLMapPointer::mergeStores(TLMapPointer* mergeFrom, TLMapPointer* mergeTo, uint64_t ASize, TLMerger* Visitor) {

  // Intersect the sets per byte. The values are just booleans, so overwriting without erasing is fine.

  SmallVector<std::pair<uint64_t, uint64_t>, 4> keepRanges;

  for(TLMapTy::iterator it = mergeFrom->M->begin(), itend = mergeFrom->M->end();
      it != itend; ++it) {

    for(TLMapTy::iterator toit = mergeTo->M->find(it.start()), toitend = mergeTo->M->end();
	toit != toitend && toit.start() < it.stop(); ++toit) {

      // Intersect ranges:
      uint64_t keepStart = std::max(toit.start(), it.start());
      uint64_t keepStop = std::min(toit.stop(), it.stop());
      keepRanges.push_back(std::make_pair(keepStart, keepStop));

    }

  }

  mergeTo->M->clear();
  for(SmallVector<std::pair<uint64_t, uint64_t>, 4>::iterator it = keepRanges.begin(),
	itend = keepRanges.end(); it != itend; ++it) {

    mergeTo->M->insert(it->first, it->second, true);

  }

}

// Get a writable array for value O, including breaking CoW data structures above it.
TLMapPointer* ShadowBB::getWritableTLStore(ShadowValue O) {

  tlStore = tlStore->getWritableFrameList();
  bool isNewStore;
  TLMapPointer* ret = tlStore->getOrCreateStoreFor(O, &isNewStore);

  if(isNewStore)
    ret->M = new TLMapTy(TLMapAllocator);

  return ret;

}

// Clear the store to mark everything tentative (needs checking against concurrent
// interference). Note that an instruction here forced us to repeat all checks.
static void markAllObjectsTentative(ShadowInstruction* SI, ShadowBB* BB) {

  BB->tlStore = BB->tlStore->getEmptyMap();
  BB->tlStore->allOthersClobbered = true;
  BB->IA->yieldState = BARRIER_HERE;

  if(inst_is<LoadInst>(SI) || inst_is<AtomicRMWInst>(SI))
    errs() << "Clobber all at " << SI->parent->IA->F.getName() << "," << SI->parent->invar->BB->getName() << "," << std::distance(SI->parent->invar->BB->begin(), BasicBlock::iterator(SI->invar->I)) << "\n";

}

// Note that GoodPtr[Offset:Offset+Len] has been checked and need not be rechecked until another memory-ordered
// instruction or yield point means we must assume possible inter-thread communication again.
// Mark the good offsets as of block BB.
static void markGoodBytes(ShadowValue GoodPtr, uint64_t Len, bool contextEnabled, ShadowBB* BB, uint64_t Offset = 0) {

  // If we're in a disabled context, the loads and stores here will
  // be committed unmodified, in particular without checks that their results are as expected,
  // and so they do not make any subsequent check redundant.
  // Stores in disabled contexts can't count either, because of the situation:
  // disabled {
  //   call void thread_yield();
  //   %0 = load %x;
  //   store %0, %y;
  // }
  // %1 = load %y
  
  // Here the load %y must be checked, because the load %x cannot be checked.

  // Might be able to be smarter...
  if(!contextEnabled)
    return;

  // If allOthersClobbered is false then no object is tentative.
  if(!BB->tlStore->allOthersClobbered)
    return;

  // If we're not sure what object we just read from we can't be sure we're
  // dealing with the same thing next load, so no check elimination is allowed.
  std::pair<ValSetType, ImprovedVal> PtrTarget;
  if(!tryGetUniqueIV(GoodPtr, PtrTarget))
    return;

  // Load from a non-pointer? Might be an assert.
  if(PtrTarget.first != ValSetTypePB)
    return;

  // Constants are always good.
  if(PtrTarget.second.V.isGV() &&  PtrTarget.second.V.u.GV->G->isConstant())
    return;

  SmallVector<std::pair<uint64_t, uint64_t>, 1> addRanges;

  TLMapPointer* store = BB->tlStore->getReadableStoreFor(PtrTarget.second.V);
  uint64_t start = PtrTarget.second.Offset + Offset;
  uint64_t stop = PtrTarget.second.Offset + Offset + Len;

  if(!store) {
   
    addRanges.push_back(std::make_pair(start, stop));

  }
  else {

    // Figure out what offsets need marking, if any.
    TLMapTy::iterator it = store->M->find(start), itend = store->M->end();

    if(it == itend || it.start() >= stop) {

      addRanges.push_back(std::make_pair(start, stop));

    }
    else {

      // Gap at left?

      if(it.start() > start)
	addRanges.push_back(std::make_pair(start, it.start()));

      for(; it != itend && it.start() < stop; ++it) {
    
	// Gap to the right of this extent?
	if(it.stop() < stop) {

	  TLMapTy::iterator nextit = it;
	  ++nextit;

	  uint64_t gapend;
	  if(nextit == itend)
	    gapend = stop;
	  else
	    gapend = std::min(stop, nextit.start());

	  if(it.stop() != gapend)
	    addRanges.push_back(std::make_pair(it.stop(), gapend));

	}

      }

    }

  }
  
  if(!addRanges.empty()) {

    TLMapPointer* writeStore = BB->getWritableTLStore(PtrTarget.second.V);
    for(SmallVector<std::pair<uint64_t, uint64_t>, 1>::iterator it = addRanges.begin(),
	  itend = addRanges.end(); it != itend; ++it) {

      writeStore->M->insert(it->first, it->second, true);

    }

  }

}

// A path condition checks that a certain value is as expected at runtime. Mark it as checked as of block BB.
static void walkPathCondition(PathConditionTypes Ty, PathCondition& Cond, bool contextEnabled, ShadowBB* BB) {

  ShadowValue CondSV = BB->IA->getFunctionRoot()->getPathConditionSV(Cond);
  uint64_t Len = 0;
  switch(Ty) {
  case PathConditionTypeIntmem: // Assertion about an in-memory integer.
    Len = GlobalTD->getTypeStoreSize(Cond.u.val->getType());
    break;
  case PathConditionTypeString: // Assertion about a C-string.
    Len = cast<ConstantDataArray>(Cond.u.val)->getNumElements();
    break;
  default:
    release_assert(0 && "Bad path condition type");
    llvm_unreachable("Bad path condition type");
  }

  markGoodBytes(CondSV, Len, contextEnabled, BB, Cond.offset);

}

// Mark the targets of all path condition checks at the top of BB checked.
static void walkPathConditions(PathConditionTypes Ty, std::vector<PathCondition>& Conds, bool contextEnabled, ShadowBB* BB, uint32_t stackDepth) {

  for(std::vector<PathCondition>::iterator it = Conds.begin(), itend = Conds.end(); it != itend; ++it) {

    if(stackDepth != it->fromStackIdx || BB->invar->BB != it->fromBB)
      continue;

    walkPathCondition(Ty, *it, contextEnabled, BB);

  }

}

// Merge the known-good-offsets maps from all IA's return blocks.
// Assign the result to BB.
void llvm::doTLCallMerge(ShadowBB* BB, InlineAttempt* IA) {

  TLMerger V(BB->IA, false);
  IA->visitLiveReturnBlocks(V);
  V.doMerge();
  
  BB->tlStore = V.newMap;

}

// Mark the targets of all path condition checks PC at the top of BB checked.
static void walkPathConditionsIn(PathConditions& PC, uint32_t stackIdx, ShadowBB* BB, bool contextEnabled, bool secondPass) {

  walkPathConditions(PathConditionTypeIntmem, PC.IntmemPathConditions, 
		     contextEnabled, BB, stackIdx);
  walkPathConditions(PathConditionTypeString, PC.StringPathConditions, 
		     contextEnabled, BB, stackIdx);

  for(std::vector<PathFunc>::iterator it = PC.FuncPathConditions.begin(),
	itend = PC.FuncPathConditions.end(); it != itend; ++it) {

    if(it->stackIdx != stackIdx)
      continue;

    // Pass the TL store into the path condition function:
    it->IA->BBs[0]->tlStore = BB->tlStore;
    // Path conditions can be treated like committed code, as the user is responsible for checking
    // their applicability.
    it->IA->findTentativeLoads(/* commitDisabledHere = */false, secondPass);
    // Retrieve the resultant TL store:
    doTLCallMerge(BB, it->IA);
    
  }

}

// Mark the targets of all path condition checks PC at the top of BB checked.
void llvm::TLWalkPathConditions(ShadowBB* BB, bool contextEnabled, bool secondPass) {

  InlineAttempt* IA = BB->IA->getFunctionRoot();

  // Consider path conditions specific to this specialisation
  if(IA->targetCallInfo)
    walkPathConditionsIn(GlobalIHP->pathConditions, IA->targetCallInfo->targetStackDepth, BB, contextEnabled, secondPass);

  // Consider path conditions that apply to all calls to this function
  if(BB->IA->invarInfo->pathConditions)
    walkPathConditionsIn(*BB->IA->invarInfo->pathConditions, UINT_MAX, BB, contextEnabled, secondPass);

}

// Mark bytes read or written by a memcpy-like instruction as checked.
static void walkCopyInst(ShadowValue CopyFrom, ShadowValue CopyTo, ShadowValue LenSV, bool contextEnabled, ShadowBB* BB) {

  uint64_t Len;
  if(!tryGetConstantInt(LenSV, Len))
    return;

  markGoodBytes(CopyTo, Len, contextEnabled, BB);
  markGoodBytes(CopyFrom, Len, contextEnabled, BB);

}

// Update the TL store in whatever way is required by SI.
static void updateTLStore(ShadowInstruction* SI, bool contextEnabled) {

  if(inst_is<AllocaInst>(SI)) {

    // Alloca: mark all good.
    ShadowValue SV(SI);
    ShadowValue Base;
    getBaseObject(SV, Base);
    markGoodBytes(ShadowValue(SI), SI->parent->IA->getFunctionRoot()->localAllocas[Base.u.PtrOrFd.idx].storeSize, contextEnabled, SI->parent);

  }
  else if(LoadInst* LI = dyn_cast_inst<LoadInst>(SI)) {

    // Load: mark good (our caller will have emitted a check if necessary) unless the load is itself
    // a synchronisation point.
    if((LI->isVolatile() || SI->hasOrderingConstraint()) && !SI->parent->IA->pass->atomicOpIsSimple(LI))
      markAllObjectsTentative(SI, SI->parent);
    else
      markGoodBytes(SI->getOperand(0), GlobalTD->getTypeStoreSize(LI->getType()), contextEnabled, SI->parent);

  }
  else if(StoreInst* StoreI = dyn_cast_inst<StoreInst>(SI)) {

    // I don't think there's a need to regard a volatile /store/ as a yield point, as this is *outgoing* interthread communication
    // if it communication at all. Compare pthread_unlock which is not a yield point to pthread_lock, which is.
    //if(StoreI->isVolatile())
    //markAllObjectsTentative(SI, SI->parent);
    //else
    markGoodBytes(SI->getOperand(1), GlobalTD->getTypeStoreSize(StoreI->getValueOperand()->getType()), contextEnabled, SI->parent);

  }
  else if(SI->readsMemoryDirectly() && SI->hasOrderingConstraint()) {

    // Might create a synchronisation edge:
    if(SI->isThreadLocal == TLS_MUSTCHECK && !SI->parent->IA->pass->atomicOpIsSimple(SI->invar->I))
      markAllObjectsTentative(SI, SI->parent);
    else
      markGoodBytes(SI->getOperand(0), GlobalTD->getTypeStoreSize(SI->getType()), contextEnabled, SI->parent);

  }
  else if(inst_is<FenceInst>(SI)) {

    // Explicit thread yield:
    markAllObjectsTentative(SI, SI->parent);

  }
  else if(inst_is<CallInst>(SI) || inst_is<InvokeInst>(SI)) {

    if(inst_is<MemSetInst>(SI)) {

      // Memset: mark good.
      uint64_t MemSize;
      if(!tryGetConstantInt(SI->getCallArgOperand(2), MemSize))
	return;

      markGoodBytes(SI->getCallArgOperand(0), MemSize, contextEnabled, SI->parent);

    }
    else if(inst_is<MemTransferInst>(SI)) {

      // Memcpy: mark both args good.
      walkCopyInst(SI->getCallArgOperand(0), SI->getCallArgOperand(1), SI->getCallArgOperand(2), contextEnabled, SI->parent);

    }
    else {

      CallInst* CallI = dyn_cast_inst<CallInst>(SI);

      Function* F = getCalledFunction(SI);
      DenseMap<Function*, specialfunctions>::iterator findit;
      if(ReadFile* RF = SI->parent->IA->tryGetReadFile(SI)) {

	// Read from file: mark buffer good.
	markGoodBytes(SI->getCallArgOperand(1), RF->readSize, contextEnabled, SI->parent);

      }
      else if((findit = SpecialFunctionMap.find(F)) != SpecialFunctionMap.end()) {

	switch(findit->second) {

	case SF_REALLOC:

	  // Realloc == copy + malloc.
	  walkCopyInst(SI, SI->getCallArgOperand(0), SI->getCallArgOperand(1), contextEnabled, SI->parent);
	  // Fall through to:

	case SF_MALLOC:
	  
	  {

	    // Malloc: mark all good.
	    ShadowValue SV(SI);
	    ShadowValue Base;
	    getBaseObject(SV, Base);

	    markGoodBytes(SV, GlobalIHP->heap[Base.u.PtrOrFd.idx].storeSize, contextEnabled, SI->parent);

	  }

	default:
	  break;

	}

      }
      else if(CallI && (((!F) && !GlobalIHP->programSingleThreaded) || GlobalIHP->yieldFunctions.count(F))) {

	// Unknown function or explicitly-annotated yield function -- may overwrite anything;
	// everything needs re-checking.
	
	if(GlobalIHP->pessimisticLocks.count(CallI)) {

	  // Pessimistic locks clobber at specialisation time, so we already assume everything was overwritten;
	  // no runtime checking required.
	  return;

	}
	
	SmallDenseMap<CallInst*, std::vector<GlobalVariable*>, 4>::iterator findit =
	  GlobalIHP->lockDomains.find(CallI);

	if(findit != GlobalIHP->lockDomains.end()) {

	  // This a bit of a hack -- the user can annotate a particular yield function
	  // as only clobbering some particular globals.
	  
	  for(std::vector<GlobalVariable*>::iterator it = findit->second.begin(),
		itend = findit->second.end(); it != itend; ++it) {

	    ShadowGV* SGV = &GlobalIHP->shadowGlobals[GlobalIHP->getShadowGlobalIndex(*it)];
	    ShadowValue SV(SGV);
	    TLMapPointer* TLObj = SI->parent->getWritableTLStore(SV);
	    // Mark whole object tentative:
	    TLObj->M->clear();

	  }

	}
	else {

	  // No explicit domain given; clobbers everything.
	  markAllObjectsTentative(SI, SI->parent);

	}

      }

    }

  }

}

// Is any of Ptr[0:Size] currently marked tentative, as of block BB?
static bool shouldCheckRead(ImprovedVal& Ptr, uint64_t Size, ShadowBB* BB) {

  // Read from null?
  if(Ptr.V.isNullPointer())
    return false;

  // Read from constant global?
  if(Ptr.V.isGV() && Ptr.V.u.GV->G->isConstant())
    return false;

  bool verbose = false;

  if(verbose)
    errs() << "Read from " << itcache(Ptr.V) << ":\n";

  TLMapPointer* Map = BB->tlStore->getReadableStoreFor(Ptr.V);
  if(!Map) {
    if(verbose)
      errs() << "Whole map: " << BB->tlStore->allOthersClobbered << "\n";
    return BB->tlStore->allOthersClobbered;
  }

  if(verbose) {

    for(TLMapTy::iterator it = Map->M->begin(), itend = Map->M->end(); it != itend; ++it) {

      errs() << it.start() << "-" << it.stop() << "\n";

    }

  }

  TLMapTy::iterator it = Map->M->find(Ptr.Offset);
  bool coveredByMap = (it != Map->M->end() && ((int64_t)it.start()) <= Ptr.Offset && ((int64_t)it.stop()) >= Ptr.Offset + ((int64_t)Size));

  return !coveredByMap;
    
}

// Is any of PtrOp[0:LenSV] currently marked tentative, as of block SI.parent?
ThreadLocalState IntegrationAttempt::shouldCheckCopy(ShadowInstruction& SI, ShadowValue PtrOp, ShadowValue LenSV) {

  uint64_t Len;
  bool LenValid = tryGetConstantInt(LenSV, Len);
  std::pair<ValSetType, ImprovedVal> Ptr;

  // Unsure what we're reading? Then there's nothing to check.
  if((!LenValid) || (!tryGetUniqueIV(PtrOp, Ptr)) || Ptr.first != ValSetTypePB)
    return TLS_NEVERCHECK;
  
  if(Len == 0)
    return TLS_NEVERCHECK;

  // memcpyValues is unpopulated if the copy didn't "work" during specialisation,
  // so there is nothing to check.
  DenseMap<ShadowInstruction*, SmallVector<IVSRange, 4> >::iterator findit = GlobalIHP->memcpyValues.find(&SI);
  if(findit == GlobalIHP->memcpyValues.end() || !findit->second.size())
    return TLS_NEVERCHECK;

  // Check each concrete value that was successfully read during information prop
  for(SmallVector<IVSRange, 4>::iterator it = findit->second.begin(),
	itend = findit->second.end(); it != itend; ++it) {

    if(it->second.isWhollyUnknown())
      continue;

    ImprovedVal ReadPtr = Ptr.second;
    ReadPtr.Offset += it->first.first;
    if(shouldCheckRead(ReadPtr, it->first.second - it->first.first, SI.parent))
      return TLS_MUSTCHECK;

  }

  // No value requires a runtime check
  return TLS_NOCHECK;
    
}

// Is any of Ptr[0:LoadSize] marked tentative as of SI.parent?
ThreadLocalState IntegrationAttempt::shouldCheckLoadFrom(ShadowInstruction& SI, ImprovedVal& Ptr, uint64_t LoadSize) {

  if(Ptr.V.isNullOrConst())
    return TLS_NEVERCHECK;

  // If this reads multiple values (e.g. an FD + integer pair) check both.
  ImprovedValSetMulti* IV = dyn_cast<ImprovedValSetMulti>(SI.i.PB);
  if(IV) {

    SmallVector<IVSRange, 4> vals;
    for(ImprovedValSetMulti::MapIt it = IV->Map.begin(), itend = IV->Map.end(); it != itend; ++it) {

      if(it.value().isWhollyUnknown())
	continue;      

      ImprovedVal ReadPtr = Ptr;
      ReadPtr.Offset += it.start();
      if(shouldCheckRead(ReadPtr, it.stop() - it.start(), SI.parent))
	return TLS_MUSTCHECK;

    }

    return TLS_NOCHECK;

  }

  return shouldCheckRead(Ptr, LoadSize, SI.parent) ? TLS_MUSTCHECK : TLS_NOCHECK;
  
}

// Does memory-reading instruction SI require a runtime check?
// It does if we succesfully extracted some information during specialisation, but the
// object we read from is marked tentative.
ThreadLocalState IntegrationAttempt::shouldCheckLoad(ShadowInstruction& SI) {

  if(GlobalIHP->programSingleThreaded)
    return TLS_NEVERCHECK;

  if(SI.readsMemoryDirectly() && !SI.isCopyInst()) {

    // Load doesn't extract any useful information?
    ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(SI.i.PB);
    if(IVS && IVS->isWhollyUnknown())
      return TLS_NEVERCHECK;

  }

  if(inst_is<LoadInst>(&SI)) {

    if(SI.hasOrderingConstraint())
      return TLS_MUSTCHECK;

    // Read from known-good memory?

    ShadowValue PtrOp = SI.getOperand(0);
    std::pair<ValSetType, ImprovedVal> Single;
    ImprovedValSet* IV;

    uint64_t LoadSize = GlobalTD->getTypeStoreSize(SI.getType());

    getIVOrSingleVal(PtrOp, IV, Single);
    if(IV) {

      ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(IV);

      // Didn't know what to read from? Then we can't have used any information
      // from this load during specialisation.
      if(IVS->isWhollyUnknown() || IVS->SetType != ValSetTypePB)
	return TLS_NEVERCHECK;

      ThreadLocalState result = TLS_NEVERCHECK;

      for(uint32_t i = 0, ilim = IVS->Values.size(); i != ilim && result != TLS_MUSTCHECK; ++i)
	result = std::min(shouldCheckLoadFrom(SI, IVS->Values[i], LoadSize), result);

      return result;

    }
    else {

      if(Single.first != ValSetTypePB)
	return TLS_NEVERCHECK;
      return shouldCheckLoadFrom(SI, Single.second, LoadSize);

    }

  }
  else if(inst_is<MemTransferInst>(&SI)) {

    ShadowValue PtrOp = SI.getCallArgOperand(1);
    ShadowValue Len = SI.getCallArgOperand(2);

    return shouldCheckCopy(SI, PtrOp, Len);

  }
  else if(inst_is<AtomicRMWInst>(&SI) || inst_is<AtomicCmpXchgInst>(&SI)) {

    // Always volatile if anything useful was loaded.
    return TLS_MUSTCHECK;

  }
  else {

    // Realloc instruction
    return shouldCheckCopy(SI, SI.getCallArgOperand(0), SI.getCallArgOperand(1));

  }

}

// Is this a memcpy, va_copy, realloc, etc?
bool ShadowInstruction::isCopyInst() {

  if(inst_is<MemTransferInst>(this))
    return true;

  if(inst_is<CallInst>(this)) {

    Function* F = getCalledFunction(this);
    DenseMap<Function*, specialfunctions>::iterator findit = SpecialFunctionMap.find(F);
    if(findit == SpecialFunctionMap.end())
      return false;

    switch(findit->second) {
      
    case SF_VACOPY:
    case SF_REALLOC:
      return true;
    default:
      return false;

    }


  }

  return false;

}

// Get read operand of a copy function / intrinsic.
ShadowValue ShadowInstruction::getCopySource() {

  if(inst_is<MemTransferInst>(this)) {

    return getCallArgOperand(1);

  }
  else if(inst_is<CallInst>(this)) {

    Function* F = getCalledFunction(this);
    if(!F)
      return ShadowValue();

    DenseMap<Function*, specialfunctions>::iterator findit = SpecialFunctionMap.find(F);
    if(findit == SpecialFunctionMap.end())
      return ShadowValue();

    switch(findit->second) {
      
    case SF_VACOPY:
      return getCallArgOperand(1);
    case SF_REALLOC:
      return getCallArgOperand(0);
    default:
      return ShadowValue();

    }
    
  }
  else {

    return ShadowValue();

  }

}

// Get target pointer for a copy instruction.
ShadowValue ShadowInstruction::getCopyDest() {

  if(inst_is<MemTransferInst>(this)) {

    return getCallArgOperand(0);

  }
  else if(inst_is<CallInst>(this)) {

    Function* F = getCalledFunction(this);
    if(!F)
      return ShadowValue();

    DenseMap<Function*, specialfunctions>::iterator findit = SpecialFunctionMap.find(F);
    if(findit == SpecialFunctionMap.end())
      return ShadowValue();

    switch(findit->second) {
      
    case SF_VACOPY:
      return getCallArgOperand(0);
    case SF_REALLOC:
      return ShadowValue(this);
    default:
      return ShadowValue();

    }
    
  }
  else {

    return ShadowValue();

  }

}

// Merge known-good-bytes maps at the start of block BB, by visiting its predecessor blocks.
void llvm::doTLStoreMerge(ShadowBB* BB) {

  TLMerger V(BB->IA, false);
  BB->IA->visitNormalPredecessorsBW(BB, &V, /* ctx = */0);
  V.doMerge();

  BB->tlStore = V.newMap;

}

// Find tentative loads across this whole context.
void InlineAttempt::findTentativeLoads(bool commitDisabledHere, bool secondPass) {

  if(isRootMainCall()) {
    BBs[0]->tlStore = new TLLocalStore(0);
    BBs[0]->tlStore->allOthersClobbered = false;
  }

  // If frameSize is -1 then this function does not alloca
  // so there's no need to add a stack frame to represent our objects.
  if(invarInfo->frameSize != -1 || !Callers.size()) {
    BBs[0]->tlStore = BBs[0]->tlStore->getWritableFrameList();
    BBs[0]->tlStore->pushStackFrame(this);
  }

  findTentativeLoadsInLoop(0, commitDisabledHere, secondPass);

}

// SI read IVS from ReadPtr[ReadOffset:ReadOffset+ReadSize]. If IVS refers to an unavailable pointer or FD,
// clobber ReadPtr as we cannot check the read was as expected.
bool IntegrationAttempt::squashUnavailableObject(ShadowInstruction& SI, const ImprovedValSetSingle& IVS, bool inLoopAnalyser, ShadowValue ReadPtr, int64_t ReadOffset, uint64_t ReadSize) {

  bool squash = false;

  for(uint32_t i = 0, ilim = IVS.Values.size(); i != ilim && !squash; ++i) {

    const ImprovedVal& IV = IVS.Values[i];

    if(IVS.SetType == ValSetTypePB) {

      // Stack objects are always available, so no need to check them.
      if(IV.V.isPtrIdx() && IV.V.getFrameNo() == -1) {

	// Globals too:
	AllocData* AD = getAllocData(IV.V);
	if(AD->allocValue.isInst()) {

	  if(AD->isCommitted && !AD->committedVal)
	    squash = true;

	}

      }

    }
    else if(IVS.SetType == ValSetTypeFD) {

      if(IV.V.isFdIdx()) {

	FDGlobalState& FDGS = pass->fds[IV.V.getFd()];
	if(FDGS.isCommitted && !FDGS.CommittedVal)
	  squash = true;

      }

    }

  }

  if(squash) {

    release_assert((!inLoopAnalyser) && "TODO: squashUnavailableObject implementation for loops");

    errs() << "Squash ";
    IVS.print(errs(), false);
    errs() << " read by " << itcache(&SI) << "\n";

    // Instruction no longer checkable:
    SI.isThreadLocal = TLS_NEVERCHECK;

    // Overwrite the pointer in the store to prevent future readers from encountering it again.
    ImprovedValSetSingle OD(ValSetTypeUnknown, true);
    ImprovedValSetSingle ReadP;
    getImprovedValSetSingle(ReadPtr, ReadP);
    
    release_assert(ReadP.SetType == ValSetTypePB && ReadP.Values.size());

    for(uint32_t i = 0, ilim = ReadP.Values.size(); i != ilim; ++i)
      ReadP.Values[i].Offset += ReadOffset;

    executeWriteInst(&ReadPtr, ReadP, OD, ReadSize, &SI);

  }

  return squash;

}

// SI's result is PB. Check whether it mentions any unavailable pointers or file descriptors,
// and if it does clobber the memory SI read it from.
void IntegrationAttempt::squashUnavailableObjects(ShadowInstruction& SI, ImprovedValSet* PB, bool inLoopAnalyser) {

  if(ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(PB)) {
    if(squashUnavailableObject(SI, *IVS, inLoopAnalyser, SI.getOperand(0), 0, GlobalTD->getTypeStoreSize(SI.getType())))
      IVS->setOverdef();
  }
  else {

    ImprovedValSetMulti* IVM = cast<ImprovedValSetMulti>(PB);
    for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), itend = IVM->Map.end();
	it != itend; ++it) {

      if(squashUnavailableObject(SI, it.value(), inLoopAnalyser, SI.getOperand(0), it.start(), it.stop() - it.start())) {
	ImprovedValSetSingle OD(it.value().SetType, true);
	uint64_t oldStart = it.start(), oldStop = it.stop();
	it.erase();
	it.insert(oldStart, oldStop, OD);
      }

    }

  }

}

// The result of this load (or data read by this copy instruction) may contain pointers or
// FDs which are not available because their defining context is not going to be committed,
// but it requires a check and the check cannot be synthesised.
// Therefore replace them with Unknown. The replacement is done using executeWriteInst to emulate
// a clobbering write over the memory that held the unverifiable pointer.
void IntegrationAttempt::squashUnavailableObjects(ShadowInstruction& SI, bool inLoopAnalyser) {

  if(inst_is<LoadInst>(&SI) || inst_is<AtomicCmpXchgInst>(&SI)) {

    if(SI.i.PB)
      squashUnavailableObjects(SI, SI.i.PB, inLoopAnalyser);

  }
  else {

    // Copy instruction.
    DenseMap<ShadowInstruction*, SmallVector<IVSRange, 4> >::iterator findit = pass->memcpyValues.find(&SI);
    if(findit != pass->memcpyValues.end()) {

      for(SmallVector<IVSRange, 4>::iterator it = findit->second.begin(), itend = findit->second.end();
	  it != itend; ++it) {

	if(squashUnavailableObject(SI, it->second, inLoopAnalyser, SI.getCopySource(), it->first.first, it->first.second - it->first.first)) {

	  it->second.setOverdef();

	  // Undo storing the pointer or FD.

	  ImprovedValSetSingle OD(ValSetTypeUnknown, true);

	  ShadowValue WritePtr = SI.getCopyDest();
	  ImprovedValSetSingle WriteP;
	  getImprovedValSetSingle(WritePtr, WriteP);

	  int64_t WriteOffset = it->first.first;
	  uint64_t WriteSize = it->first.second - it->first.first;
    
	  release_assert(WriteP.SetType == ValSetTypePB && WriteP.Values.size());

	  for(uint32_t i = 0, ilim = WriteP.Values.size(); i != ilim; ++i)
	    WriteP.Values[i].Offset += WriteOffset;

	  executeWriteInst(&WritePtr, WriteP, OD, WriteSize, &SI);

	}

      }

    }

  }

}

// If this load read a pointer or FD that is currently unrealisable (i.e. has been previously committed
// but currently has no committed value), volunteer to replace it, becoming the new definitive version,
// if SI is always executed and thus this version must be reachable from all (future) users.
void IntegrationAttempt::replaceUnavailableObjects(ShadowInstruction& SI, bool inLoopAnalyser) {

  if(inLoopAnalyser)
    return;

  if(inst_is<LoadInst>(&SI) || inst_is<CallInst>(&SI) || inst_is<InvokeInst>(&SI)) {

    if(SI.parent->status != BBSTATUS_CERTAIN)
      return;

    ShadowValue Base;
    int64_t Offset;
    if(getBaseAndConstantOffset(ShadowValue(&SI), Base, Offset, false)) {
      
      if(Base.isPtrIdx() && Base.getFrameNo() == -1) {

	AllocData* AD = getAllocData(Base);
	if(AD->isCommitted && !AD->committedVal) {

	  // This means that the save phase will record the new reference and patch refs will be accrued
	  // in the meantime.
	  errs() << itcache(&SI) << " stepping up as new canonical reference for " << itcache(Base) << "\n";
	  AD->isCommitted = false;
	  AD->allocValue = ShadowValue(&SI);
	  // Should be safe to change the allocType, as until now the allocation had no examplar pointer
	  // and thus could not be referenced.
	  AD->allocType = SI.getType();
	  release_assert(isa<PointerType>(AD->allocType));

	}

      }

    }
    else {

      ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(SI.i.PB);
      if(IVS && IVS->Values.size() == 1 && IVS->SetType == ValSetTypeFD && IVS->Values[0].V.isFdIdx()) {

	int32_t FD = IVS->Values[0].V.getFd();
	FDGlobalState& FDGS = pass->fds[FD];

	if(FDGS.isCommitted && !FDGS.CommittedVal) {

	  errs() << itcache(&SI) << " stepping up as new canonical reference for " << itcache(IVS->Values[0].V) << "\n";
	  FDGS.isCommitted = false;
	  FDGS.SI = &SI;

	}

      }

    }

  }

}

// Main entry point for updating the tentative loads map according to SI's effects.
void IntegrationAttempt::TLAnalyseInstruction(ShadowInstruction& SI, bool commitDisabledHere, bool secondPass, bool inLoopAnalyser) {

  // Note that TLS_NEVERCHECK may have been assigned already during the main analysis phase,
  // signifying a load from a known thread-local object.

  if(SI.readsMemoryDirectly()) {

    // Ordinary load or memcpy, without memory ordering constraints.
    // Check this value if a previous memory op has rendered it uncertain.

    // Known that we must check when this block is reached from a loop preheader?
    // If so whether it is tentative from the latch is irrelevant.
    if(secondPass && SI.isThreadLocal == TLS_MUSTCHECK)
      return;
    
    if(SI.isThreadLocal != TLS_NEVERCHECK)
      SI.isThreadLocal = shouldCheckLoad(SI);
    
    if(SI.isThreadLocal == TLS_MUSTCHECK) {

      readsTentativeData = true;
      squashUnavailableObjects(SI, inLoopAnalyser);
      
    }
    else {

      replaceUnavailableObjects(SI, inLoopAnalyser);

    }

  }
  else if(inst_is<CallInst>(&SI) || inst_is<InvokeInst>(&SI)) {
      
    // This is a little awkwardly placed since expanded calls are not tentative loads,
    // but this way it's together with load instructions replacing an unavailable object.
    replaceUnavailableObjects(SI, inLoopAnalyser);

  }
  else {

    if(SI.isThreadLocal == TLS_NEVERCHECK)
      return;

  }
  
  updateTLStore(&SI, !commitDisabledHere);

}

// Entry point for discovering a fixed-point solution for a general loop iteration. For example,
// in a simple case we'll have to check a load in the loop header if it could be interfered with by
// concurrent thread action either in the preheader or in the latch block.
// commitDisabledHere notes that this context won't generate specialised code, so we can't
// emit checks, only note memory that needs checking in the future.
// secondPass indicates this is the second time walking this context so loop latch edges will already have
// an associated TLStore.
void IntegrationAttempt::findTentativeLoadsInUnboundedLoop(const ShadowLoopInvar* UL, bool commitDisabledHere, bool secondPass) {

  ShadowBB* BB = getBB(UL->headerIdx);

  // Give header its store:
  BB->tlStore = getBB(UL->preheaderIdx)->tlStore;
  
  if(!edgeIsDead(getBBInvar(UL->latchIdx), getBBInvar(UL->headerIdx))) {

    if(!secondPass) {
      // Passing true for the last parameter causes the store to be given to the header from the latch
      // and not to any exit blocks. 
      findTentativeLoadsInLoop(UL, commitDisabledHere, false, true);
      BB->tlStore = getBB(UL->latchIdx)->tlStore;
    }
    // Second pass, unifying checks implied by the latch-to-header course
    // with those needed when entering from the header.
    findTentativeLoadsInLoop(UL, commitDisabledHere, true);

  }
  else {

    // Latch edge has been killed, despite this being a general iteration. One pass will suffice.
    findTentativeLoadsInLoop(UL, commitDisabledHere, secondPass);

  }

}

// Find tentative loads within loop L. commitDisabledHere and secondPass have the same meaning as above;
// latchToHeader indicates we should retain TLStores at each loop latch edge for consumption during the second pass.
// (!secondPass) does not necessarily imply latchToHeader, e.g. in the case where a latch edge is dead.
// This will recurse into each child context as it is encountered.
void IntegrationAttempt::findTentativeLoadsInLoop(const ShadowLoopInvar* L, bool commitDisabledHere, bool secondPass, bool latchToHeader) {

  // Don't repeat search due to sharing:
  if(tentativeLoadsRun)
    return;

  // Bump progress bar:
  TLProgress();

  uint32_t startIdx;
  if(L)
    startIdx = L->headerIdx;
  else
    startIdx = 0;

  // For each block within loop L:
  for(uint32_t i = startIdx, ilim = nBBs + BBsOffset; i != ilim && ((!L) || L->contains(getBBInvar(i)->naturalScope)); ++i) {

    ShadowBB* BB = getBB(i);
    // Skip killed block:
    if(!BB)
      continue;

    // Entering a child loop?
    if(BB->invar->naturalScope != L) {

      const ShadowLoopInvar* NewLInfo = BB->invar->naturalScope;

      PeelAttempt* LPA;
      // If we have a child context and have established the loop's iteration count:
      if((LPA = getPeelAttempt(BB->invar->naturalScope)) && LPA->isTerminated()) {

	// Loop header gets its TLStore from the preheader:
	LPA->Iterations[0]->BBs[0]->tlStore = getBB(NewLInfo->preheaderIdx)->tlStore;
	bool commitDisabled = commitDisabledHere || !LPA->isEnabled();
	uint32_t latchIdx = NewLInfo->latchIdx;

	// Pass the TLStore through each iteration in turn:
	for(uint32_t j = 0, jlim = LPA->Iterations.size(); j != jlim; ++j) {

	  LPA->Iterations[j]->findTentativeLoadsInLoop(BB->invar->naturalScope, commitDisabled, secondPass);
	  // Pass the TLStore over the latch edge:
	  if(j + 1 != jlim)
	    LPA->Iterations[j + 1]->BBs[0]->tlStore = LPA->Iterations[j]->getBB(latchIdx)->tlStore;

	}
	
      }
      else {

	// Loop is unbounded:
	findTentativeLoadsInUnboundedLoop(BB->invar->naturalScope, 
					  commitDisabledHere || (LPA && !LPA->isEnabled()), // Is commit disabled for the child?
					  secondPass);

      }

      // Advance 'i' past the loop:
      while(i != ilim && BB->invar->naturalScope->contains(getBBInvar(i)->naturalScope))
	++i;
      --i;
      continue;

    }

    // Merge predecessor blocks' TLStores:
    if(i != startIdx)
      doTLStoreMerge(BB);

    // Pass the TL store through any path conditions at the top of this block:
    TLWalkPathConditions(BB, !commitDisabledHere, secondPass);

    bool brokeOnUnreachableCall = false;

    // Enact each instruction w.r.t. this block's TLStore.
    // Recurse into child function contexts on a call/invoke instruction.
    for(uint32_t j = 0, jlim = BB->invar->insts.size(); j != jlim; ++j) {

      ShadowInstruction& SI = BB->insts[j];
      TLAnalyseInstruction(SI, commitDisabledHere, secondPass, false);
      
      if(InlineAttempt* IA = getInlineAttempt(&SI)) {

	// Pass our TLStore in:
	IA->BBs[0]->tlStore = BB->tlStore;
	IA->findTentativeLoads(commitDisabledHere || !IA->isEnabled(), secondPass);
	// Merge return block TLStores:
	doTLCallMerge(BB, IA);

	if(!BB->tlStore) {

	  // Call exit unreachable
	  brokeOnUnreachableCall = true;
	  break;

	}	    

      }

    }

    if(!BB->tlStore) {

      // Block doesn't have a store due to a never-returns call.
      // Can't have any successors either in this case.

      release_assert(brokeOnUnreachableCall);
      continue;

    }

    // Give a store copy to each successor block that needs it. If latchToHeader is true,
    // ignore branches to outside the current loop; otherwise ignore any latch->header edge.

    for(uint32_t i = 0; i < BB->invar->succIdxs.size(); ++i) {

      if(!BB->succsAlive[i])
	continue;
      
      ShadowBBInvar* SuccBBI = getBBInvar(BB->invar->succIdxs[i]);
      if(L) {

	if(L != this->L && latchToHeader && !L->contains(SuccBBI->naturalScope))
	  continue;
	else if(L != this->L && (!latchToHeader) && SuccBBI->idx == L->headerIdx) {
	  release_assert(BB->invar->idx == L->latchIdx);
	  continue;
	}

      }

      // Create a store reference for each live successor
      ++BB->tlStore->refCount;

    }

    // Drop stack allocations here.

    if(BB->invar->succIdxs.size() == 0) {

      if(invarInfo->frameSize != -1) {
	BB->tlStore = BB->tlStore->getWritableFrameList();
	BB->tlStore->popStackFrame();
      }

    }

    // Drop the reference belonging to this block.
    // Return blocks need to keep their references until they're consumed by doTLCallMerge.

    if(!isa<ReturnInst>(BB->invar->BB->getTerminator()))
      SAFE_DROP_REF(BB->tlStore);
    
  }

}

// Stats interface -- count instructions that need a runtime check. Recurse into uncommitted
// child contexts.
void IntegrationAttempt::countTentativeInstructions() {

  if(isCommitted())
    return;

  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i);
    ShadowBB* BB = getBB(*BBI);
    if(!BB)
      continue;

    if(BBI->naturalScope != L) {

      const ShadowLoopInvar* subL = immediateChildLoop(L, BBI->naturalScope);
      PeelAttempt* LPA;
      if((LPA = getPeelAttempt(subL)) && LPA->isTerminated()) {

	while(i != ilim && subL->contains(getBBInvar(i)->naturalScope))
	  ++i;
	--i;
	continue;

      }

    }

    for(uint32_t j = 0, jlim = BBI->insts.size(); j != jlim; ++j) {

      ShadowInstruction* SI = &BB->insts[j];

      // This should count only instructions that are checked because their result might be
      // invalidated by the concurrent action of other threads in the same address space.
      // Instructions with SI->needsRuntimeCheck set are checked to implement a path condition
      // or other check and so should not be included in the count.
      
      if(requiresRuntimeCheck2(ShadowValue(SI), false) && SI->needsRuntimeCheck == RUNTIME_CHECK_NONE)
	++checkedInstructionsHere;

    }

  }

  checkedInstructionsChildren = checkedInstructionsHere;

  for(IAIterator it = child_calls_begin(this), itend = child_calls_end(this); it != itend; ++it) {

    it->second->countTentativeInstructions();
    checkedInstructionsChildren += it->second->checkedInstructionsChildren;

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    if(!it->second->isTerminated())
      continue;

    for(uint32_t i = 0, ilim = it->second->Iterations.size(); i != ilim; ++i) {
     
      it->second->Iterations[i]->countTentativeInstructions();
      checkedInstructionsChildren += it->second->Iterations[i]->checkedInstructionsChildren;

    }

  }

}

// Any runtime checks needed within this loop?
bool PeelAttempt::containsTentativeLoads() {

  for(uint32_t i = 0, ilim = Iterations.size(); i != ilim; ++i)
    if(Iterations[i]->containsTentativeLoads())
      return true;

  return false;

}

// Any runtime checks needed within this context?
bool IntegrationAttempt::containsTentativeLoads() {

  return readsTentativeData;

}

// The tentative loads passlet has already run at this point.
// Check whether we found that V is an instruction requiring a runtime
// check; if includeSpecialChecks is set include checking files for
// concurrent modification which is not really the purview of the TL pass
// but is convenient to include here.
bool llvm::requiresRuntimeCheck(ShadowValue V, bool includeSpecialChecks) {

  if(GlobalIHP->omitChecks)
    return false;

  if(!V.isInst())
    return false;

  return V.u.I->parent->IA->requiresRuntimeCheck2(V, includeSpecialChecks);

}

// As above.
bool IntegrationAttempt::requiresRuntimeCheck2(ShadowValue V, bool includeSpecialChecks) {

  release_assert(V.isInst());
  ShadowInstruction* SI = V.u.I;

  // Nothing to check?
  if(SI->getType()->isVoidTy())
    return false;

  // No result calculated to check?
  if(!SI->i.PB)
    return false;

  // Check introduced by a user assertion, or by checking that malloc doesn't fail at runtime?
  if(SI->needsRuntimeCheck == RUNTIME_CHECK_AS_EXPECTED)
    return true;

  // Check introduced by the possibility of concurrent file alteration, or a read from a FIFO
  // which might vary from our expectations?
  if(includeSpecialChecks && (SI->needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD || SI->needsRuntimeCheck == RUNTIME_CHECK_READ_MEMCMP))
    return true;

  if(inst_is<MemTransferInst>(SI) || ((!inst_is<CallInst>(SI)) && SI->readsMemoryDirectly())) {
    
    // Check introduced by the TL pass finding that this memory-reading instruction's result may be subject
    // to interference by concurrent code?
    if(SI->isThreadLocal == TLS_MUSTCHECK)
      return true;
    
  }
  else if (InlineAttempt* IA = getInlineAttempt(SI)) {

    // Check because we would ideally make checks within the context,
    // but we're not emitting a specialised version and so its return value may be questionable?
    if((!IA->isEnabled()) && IA->containsTentativeLoads())
      return !SI->i.PB->isWhollyUnknown();

  }
  else if(inst_is<PHINode>(SI)) {

    // Similarly, check that phi nodes escaping from a child loop context have their expected
    // results when we'd like to make checks during the loop but can't because we're not
    // emitting a specialised loop body?
    ShadowBB* BB = SI->parent;
    for(uint32_t i = 0, ilim = BB->invar->predIdxs.size(); i != ilim; ++i) {

      ShadowBBInvar* predBBI = getBBInvar(BB->invar->predIdxs[i]);
      if(predBBI->naturalScope != L && ((!L) || L->contains(predBBI->naturalScope))) {

	PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(L, predBBI->naturalScope));
	if(LPA && LPA->isTerminated() && (!LPA->isEnabled()) && LPA->containsTentativeLoads())
	  return !SI->i.PB->isWhollyUnknown();

      }

    }

  }

  return false;

}

// Note basic blocks which must have unspecialised versions available,
// in case we fail a runtime check and bail to unspecialised code.
void IntegrationAttempt::addCheckpointFailedBlocks() {

  if(isCommitted())
    return;

  // For each block within this context:
  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i);
    ShadowBB* BB = getBB(*BBI);

    if(!BB)
      continue;

    if(BBI->naturalScope != L) {

      const ShadowLoopInvar* subL = immediateChildLoop(L, BBI->naturalScope);
      PeelAttempt* LPA;

      if((LPA = getPeelAttempt(subL)) && LPA->isTerminated() && LPA->isEnabled()) {

	// We'll emit specialised code per iteration. Check for spec-to-unspec edges
	// in each such iteration.
	for(uint32_t k = 0, klim = LPA->Iterations.size(); k != klim; ++k)
	  LPA->Iterations[k]->addCheckpointFailedBlocks();	

	// Skip past the loop blocks.
	while(i != ilim && subL->contains(getBBInvar(i)->naturalScope))
	  ++i;
	--i;
	continue;
	
      }

    }

    // For each instruction in this block:
    for(uint32_t j = 0, jlim = BBI->insts.size(); j != jlim; ++j) {

      ShadowInstruction* SI = &BB->insts[j];
      InlineAttempt* IA;

      if(requiresRuntimeCheck2(ShadowValue(SI), false) || SI->needsRuntimeCheck == RUNTIME_CHECK_READ_MEMCMP) {

	// Loop exit PHIs that need testing will be tested after the PHIs are all evaluated, rather
	// than introduce a branch after each one.
	if(inst_is<PHINode>(SI) && (j + 1) != jlim && inst_is<PHINode>(&BB->insts[j+1]))
	  continue;

     	// Note that we need unspecialised block variants available from this instruction's successor onwards.
	// Invoke instruction? (Only an invoke could be a terminator, and also produce a value that needs checking)
	if(j == jlim - 1)
	  getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(BB->invar->succIdxs[0], 0);
	else
	  getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(i, j + 1);

      }
      else if(SI->needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD) {

	// Special checks *precede* the instruction, hence 'j' vs. 'j + 1' above.
	getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(i, j);

      }
      else if((IA = getInlineAttempt(SI)) && IA->isEnabled()) {

	// Recurse into child call context.
	IA->addCheckpointFailedBlocks();

	// If the call may bail to unspecialised code internally we'll need to bail ourselves
	// after it returns.
	if(IA->hasFailedReturnPath()) {

	  // If this is the block terminator then it must be an invoke instruction,
	  // the only kind of terminator that produces a checkable value.
	  // If it is an invoke, mark the normal continuation reachable on failure.
	  if(j == jlim - 1)
	    getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(BB->invar->succIdxs[0], 0);
	  else
	    getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(i, j + 1);

	}

      }

    }

  }

}

// We've decided that context IA, called from SI, will not have a specialised variant in the final program.
// Rerun tentative load analysis now that we know we won't be able to emit any inline checks in specialised code.
void llvm::rerunTentativeLoads(ShadowInstruction* SI, InlineAttempt* IA, bool inLoopAnalyser) {

  // This indicates the call never returns, so there's nobody to consume a TLStore.
  if(!SI->parent->tlStore)
    return;

  if(IA->readsTentativeData) {

    // There may have been thread interference during the function, and/or it may have read data
    // that needed checking from prior interference and may have used it, unchecked, to calculate
    // its return value or store values to memory. Everything needs checking at this point.
    errs() << "Warning: disabled context " << IA->SeqNumber << " reads tentative information\n";
    SI->parent->tlStore = SI->parent->tlStore->getEmptyMap();
    SI->parent->tlStore->allOthersClobbered = true;
    IA->backupTlStore->dropReference();

    // Note that if IA returns a pointer we won't be able to directly refer to its allocation site.
    if(IA->returnValue)
      SI->parent->IA->squashUnavailableObjects(*SI, IA->returnValue, inLoopAnalyser);

  }
  else {

    // It does not corrupt state, but it does not itself perform checks.
    // Undo any check elimination performed within the function.
    release_assert(IA->backupTlStore);
    SI->parent->tlStore->dropReference();
    SI->parent->tlStore = IA->backupTlStore;

  }

}
