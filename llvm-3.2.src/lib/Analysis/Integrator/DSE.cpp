// Dead store elimination using essentially the same technique as Transforms/Scalar/DSE.cpp,
// only taking into account that we've been computing a probable flow through the program.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DataLayout.h"

#include <vector>

using namespace llvm;

static uint32_t DSEProgressN = 0;
const uint32_t DSEProgressLimit = 1000;

static void DSEProgress() {

  DSEProgressN++;
  if(DSEProgressN == DSEProgressLimit) {

    errs() << ".";
    DSEProgressN = 0;

  }

}

static void DSEInstructionDead(ShadowInstruction* SI) {

  SI->dieStatus |= INSTSTATUS_UNUSED_WRITER;

}

void TrackedStore::derefBytes(uint64_t nBytes) {

  release_assert(nBytes <= outstandingBytes);
  if(!(outstandingBytes -= nBytes)) {

    if(!isNeeded)
      DSEInstructionDead(I);

    delete this;

  }

}

static DSEMapTy::Allocator DSEMapAllocator;
static DSEMapTy DSEEmptyMap(DSEMapAllocator);
DSEMapPointer llvm::DSEEmptyMapPtr(&DSEEmptyMap, 0);

DSELocalStore* DSEMapPointer::getMapForBlock(ShadowBB* BB) {

  return BB->u.dseStore;
  
}

void TrackedAlloc::dropReference() {

  if(!(--nRefs)) {
    
    if(!isNeeded)
      DSEInstructionDead(SI);

    delete this;

  }
    

}

static bool GCStores(DSEMapTy::iterator argit) {

  uint64_t entrySize = (argit.stop() - argit.start());
  DSEMapEntry& entry = argit.val();

  for(DSEMapEntry::iterator entryit = entry.begin(); entryit != entry.end(); ++entryit) {

    TrackedStore* thisStore = *entryit;
    if(thisStore->isNeeded) {

      thisStore->derefBytes(entrySize);

      if(&*entryit == &entry.back()) {
	entry.pop_back();
	break;
      }
      else {
	std::swap(*entryit, entry.back());
	entry.pop_back();
	continue;
      }

    }

  }

  return entry.size() == 0;

}

DSEMapPointer DSEMapPointer::getReadableCopy() { 

  // At present we always do a real copy and update the byte counts of all referenced stores.
  // Take the opportunity to exclude any stores that turn out to have been needed,
  // both here and at the target (the information is of no further value).

  DSEMapTy* newMap = new DSEMapTy(DSEMapAllocator);
    
  for(DSEMapTy::iterator it = M->begin(), itend = M->end(); it != itend;) {

    DSEMapEntry& oldEntry = it.val();

    uint64_t entrySize = (it.stop() - it.start());

    if(GCStores(it)) {

      it.erase();

    }
    else {

      newMap->insert(it.start(), it.stop(), DSEMapEntry());
      DSEMapEntry* newEntry = &(newMap->find(it.start()).val());
	
      for(DSEMapEntry::iterator entryit = oldEntry.begin(); entryit != oldEntry.end(); ++entryit) {

	TrackedStore* thisStore = *entryit;
	newEntry->push_back(thisStore);
	thisStore->outstandingBytes += entrySize;

      }

      ++it;

    }

  }

  // Add a reference to the allocation:
  if(A)
    ++A->nRefs;

  return DSEMapPointer(newMap, A);

}

static void derefBytes(DSEMapEntry& entry, uint64_t nBytes) {

  for(DSEMapEntry::iterator entryit = entry.begin(); entryit != entry.end(); ++entryit)
    (*entryit)->derefBytes(nBytes);
  
}

void DSEMapPointer::release() {

  // The store entries themselves are not reference counted, so drop refs to all mentioned
  // TrackedStores and delete the map.

  for(DSEMapTy::iterator it = M->begin(), itend = M->end(); it != itend; ++it) {

    uint64_t entrySize = (it.stop() - it.start());

    DSEMapEntry& oldEntry = it.val();
    derefBytes(oldEntry, entrySize);

  }

  M->clear();

  if(A) {
    A->dropReference();
    A = 0;
  }

}

void DSEMapPointer::dropReference() { 
    
  release();
  delete M;

}

static void setAllNeeded(DSEMapEntry& entry) {

  for(DSEMapEntry::iterator it = entry.begin(), itend = entry.end(); it != itend; ++it)
    (*it)->isNeeded = true;

}

static void setAllNeeded(DSEMapTy& M) {

  for(DSEMapTy::iterator it = M.begin(), itend = M.end(); it != itend; ++it) {

    DSEMapEntry& entry = it.val();
    setAllNeeded(entry);

  }

}

static void setAllNeeded(DSELocalStore::FrameType& frame) {

  for(std::vector<DSEMapPointer>::iterator it = frame.store.begin(), itend = frame.store.end();
      it != itend; ++it) {

    if(it->isValid()) {
      setAllNeeded(*it->M);
      if(it->A)
	it->A->isNeeded = true;
    }

  }

}

static void setAllNeeded(DSELocalStore::NodeType* node, uint32_t height) {

  if(height == 0) {

    for(uint32_t i = 0, ilim = HEAPTREEORDER; i != ilim; ++i) {

      DSEMapPointer* child = (DSEMapPointer*)node->children[i];
	
      if(child && child->isValid()) {
	setAllNeeded(*child->M);
	if(child->A)
	  child->A->isNeeded = true;
      }
      
    }

  }
  else {

    for(uint32_t i = 0, ilim = HEAPTREEORDER; i != ilim; ++i) {

      DSELocalStore::NodeType* child = (DSELocalStore::NodeType*)node->children[i];
      if(child)
	setAllNeeded(child, height - 1);

    }

  }

}

static void setAllNeeded(DSELocalStore* store) {

  // No need for CoW breaks: if a location is needed, it is needed everywhere.
  for(SmallVector<DSELocalStore::FrameType*, 4>::iterator it = store->frames.begin(),
	itend = store->frames.end(); it != itend; ++it) {

    setAllNeeded(**it);

  }

  if(store->heap.height)
    setAllNeeded(store->heap.root, store->heap.height - 1);

}

void DSEMapPointer::mergeStores(DSEMapPointer* mergeFrom, DSEMapPointer* mergeTo, ShadowValue& V, DSEMerger* Visitor) {

  // Just union the two stores together. They can't be the same store.
  release_assert(mergeFrom != mergeTo && mergeFrom->M != mergeTo->M);

  // Merge the allocation tracking: target map should have it if it doesn't already.
  if((!mergeTo->A) && mergeFrom->A) {

    mergeTo->A = mergeFrom->A;
    mergeTo->A->nRefs++;

  }

  // The union should be per-byte, so insert a split in mergeTo whereever one exists in mergeFrom.
  // Take the opportunity to garbage collect: anything with isNeeded set should be omitted.

  for(DSEMapTy::iterator fromit = mergeFrom->M->begin(); fromit != mergeFrom->M->end();) {

    if(GCStores(fromit))
      fromit.erase();
    else
      ++fromit;
      
  }

  for(DSEMapTy::iterator toit = mergeTo->M->begin(); toit != mergeTo->M->end();) {

    if(GCStores(toit))
      toit.erase();
    else
      ++toit;
      
  }

  DSEMapTy::iterator fromit = mergeFrom->M->begin();

  for(DSEMapTy::iterator fromit = mergeFrom->M->begin(), fromend = mergeFrom->M->end();
      fromit != fromend; ++fromit) {

    DSEMapTy::iterator toit = mergeTo->M->find(fromit.start());

    if(toit == mergeTo->M->end() || toit.start() > fromit.start()) {

      // Fill in gap in the merge-to sequence:

      uint64_t stop;
      if(toit == mergeTo->M->end())
	stop = fromit.stop();
      else
	stop = std::min(toit.start(), fromit.stop());
      mergeTo->M->insert(fromit.start(), stop, DSEMapEntry()); 

      toit = mergeTo->M->find(fromit.start());

    }
    else if(toit.start() < fromit.start()) {

      // Break at start:

      uint64_t oldStop = toit.stop();
      toit.setStop(fromit.start());
      mergeTo->M->insert(fromit.start(), oldStop, toit.val());
       
      toit = mergeTo->M->find(fromit.start());

    }
    
    // Check for gaps within this from range:
    // This to-entry must end within the span of fromit.
    while(toit != mergeTo->M->end() && toit.stop() < fromit.stop()) {

      // Next to-entry:
      DSEMapTy::iterator nextto = toit;
      ++nextto;

      // Gap?
      if(nextto == mergeTo->M->end() || nextto.start() != toit.stop()) {

	uint64_t stop;
	if(nextto == mergeTo->M->end())
	  stop = fromit.stop();
	else
	  stop = std::min(nextto.start(), fromit.stop());
	mergeTo->M->insert(toit.stop(), stop, DSEMapEntry());
	toit = mergeTo->M->find(toit.stop());

      }

      ++toit;

    }

    // Last entry over-long?
    if(toit != mergeTo->M->end() && toit.start() < fromit.stop() && toit.stop() > fromit.stop()) {

      uint64_t oldStop = toit.stop();
      toit.setStop(fromit.stop());
      mergeTo->M->insert(fromit.stop(), oldStop, toit.val());

    }
      
  }

  // The to-sequence should now be defined everywhere the from-sequence is, and has a break
  // at least as often as the from-sequence. Add missing store refs into the to-sequence
  // and account for the new outstanding bytes that result.

  fromit = mergeFrom->M->begin();
  DSEMapTy::iterator toit = mergeTo->M->find(fromit.start());

  for(; fromit != mergeFrom->M->end(); ++fromit) {

    DSEMapEntry& fromEntry = fromit.val();
	
    for(; toit.stop() <= fromit.stop(); ++toit) {

      DSEMapEntry& toEntry = toit.val();
      uint64_t entrySize = toit.stop() - toit.start();
	
      for(DSEMapEntry::iterator it = fromEntry.begin(), itend = fromEntry.end(); it != itend; ++it) {

	TrackedStore* fromStore = *it;
	if(std::find(toEntry.begin(), toEntry.end(), fromStore) != toEntry.end())
	  continue;

	toEntry.push_back(fromStore);
	fromStore->outstandingBytes += entrySize;

      }

    }

  }

}

void DSEMapPointer::useWriters(int64_t Offset, uint64_t Size) {

  uint64_t End = (uint64_t)(Offset + Size);

  // Knock out whole map entries wherever they overlap, because records with isNeeded = true
  // are never any use and are only retained to save from having to keep a reverse index
  // from TrackedStores to maps they are stored in.

  for(DSEMapTy::iterator it = M->find(Offset), itend = M->end(); it != itend && it.start() < End; it.erase()) {
    
    DSEMapEntry& E = it.val();
    for(DSEMapEntry::iterator Eit = E.begin(), Eend = E.end(); Eit != Eend; ++Eit)
      (*Eit)->isNeeded = true;

    derefBytes(E, it.stop() - it.start());
    
  }

}

void DSEMapPointer::setWriter(int64_t Offset, uint64_t Size, ShadowInstruction* SI) {

  // Punch a hole in this map and insert SI as a new writer.
  // Release each store that drops out of the map this way.
  
  uint64_t End = (uint64_t)(Offset + Size);

  for(DSEMapTy::iterator it = M->find(Offset), itend = M->end(); it != itend && it.start() < End;) {

    if(((int64_t)it.start()) < Offset) {
      
      uint64_t oldStop = it.stop();
      it.setStop(Offset);
      derefBytes(it.val(), std::min(oldStop, End) - Offset);

      if(oldStop > End) {

	// Punched a hole in a single value: duplicate it and we're done.
	M->insert(End, oldStop, it.val());
	break;

      }

      ++it;

    }
    else if(it.stop() > End) {

      derefBytes(it.val(), End - it.start());
      it.setStart(End);

      ++it;

    }
    else {

      // Wholly within the cleared range.
      derefBytes(it.val(), it.stop() - it.start());
      it.erase();

    }

  }

  // Insert the new entry:
  TrackedStore* newStore = new TrackedStore(SI, Size);
  DSEMapEntry newEntry;
  newEntry.push_back(newStore);
  M->insert(Offset, End, newEntry);

}

DSEMapPointer* ShadowBB::getWritableDSEStore(ShadowValue O) {

  u.dseStore = u.dseStore->getWritableFrameList();
  bool isNewStore;
  DSEMapPointer* ret = u.dseStore->getOrCreateStoreFor(O, &isNewStore);

  if(isNewStore) {
    ret->M = new DSEMapTy(DSEMapAllocator);
    // The TrackedAlloc will be filled in for Allocas and mallocs by our caller.
    ret->A = 0;
  }

  return ret;

}

static bool containsUncertainPointers(ImprovedValSetSingle& IVS) {

  for(uint64_t i = 0, ilim = IVS.Values.size(); i != ilim; ++i) {
   
    if(IVS.Values[i].Offset == LLONG_MAX)
      return true;

  }

  return false;

}

static void doDSEStoreMerge(ShadowBB* BB) {

  DSEMerger V(false);
  BB->IA->visitNormalPredecessorsBW(BB, &V, /* ctx = */0);
  V.doMerge();

  BB->u.dseStore = V.newMap;

}

static void doDSECallMerge(ShadowBB* BB, InlineAttempt* IA) {

  DSEMerger V(false);
  IA->visitLiveReturnBlocks(V);
  V.doMerge();
  
  BB->u.dseStore = V.newMap;

}

void IntegrationAttempt::DSEHandleRead(ShadowValue PtrOp, uint64_t Size, ShadowBB* BB) {

  ImprovedValSetSingle IVS;
  getImprovedValSetSingle(PtrOp, IVS);

  if(IVS.isWhollyUnknown() || IVS.SetType != ValSetTypePB || containsUncertainPointers(IVS)) {

    // May read anything -- assumed to read everything.
    setAllNeeded(BB->u.dseStore);
    BB->u.dseStore = BB->u.dseStore->getEmptyMap();
    return;

  }

  for(uint64_t i = 0, ilim = IVS.Values.size(); i != ilim; ++i) {

    if(val_is<ConstantPointerNull>(IVS.Values[i].V))
      continue;

    ShadowGV* GV;
    if((GV = IVS.Values[i].V.getGV()) && GV->G->isConstant())
      continue;

    DSEMapPointer* store = BB->getWritableDSEStore(IVS.Values[i].V);
    // The allocation is needed (and no need to track it anymore).
    if(store->A) {
      store->A->isNeeded = true;
      store->A->dropReference();
      store->A = 0;
    }

    uint64_t Offset = IVS.Values[i].Offset;

    if(Offset == LLONG_MAX) {
      Offset = 0;
      Size = AliasAnalysis::UnknownSize;
    }
    
    store->useWriters(Offset, Size);

  }
      
}

void IntegrationAttempt::DSEHandleWrite(ShadowValue PtrOp, uint64_t Size, ShadowInstruction* Writer, ShadowBB* BB) {

  ShadowValue Ptr;
  int64_t Offset;
  if(!getBaseAndConstantOffset(PtrOp, Ptr, Offset))
    return;

  if(val_is<ConstantPointerNull>(Ptr))
    return;

  DSEMapPointer* store = BB->getWritableDSEStore(Ptr);
  store->setWriter(Offset, Size, Writer);

}

void InlineAttempt::tryKillStores(bool commitDisabledHere, bool disableWrites) {

  if(isRootMainCall())
    BBs[0]->u.dseStore = new DSELocalStore(0);

  if(invarInfo->frameSize != -1 || !Callers.size()) {
    BBs[0]->u.dseStore = BBs[0]->u.dseStore->getWritableFrameList();
    BBs[0]->u.dseStore->pushStackFrame(this);
  }

  tryKillStoresInLoop(0, commitDisabledHere, disableWrites);

}

void IntegrationAttempt::tryKillStoresInLoop(const Loop* L, bool commitDisabledHere, bool disableWrites, bool latchToHeader) {

  DSEProgress();

  ShadowLoopInvar* LInfo = L ? invarInfo->LInfo[L] : 0;
  
  uint32_t startIdx;
  if(L)
    startIdx = LInfo->headerIdx;
  else
    startIdx = 0;

  for(uint32_t i = startIdx, ilim = nBBs + BBsOffset; i != ilim && ((!L) || L->contains(getBBInvar(i)->naturalScope)); ++i) {

    ShadowBB* BB = getBB(i);
    if(!BB)
      continue;

    if(BB->invar->naturalScope != L) {

      ShadowLoopInvar* NewLInfo = invarInfo->LInfo[BB->invar->naturalScope];

      PeelAttempt* LPA;
      if((LPA = getPeelAttempt(BB->invar->naturalScope)) && LPA->isTerminated()) {

	LPA->Iterations[0]->BBs[0]->u.dseStore = getBB(NewLInfo->preheaderIdx)->u.dseStore;
	bool commitDisabled = commitDisabledHere || !LPA->isEnabled();
	uint32_t latchIdx = NewLInfo->latchIdx;

	for(uint32_t j = 0, jlim = LPA->Iterations.size(); j != jlim; ++j) {

	  LPA->Iterations[j]->tryKillStoresInLoop(BB->invar->naturalScope, commitDisabled, disableWrites);
	  if(j + 1 != jlim)
	    LPA->Iterations[j + 1]->BBs[0]->u.dseStore = LPA->Iterations[j]->getBB(latchIdx)->u.dseStore;

	}
	
      }
      else {

	// Give header its store:
	BB->u.dseStore = getBB(NewLInfo->preheaderIdx)->u.dseStore;

	if(!edgeIsDead(getBBInvar(NewLInfo->latchIdx), getBBInvar(NewLInfo->headerIdx))) {

	  if(!disableWrites) {
	    // Passing true for the last parameter causes the store to be given to the header from the latch
	    // and not to any exit blocks. 
	    tryKillStoresInLoop(BB->invar->naturalScope, commitDisabledHere || (LPA && !LPA->isEnabled()), false, true);
	    BB->u.dseStore = getBB(NewLInfo->latchIdx)->u.dseStore;
	  }
	  tryKillStoresInLoop(BB->invar->naturalScope, commitDisabledHere || (LPA && !LPA->isEnabled()), true);

	}
	else {

	  tryKillStoresInLoop(BB->invar->naturalScope, commitDisabledHere || (LPA && !LPA->isEnabled()), disableWrites);

	}

      }

      while(i != ilim && BB->invar->naturalScope->contains(getBBInvar(i)->naturalScope))
	++i;
      --i;
      continue;

    }

    if(i != startIdx) {

      doDSEStoreMerge(BB);

    }

    if((!pass->omitChecks) && pass->countPathConditionsAtBlockStart(BB->invar, BB->IA)) {
      
      // Reaches a path condition check, where unspecialised code might use this value.
      setAllNeeded(BB->u.dseStore);
      BB->u.dseStore = BB->u.dseStore->getEmptyMap();
      
    }

    bool brokeOnUnreachableCall = false;

    for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

      ShadowInstruction* I = &BB->insts[j];

      if(disableWrites && !(inst_is<LoadInst>(I) || inst_is<MemTransferInst>(I)))
	continue;

      // This will be a branch to unspecialised code in the output program;
      // assume store is needed if it is live over this point.
      if(requiresRuntimeCheck(ShadowValue(I), true)) {

	setAllNeeded(BB->u.dseStore);
	BB->u.dseStore = BB->u.dseStore->getEmptyMap();	

      }

      if(inst_is<MemIntrinsic>(I)) {
	
	ConstantInt* SizeC = cast_or_null<ConstantInt>(getConstReplacement(I->getCallArgOperand(2)));
	uint64_t MISize;
	if(SizeC)
	  MISize = SizeC->getZExtValue();
	else
	  MISize = AliasAnalysis::UnknownSize;

	if(inst_is<MemTransferInst>(I)) {

	  if(commitDisabledHere || I->isThreadLocal == TLS_MUSTCHECK || !canSynthMTI(I)) {

	    // If it will be emitted for real, it will read at runtime.
	    DSEHandleRead(I->getCallArgOperand(1), MISize, BB);

	  }
	  
	}

	if(disableWrites)
	  continue;

	// If the size is unknown we must assume zero.
	if(MISize != AliasAnalysis::UnknownSize)
	  DSEHandleWrite(I->getCallArgOperand(0), MISize, I, BB);


      }
      else if(inst_is<AllocaInst>(I)) {

	DSEMapPointer* store = BB->getWritableDSEStore(ShadowValue(I));
	store->A = new TrackedAlloc(I);

      }
      else if(inst_is<CallInst>(I)) {

	if(InlineAttempt* IA = getInlineAttempt(I)) {

	  IA->BBs[0]->u.dseStore = BB->u.dseStore;
	  IA->tryKillStores(commitDisabledHere || (!IA->isEnabled()), disableWrites);
	  doDSECallMerge(BB, IA);

	  if(!BB->u.dseStore) {

	    // The call never returns: no sense analysing the rest of this block.
	    // This block cannot have any live successors in this case.
	    brokeOnUnreachableCall = true;
	    break;

	  }

	}
	else {

	  DenseMap<ShadowInstruction*, ReadFile>::iterator RI = pass->resolvedReadCalls.find(I);
	  Function* F;
	  DenseMap<Function*, specialfunctions>::iterator findit;
	  if(RI != pass->resolvedReadCalls.end()) {

	    DSEHandleWrite(I->getCallArgOperand(1), RI->second.readSize, I, BB);

	  }
	  else if((F = getCalledFunction(I)) && 
		  (findit = SpecialFunctionMap.find(F)) != SpecialFunctionMap.end()) {

	    if(findit->second == SF_FREE) {

	      // Release the map and a tracked alloc reference for this location:
	      ShadowValue PtrOp = I->getCallArgOperand(0);
	      ShadowValue Ptr;
	      int64_t Offset;
	      if(!getBaseAndConstantOffset(PtrOp, Ptr, Offset))
		continue;
	      
	      if(val_is<ConstantPointerNull>(Ptr))
		continue;

	      DSEMapPointer* store = BB->getWritableDSEStore(Ptr);
	      store->release();
	      
	    }
	    else if(findit->second == SF_MALLOC || findit->second == SF_REALLOC) {

	      // Track the allocation to determine if it is unused everywhere.
	      
	      DSEMapPointer* store = BB->getWritableDSEStore(ShadowValue(I));
	      store->A = new TrackedAlloc(I);

	    }
	    else if(findit->second == SF_VACOPY) {

	      DSEHandleRead(I->getCallArgOperand(1), 24, BB);

	    }
	      
	  }
	  else if(F) {

	    if(F->doesNotAccessMemory())
	      continue;

	    // Known system calls may read from any pointer-typed argument,
	    // pending more accurate definition of their read behaviour.
	    // We'll assume they don't write at the moment, since the definitions
	    // in VFSCallModRef are /worst/ case write assumptions used for clobbering,
	    // whereas here we need /conservative/ always-overwrites information.

	    const IHPFunctionInfo* FI = GlobalIHP->getMRInfo(F);

	    if(FI) {

	      if(FI->NoModRef)
		continue;

	      FunctionType* FType = F->getFunctionType();

	      for(uint32_t arg = 0, arglim = I->getNumArgOperands(); arg != arglim; ++arg) {

		// Can't hold a pointer?
		if(GlobalAA->getTypeStoreSize(FType->getParamType(arg)) < 8)
		  continue;

		// Known not a pointer?
		ShadowValue argval = I->getCallArgOperand(arg);
		ImprovedValSetSingle argivs;
		if(getImprovedValSetSingle(argval, argivs)) {

		  if(argivs.SetType == ValSetTypeScalar || argivs.SetType == ValSetTypeFD)
		    continue;

		}

		// OK, assume the call reads any amount through the pointer.
		DSEHandleRead(argval, AliasAnalysis::UnknownSize, BB);

	      }
	    
	    }
	    else {

	      // Call with unknown properties blocks everything:
	      setAllNeeded(BB->u.dseStore);
	      BB->u.dseStore = BB->u.dseStore->getEmptyMap();

	    }

	  }
	  else {

	    // Unexpanded call blocks everything:
	    setAllNeeded(BB->u.dseStore);
	    BB->u.dseStore = BB->u.dseStore->getEmptyMap();

	  }

	}

      }
      else if(inst_is<LoadInst>(I)) {

	ShadowValue Pointer = I->getOperand(0);
	uint64_t LoadSize = GlobalAA->getTypeStoreSize(I->getType());

	// If isThreadLocal == TLS_MUSTCHECK then the load will happen for real
	// despite its known value.
	if(I->isThreadLocal != TLS_MUSTCHECK && mayBeReplaced(I) && !commitDisabledHere) {

	  // mayBeReplaced implies a single value.
	  ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(I->i.PB);
	  if(IVS->SetType == ValSetTypePB || IVS->SetType == ValSetTypeFD) {

	    ShadowValue Base = IVS->Values[0].V;
	    if((!Base.getCtx()) || Base.objectAvailable())
	      continue;

	  }
	  else {

	    continue;

	  }

	}
    
	// Otherwise the load will happen for real at runtime:
	DSEHandleRead(Pointer, LoadSize, BB);

      }
      else if(inst_is<StoreInst>(I)) {

	ShadowValue Pointer = I->getOperand(1);
	uint64_t StoreSize = GlobalAA->getTypeStoreSize(I->invar->I->getOperand(0)->getType());
	DSEHandleWrite(Pointer, StoreSize, I, BB);

      }

    }

    if(!BB->u.dseStore) {

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
	else if(L != this->L && (!latchToHeader) && SuccBBI->idx == LInfo->headerIdx) {
	  release_assert(BB->invar->idx == LInfo->latchIdx);
	  continue;
	}

      }

      // Create a store reference for each live successor
      ++BB->u.dseStore->refCount;

    }

    // Drop stack allocations here.

    if(BB->invar->succIdxs.size() == 0) {

      if(invarInfo->frameSize != -1) {
	BB->u.dseStore = BB->u.dseStore->getWritableFrameList();
	BB->u.dseStore->popStackFrame();
      }

    }

    // Drop the reference belonging to this block.

    if(!isa<ReturnInst>(BB->invar->BB->getTerminator()))
      BB->u.dseStore->dropReference();

  }

}


