// Implement the main loop for exploring and specialising a program.
// Algorithm:
// For each BB in a topologically ordered walk of the CFG:
// Check scope (see if we need to enter a loop, ignore because out of scope, etc)
// checkBlock it. If it hasn't been created then it has no live predecessors; skip.
// If it's the top of a loop:
//   Open up the loop, investigate within the loop according to the same rules.
//   If we didn't establish that it terminates analyse for invariants (in parent scope).
// Otherwise, for each instruction:
//   If it's a store, memcpy, memset or other memory-writing instruction (including read from file), modify the local store.
//   Elif it's a load instruction, try to read from the block-local store
//   Elif it's a VFS call, try to forward it.
//   Elif it's an expandable call (and e.g. certainty / recursion doesn't forbid it), expand it and recurse.
//   Else, (or if it's a load not yet resolved), try to constant fold it.
//
// For the topo walk, use reverse postorder DFS, where loop headers are entered in the ordering
// implying that we should at that point enter the loop rather than listing all blocks in some order.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/BasicBlock.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

bool InlineAttempt::analyseWithArgs(bool inLoopAnalyser, bool inAnyLoop) {

  bool anyChange = false;

  for(unsigned i = 0; i < F.arg_size(); ++i) {

    ShadowArg* SArg = &(argShadows[i]);
    bool ign;
    anyChange |= tryEvaluate(ShadowValue(SArg), inLoopAnalyser, ign);

  }

  anyChange |= analyse(inLoopAnalyser, inAnyLoop);
  return anyChange;

}

void InlineAttempt::getInitialStore() {

  // Take our caller's store; they will make a new one
  // upon return.

  if(CI)
    BBs[0]->localStore = CI->parent->localStore;
  else
    BBs[0]->localStore = new LocalStoreMap(0);

  if(invarInfo->frameSize != -1)
    BBs[0]->pushStackFrame(this);

}

void PeelIteration::getInitialStore() {
  
  if(iterationCount == 0) {

    // Borrow the preheader's store read-only (in case we fail to terminate
    // then the preheader store will be needed again)
    BBs[0]->localStore = parent->getBB(parentPA->invarInfo->preheaderIdx)->localStore;
    BBs[0]->localStore->refCount++;

  }
  else {

    // Take the previous latch's store
    BBs[0]->localStore = parentPA->Iterations[iterationCount-1]->getBB(parentPA->invarInfo->latchIdx)->localStore;

  } 

}

bool IntegrationAttempt::analyse(bool inLoopAnalyser, bool inAnyLoop) {

  bool anyChange = false;

  anyChange |= createEntryBlock();

  getInitialStore();

  for(uint32_t i = BBsOffset; i < (BBsOffset + nBBs); ++i) {

    // analyseBlock can increment i past loops
    anyChange |= analyseBlock(i, inLoopAnalyser, inAnyLoop, i == BBsOffset, L);

  }

  return anyChange;

}

void IntegrationAttempt::analyse() {

  analyse(false, false);

}

bool PeelAttempt::analyse() {
  
  bool anyChange = false;

  for(PeelIteration* PI = Iterations[0]; PI; PI = PI->getOrCreateNextIteration()) {

    anyChange |= PI->analyse(false, true);

  }

  Iterations.back()->checkFinalIteration();
  if(!isTerminated())
    dropNonterminatedStoreRefs();
 
  return anyChange;

}

#define LFV3(x) do {} while(0);

bool IntegrationAttempt::analyseBlock(uint32_t& blockIdx, bool inLoopAnalyser, bool inAnyLoop, bool skipStoreMerge, const Loop* MyL) {

  ShadowBB* BB = getBB(blockIdx);
  if(!BB)
    return false;

  bool anyChange = false;

  // Use natural scope rather than scope because even if a loop is
  // ignored we want to notice that it exists so we can call analyseLoop
  ShadowBBInvar* BBI = BB->invar;
  const Loop* BBL = BBI->naturalScope;

  if(BBL != MyL) {

    BB->inAnyLoop = true;
    inAnyLoop = true;

    // By construction of our top-ordering, must be a loop entry block.
    release_assert(BBL && "Walked into root context?");

    // Now explore the loop, if possible.
    // At the moment can't ever happen inside the loop analyser.
    PeelAttempt* LPA = 0;
    if(!inLoopAnalyser) {
      if((LPA = getOrCreatePeelAttempt(BBL)))
	LPA->analyse();
    }

    // Analyse for invariants if we didn't establish that the loop terminates.
    if((!LPA) || !LPA->isTerminated()) {

      anyChange |= analyseLoop(BBL, inLoopAnalyser);

    }
    else {

      // The loop preheader's local store was copied by the loop analysis assuming we'd
      // need it to analyse the loop body, but we've found the loop terminates; drop the extra ref.
      ShadowLoopInvar* LInfo = invarInfo->LInfo[BBL];
      getBB(LInfo->preheaderIdx)->localStore->dropReference();

      // Copy edges found always dead to local scope, to accelerate edgeIsDead queries without
      // checking every iteration every time.
      copyLoopExitingDeadEdges(LPA);

    }

    // Advance the main loop past this loop. Loop blocks are always contiguous in the topo ordering.
    while(blockIdx < invarInfo->BBs.size() && BBL->contains(getBBInvar(blockIdx)->naturalScope))
      ++blockIdx;
    --blockIdx;
      
    return anyChange;

  }

  BB->inAnyLoop = inAnyLoop;
   
  if(!skipStoreMerge) {

    // Loop headers and entry blocks are given their stores in other ways
    // If doBlockStoreMerge returned false this block isn't currently reachable.
    // See comments in that function for reasons why that can happen.
    if(!doBlockStoreMerge(BB))
      return false;

  }

  LFV3(errs() << "Block " << F.getName() << "/" << BB->invar->BB->getName() << " stack height " << BB->localStore->frames.size() << "\n");

  LFV3(errs() << "  Start block " << BB->invar->BB->getName() << " store " << BB->localStore << " refcount " << BB->localStore->refCount << "\n");

  LFV3(errs() << "Entering block " << BB->invar->BB->getName() << " with store:\n");
  LFV3(BB->localStore->print(errs()));

  // Else we should just analyse this block here.
  anyChange |= analyseBlockInstructions(BB, 
					/* skip successor creation = */ false, 
					inLoopAnalyser, inAnyLoop);

  LFV3(errs() << "  End block " << BB->invar->BB->getName() << " store " << BB->localStore << " refcount " << BB->localStore->refCount << "\n");

  return anyChange;

}

// Returns true if there was any change
bool IntegrationAttempt::analyseBlockInstructions(ShadowBB* BB, bool skipTerminatorEval, bool inLoopAnalyser, bool inAnyLoop) {

  bool anyChange = false;
  bool loadedVarargsHere = false;

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* SI = &(BB->insts[i]);
    ShadowInstructionInvar* SII = SI->invar;
    Instruction* I = SII->I;

    if(inst_is<TerminatorInst>(SI)) {
      if(skipTerminatorEval)
	return anyChange;
      // Call tryEvalTerminator regardless of scope.
      anyChange |= tryEvaluateTerminator(SI, loadedVarargsHere);
      continue;
    }

    switch(I->getOpcode()) {

    case Instruction::Alloca:
      executeAllocaInst(SI);
      continue;
    case Instruction::Store:
      executeStoreInst(SI);
      continue;
    case Instruction::Call: 
      {
	if(tryPromoteOpenCall(SI))
	  continue;
	if(tryResolveVFSCall(SI))
	  continue;
      
	bool created;
	if(InlineAttempt* IA = getOrCreateInlineAttempt(SI, false, created)) {
	  anyChange |= created;
	  anyChange |= IA->analyseWithArgs(inLoopAnalyser, inAnyLoop);
	  doCallStoreMerge(SI);
	  if(!SI->parent->localStore) {

	    // Call must have ended in unreachable.
	    // Don't bother analysing the rest of this path.
	    return anyChange;

	  }
	}
	else {
	  // For special calls like malloc this might define a return value.
	  executeUnexpandedCall(SI);
	  continue;
	}
      }

      // Fall through to try to get the call's return value

    }

    anyChange |= tryEvaluate(ShadowValue(SI), inLoopAnalyser, loadedVarargsHere);

  }

  return anyChange;

}

void IntegrationAttempt::releaseLatchStores(const Loop* L) {

  // Release loops belonging to sub-calls and loops:

  ShadowLoopInvar* LInfo;
  uint32_t startBlock;
  if(L) {
    LInfo = invarInfo->LInfo[L];
    startBlock = LInfo->headerIdx;
  }
  else {
    LInfo = 0;
    startBlock = 0;
  }

  for(uint32_t i = startBlock; i < (BBsOffset + nBBs); ++i) {

    if(L && !L->contains(getBBInvar(i)->naturalScope))
      break;

    ShadowBB* BB = getBB(i);
    if(!BB)
      continue;

    ShadowBBInvar* BBI = BB->invar;
    const Loop* BBL = BBI->naturalScope;
   
    if(BBL != L) {

      releaseLatchStores(BBL);

      // Skip past the loop:
      while(i < (BBsOffset + nBBs) && BBL->contains(getBBInvar(i)->naturalScope))
	++i;
      --i;
      
    }
    else {

      // Look for calls with subloops:
      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	ShadowInstruction* SI = &(BB->insts[j]);
	ShadowInstructionInvar* SII = SI->invar;
	Instruction* I = SII->I;

	if(CallInst* CI = dyn_cast<CallInst>(I)) {

	  if(InlineAttempt* IA = getInlineAttempt(CI))
	    IA->releaseLatchStores(0);

	}

      }

    }

  }
   
  // Release here:

  if(LInfo) {
    ShadowBBInvar* HBBI = getBBInvar(LInfo->headerIdx);
    if(!edgeIsDead(getBBInvar(LInfo->latchIdx), HBBI)) {
      // Release the latch store that the header will not use again:
      ShadowBB* LBB = getBB(LInfo->latchIdx);
      LBB->localStore->dropReference();
    }
  }

}

// nestedLoop indicates we're being analysed in the context of a loop further out,
// either in our call or a parent call.
bool IntegrationAttempt::analyseLoop(const Loop* L, bool nestedLoop) {

  ShadowLoopInvar* LInfo = invarInfo->LInfo[L];
  bool anyChange = true;
  bool firstIter = true;
  bool everChanged = false;
  uint64_t iters = 0;

  ShadowBB* PHBB = getBB(LInfo->preheaderIdx);
  ShadowBB* HBB = getBB(LInfo->headerIdx);

  LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount at entry: " << PHBB->localStore->refCount << "\n");

  // Stop iterating if we show that the latch edge died!
  while(anyChange && (firstIter || !edgeIsDead(getBBInvar(LInfo->latchIdx), HBB->invar))) {
    
    ++iters;

    // Give the preheader store an extra reference to ensure it is never modified.
    // This ref corresponds to ph retaining its reference (h has already been given one by ph's successor code).
    PHBB->localStore->refCount++;

    {

      if(!firstIter) {

	// Drop store references at exit edges: we're going around again.
	for(std::vector<std::pair<uint32_t, uint32_t> >::iterator it = LInfo->exitEdges.begin(),
	      itend = LInfo->exitEdges.end(); it != itend; ++it) {

	  ShadowBB* BB = getBB(it->first);
	  if(BB && !edgeIsDead(BB->invar, getBBInvar(it->second))) {
	    LFV3(errs() << "Drop exit edge " << BB->invar->BB->getName() << " -> " << getBBInvar(it->second)->BB->getName() << " with store " << BB->localStore << "\n");
	    BB->localStore->dropReference();
	  }

	}

      }

      ShadowBB* LBB = getBB(LInfo->latchIdx);
      if(LBB && LBB->localStore) {
	// We've analysed this loop before -- we must be under analysis as a nested loop.
	// If our latch edge lives we should use its store ref, which was saved last time around.
	if(!edgeIsDead(LBB->invar, HBB->invar))
	  firstIter = false;
      }

      MergeBlockVisitor V(false);

      if(!firstIter) {

	// Merge the latch store with the preheader store:
	release_assert(LBB && "Iterating on a loop with a dead latch block?");
	V.visit(LBB, 0, false);
	V.visit(PHBB, 0, false);

      }
      else {

	// Give the header block the store from the preheader
	V.visit(PHBB, 0, false);

      }

      V.doMerge();
      HBB->localStore = V.newMap;

    }

    LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount after old exit elim: " << PHBB->localStore->refCount << "\n");

    anyChange = false;

    for(uint32_t i = LInfo->headerIdx; i < (BBsOffset + nBBs); ++i) {

      if(!L->contains(getBBInvar(i)->naturalScope))
	break;
      
      anyChange |= analyseBlock(i, true, true, i == LInfo->headerIdx, L);

    }

    everChanged |= anyChange;

    firstIter = false;

    LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount after block analysis: " << PHBB->localStore->refCount << "\n");

  }

  if(edgeIsDead(getBBInvar(LInfo->latchIdx), HBB->invar))
    release_assert(iters == 1 && "Loop analysis found the latch dead but not first time around?");

  // Release the preheader store that was held for merging in each iteration:
  PHBB->localStore->dropReference();

  // If this is a nested loop, hang onto the reference given from latch to header
  // for use in the next iteration of analysing this loop.
  if(!nestedLoop)
    releaseLatchStores(L);

  LFV3(errs() << "Loop " << L->getHeader()->getName() << " refcount at exit: " << PHBB->localStore->refCount << "\n");
  
  return everChanged;

}

