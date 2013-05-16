// Implement the main loop for exploring and specialising a program.
// Algorithm:
// For each BB in a topologically ordered walk of the CFG:
// Check scope (see if we need to enter a loop, ignore because out of scope, etc)
// checkBlock it. If it's now dead, bail.
// If it's the top of a loop:
//   For outright invariants that aren't loads, do a topo walk through the loop blocks
//     ignoring the backedge (i.e. treating the blocks like they're non-loop blocks).
//   Open up the loop, investigate within the loop according to the same rules.
//   If we never made it past iteration 1, ditch the investigation so far.
//   If we didn't establish it terminates, do an invariant investigation.
// Otherwise, for each instruction:
//   If it's a load instruction, try conventional LF, or if that doesn't work, PBLF.
//   Elif it's a VFS call, try to forward it.
//   Elif it's an expandable call (and e.g. certainty / recursion doesn't forbid it), expand it and recurse.
//   Else, (or if it's a load not yet resolved), try to constant fold it, or if that doesn't work, PBCF.
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

bool InlineAttempt::analyseWithArgs(bool inLoopAnalyser) {

  bool anyChange = false;

  for(unsigned i = 0; i < F.arg_size(); ++i) {

    ShadowArg* SArg = &(argShadows[i]);
    anyChange |= tryEvaluate(ShadowValue(SArg), inLoopAnalyser);

  }

  anyChange |= analyse(inLoopAnalyser);
  return anyChange;

}

void InlineAttempt::getInitialStore() {

  // Take our caller's store; they will make a new one
  // upon return.

  if(CI)
    BBs[0]->localStore = CI->parent->localStore;
  else
    BBs[0]->localStore = new LocalStoreMap();

}

void PeelIteration::getInitialStore() {
  
  if(iterationCount == 0) {

    // Borrow the preheader's store read-only (in case we fail to terminate
    // then the preheader store will be needed again)
    BBs[0]->localStore = parent->getBB(parentPA->invarInfo->latchIdx)->localStore;
    BBs[0]->localStore->refCount++;

  }
  else {

    // Take the previous latch's store
    BBs[0]->localStore = parentPA->Iterations[iterationCount-1]->getBB(parentPA->invarInfo->latchIdx)->localStore;

  } 

}

void IntegrationAttempt::cleanupLocalStore() {}
void InlineAttempt::cleanupLocalStore() {

  localAllocas.clear();

}

bool IntegrationAttempt::analyse(bool inLoopAnalyser) {

  bool anyChange = false;

  anyChange |= createEntryBlock();

  getInitialStore();

  for(uint32_t i = BBsOffset; i < (BBsOffset + nBBs); ++i) {

    // analyseBlock can increment i past loops
    anyChange |= analyseBlock(i, inLoopAnalyser, i == BBsOffset, L);

  }

  cleanupLocalStore();

  return anyChange;

}

void IntegrationAttempt::analyse() {

  analyse(false);

}

bool PeelAttempt::analyse() {
  
  bool anyChange = false;

  for(PeelIteration* PI = Iterations[0]; PI; PI = PI->getOrCreateNextIteration()) {

    anyChange |= PI->analyse(false);

  }

  Iterations.back()->checkFinalIteration();
  if(!isTerminated()) {
    for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end();
	it != it2; ++it) {
      (*it)->dropExtraStoreRefs();
    }
  }
  
  return anyChange;

}

#define LFV3(x) x

bool IntegrationAttempt::analyseBlock(uint32_t& blockIdx, bool inLoopAnalyser, bool skipStoreMerge, const Loop* MyL) {

  ShadowBB* BB = getBB(blockIdx);
  if(!BB)
    return false;

  bool anyChange = false;

  if(!skipStoreMerge) {

    // Loop headers and entry blocks are given their stores in other ways
    doBlockStoreMerge(BB);

  }

  LFV3(errs() << "Entering block " << BB->invar->BB->getName() << " with store:\n");
  LFV3(BB->localStore->print(errs()));

  // Use natural scope rather than scope because even if a loop is
  // ignored we want to notice that it exists so we can call analyseLoopPBs.
  ShadowBBInvar* BBI = BB->invar;
  const Loop* BBL = BBI->naturalScope;
   
  if(BBL != MyL) {

    // By construction of our top-ordering, must be a loop entry block.
    release_assert(BBL && "Walked into root context?");

    // Loop invariants used to be found here, but are now explored on demand whenever a block
    // gets created that doesn't yet exist in parent scope.

    // Calculate invariants for the header block, which uniquely is created in its invariant scope
    // before being created in any child loops.

    anyChange |= analyseBlockInstructions(BB, true, false);
   
    // Now explore the loop, if possible.
    // At the moment can't ever happen inside the loop analyser.
    PeelAttempt* LPA = 0;
    if(!inLoopAnalyser) {
      if((LPA = getOrCreatePeelAttempt(BBL)))
	LPA->analyse();
    }

    // Analyse for invariants if we didn't establish that the loop terminates.
    if((!LPA) || !LPA->isTerminated()) {

      anyChange |= analyseLoop(BBL);

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

  // Else we should just analyse this block here.
  anyChange |= analyseBlockInstructions(BB, false, inLoopAnalyser);

  return anyChange;

}

// Returns true if there was any change
bool IntegrationAttempt::analyseBlockInstructions(ShadowBB* BB, bool skipSuccessorCreation, bool inLoopAnalyser) {

  const Loop* MyL = L;

  bool anyChange = false;

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* SI = &(BB->insts[i]);
    ShadowInstructionInvar* SII = SI->invar;
    Instruction* I = SII->I;

    if(inst_is<TerminatorInst>(SI)) {
      // Call tryEvalTerminator regardless of scope.
      anyChange |= tryEvaluateTerminator(SI, skipSuccessorCreation);
      continue;
    }

    // Could the instruction have out-of-loop dependencies?
    if((!inLoopAnalyser) && SII->naturalScope != MyL)
      continue;
    
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
	  anyChange |= IA->analyseWithArgs(inLoopAnalyser);
	  doCallStoreMerge(SI);
	}
	else
	  executeUnexpandedCall(SI);
      }

      // Fall through to try to get the call's return value

    }

    anyChange |= tryEvaluate(ShadowValue(SI), inLoopAnalyser);

  }

  return anyChange;

}

bool IntegrationAttempt::analyseLoop(const Loop* L) {

  ShadowLoopInvar* LInfo = invarInfo->LInfo[L];
  bool anyChange = true;
  bool firstIter = true;
  bool everChanged = false;

  ShadowBB* PHBB = getBB(LInfo->preheaderIdx);
  ShadowBB* HBB = getBB(LInfo->headerIdx);
  ShadowBB* LBB = getBB(LInfo->latchIdx);

  while(anyChange) {

    // Give the preheader store an extra reference to ensure it is never modified.
    // This ref will be consumed in the merge below.
    PHBB->localStore->refCount++;
    
    {
      MergeBlockVisitor V(false);

      if(!firstIter) {

	// Drop store references at exit edges: we're going around again.
	for(std::vector<std::pair<uint32_t, uint32_t> >::iterator it = LInfo->exitEdges.begin(),
	      itend = LInfo->exitEdges.end(); it != itend; ++it) {

	  ShadowBB* BB = getBB(it->first);
	  if(BB && !edgeIsDead(BB->invar, getBBInvar(it->second)))
	    BB->localStore->dropReference();

	}

	// Merge the latch store with the preheader store:
	V.visit(getBB(LInfo->latchIdx), 0, false);
	V.visit(PHBB, 0, false);

      }
      else {

	firstIter = false;
      
	// Give the header block the store from the preheader
	V.visit(PHBB, 0, false);

      }

      HBB->localStore = V.newMap;

    }

    anyChange = false;

    for(uint32_t i = LInfo->headerIdx; i < (BBsOffset + nBBs); ++i) {

      if(!L->contains(getBBInvar(i)->naturalScope))
	break;

      anyChange |= analyseBlock(i, true, i == LInfo->headerIdx, L);

    }

    everChanged |= anyChange;

  }

  // Release the preheader store that was held for merging in each iteration:
  PHBB->localStore->dropReference();

  // Release the latch store that the header will not use again:
  LBB->localStore->dropReference();
  
  return everChanged;

}

