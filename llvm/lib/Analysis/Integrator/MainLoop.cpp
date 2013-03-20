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

static cl::opt<bool> NoInnerLoopSolver("int-no-inner-loop-solver");

void InlineAttempt::analyseWithArgs(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA) {

  for(unsigned i = 0; i < F.arg_size(); ++i) {

    ShadowArg* SArg = &(argShadows[i]);
    tryEvaluate(ShadowValue(SArg), true, 0, CacheThresholdBB, CacheThresholdIA);

  }
  analyse(withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA);

}

void IntegrationAttempt::analyse(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA) {

  createEntryBlock();

  for(uint32_t i = BBsOffset; i < (BBsOffset + nBBs); ++i) {

    // analyseBlock can increment i past loops
    analyseBlock(i, withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA);

  }

}

void IntegrationAttempt::analyse() {

  // Analysis primary entry point:
  BasicBlock* FirstThresholdBB = &F.getEntryBlock();
  IntegrationAttempt* FirstThresholdIA = this;

  analyse(false, FirstThresholdBB, FirstThresholdIA);

}

void PeelAttempt::analyse(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA) {
  
  for(PeelIteration* PI = Iterations[0]; PI; PI = PI->getOrCreateNextIteration()) {

    PI->analyse(withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA);

  }

  Iterations.back()->checkFinalIteration();

}

void IntegrationAttempt::analyseBlock(uint32_t& blockIdx, bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA) {

  ShadowBB* BB = getBB(blockIdx);
  if(!BB)
    return;

  // Use natural scope rather than scope because even if a loop is
  // ignored we want to notice that it exists so we can call analyseLoopPBs.
  ShadowBBInvar* BBI = BB->invar;
  const Loop* BBL = BBI->naturalScope;
   
  if(BBL != L) {

    // By construction of our top-ordering, must be a loop entry block.
    release_assert(BBL && "Walked into root context?");

    // Loop invariants used to be found here, but are now explored on demand whenever a block
    // gets created that doesn't yet exist in parent scope.

    // Calculate invariants for the header block, which uniquely is created in its invariant scope
    // before being created in any child loops.

    analyseBlockInstructions(BB, true, CacheThresholdBB, CacheThresholdIA, true);
   
    BasicBlock* LThresholdBB = CacheThresholdBB;
    IntegrationAttempt* LThresholdIA = CacheThresholdIA;
    
    // Now explore the loop, if possible.
    PeelAttempt* LPA = getOrCreatePeelAttempt(BBL);
    if(LPA) {
      LPA->analyse(withinUnboundedLoop, LThresholdBB, LThresholdIA);
    }

    // Analyse for invariants if we didn't establish that the loop terminates.
    if((!LPA) || !LPA->isTerminated()) {
      for(uint32_t i = blockIdx; i < (nBBs + BBsOffset) && BBL->contains(getBBInvar(i)->naturalScope); ++i) {
	if(ShadowBB* InvarBB = getBB(i))
	  analyseBlockInstructions(InvarBB, true, CacheThresholdBB, CacheThresholdIA, false);
      }

      // If the non-creation was because this loop is ignored, create child contexts:
      /*
      if((!LPA) && (pass->shouldIgnoreLoop(&F, BBL->getHeader()) || 
      pass->shouldExpandLoopCalls(&F, BBL->getHeader()))) {*/
      // For now create invariant functions whenever a peel attempt is not available.
      if((!LPA) || !LPA->isTerminated()) {

	for(uint32_t i = blockIdx; i < (nBBs + BBsOffset) && BBL->contains(getBBInvar(i)->naturalScope); ++i) {

	  if(ShadowBB* InvarBB = getBB(i)) {

	    for(uint32_t j = 0; j < InvarBB->insts.size(); ++j) {

	      ShadowInstruction* SI = &(InvarBB->insts[j]);
	      if(inst_is<CallInst>(SI)) {

		if(InlineAttempt* IA = getOrCreateInlineAttempt(SI, true, true))
		  IA->analyseWithArgs(true, CacheThresholdBB, CacheThresholdIA);

	      }

	    }

	  }

	}

      }

      // Finally, analyse everything in loop context together:
      if((!withinUnboundedLoop) || (!NoInnerLoopSolver))
	analyseLoopPBs(BBL, CacheThresholdBB, CacheThresholdIA);

    }
    else {
      // Copy edges found always dead to local scope, to accelerate edgeIsDead queries without
      // checking every iteration every time.
      copyLoopExitingDeadEdges(LPA);
      // Loop terminated, permit a within-loop-threshold (block certainty constraint implies
      // there is no path around the loop).
      CacheThresholdBB = LThresholdBB;
      CacheThresholdIA = LThresholdIA;
      LPDEBUG("Accept loop threshold adv -> " << CacheThresholdBB->getName() << "\n");
    }

    // Advance the main loop past this loop. Loop blocks are always contiguous in the topo ordering.
    while(blockIdx < invarInfo->BBs.size() && BBL->contains(getBBInvar(blockIdx)->naturalScope))
      ++blockIdx;
    --blockIdx;

  }
  else {

    if((!withinUnboundedLoop) && BB->status == BBSTATUS_CERTAIN) {

      LPDEBUG("Advance threshold to " << BB->getName() << "\n");
      CacheThresholdBB = BB->invar->BB;
      CacheThresholdIA = this;

    }
    
    // Else we should just analyse this block here.
    analyseBlockInstructions(BB, withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA, false);

  }

}

void IntegrationAttempt::analyseBlockInstructions(ShadowBB* BB, bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA, bool skipSuccessorCreation) {

  const Loop* MyL = L;

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* SI = &(BB->insts[i]);
    ShadowInstructionInvar* SII = SI->invar;
    Instruction* I = SII->I;

    if(inst_is<TerminatorInst>(SI)) {
      // Call tryEvalTerminator regardless of scope.
      tryEvaluateTerminator(SI, skipSuccessorCreation);
      continue;
    }

    // Could the instruction have out-of-loop dependencies?
    if(SII->naturalScope != MyL)
      continue;
    
    if(isa<CallInst>(I)) {

      if(tryPromoteOpenCall(SI))
	continue;
      if(tryResolveVFSCall(SI))
	continue;
      if(InlineAttempt* IA = getOrCreateInlineAttempt(SI, false, withinUnboundedLoop))
	IA->analyseWithArgs(withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA);

      // Fall through to try to get the call's return value

    }

    tryEvaluate(ShadowValue(SI), true, 0, CacheThresholdBB, CacheThresholdIA);

  }

}


