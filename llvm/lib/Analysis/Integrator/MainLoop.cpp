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

using namespace llvm;

void InlineAttempt::analyseWithArgs(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA) {

  for(unsigned i = 0; i < F.arg_size(); ++i) {

    ShadowArg* SArg = argShadows[i];
    tryEvaluateArg(SArg);
    if(isUnresolved(SArg)) {
      updateBasePointer(SArg, true, 0, CacheThresholdBB, CacheThresholdIA);
      tryPromoteSingleValuedPB(SArg);
    }

  }
  analyse(withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA);

}

void IntegrationAttempt::analyse(bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA) {

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

  checkBlock(blockIdx);
  // Was block killed?

  ShadowBB* BB = getBB(blockIdx);
  if(!BB)
    return;

  // Use natural scope rather than scope because even if a loop is
  // ignored we want to notice that it exists so we can call analyseLoopPBs.
  const Loop* BBL = BB->invar->naturalScope;
  const Loop* MyL = L;
    
  if(BBL != MyL) {

    // By construction of our top-ordering, must be a loop entry block.
    release_assert(BBL && "Walked into root context?");

    // This works because loop blocks are all topologically before any loop exit blocks, because by 
    // definition of a loop block there's a path back to the header and then to the exit block.
    // Therefore we can scan blockIdx forwards until we leave the loop BBL.
   
    // First, examine each block in the loop to discover invariants, including invariant dead blocks.
    for(uint32_t i = blockIdx; i < invarInfo->BBs.size() && BBL->contains(invarInfo->BBs[i]->naturalScope; ++i)) {
      
      // Thresholds should not be modified due to withinUnboundedLoop = true,
      // but just to be safe...
      
      BasicBlock* InvarCTBB = CacheThresholdBB;
      IntegrationAttempt* InvarCTIA = CacheThresholdIA;
      
      checkBlock(i);
      if(ShadowBB* LoopBB = getBB(i))
	analyseBlockInstructions(LoopBB, true, InvarCTBB, InvarCTIA);
      
    }

    BasicBlock* LThresholdBB = CacheThresholdBB;
    IntegrationAttempt* LThresholdIA = CacheThresholdIA;
    
    // Now explore the loop, if possible.
    PeelAttempt* LPA = getOrCreatePeelAttempt(BBL);
    if(LPA) {
      LPA->analyse(withinUnboundedLoop, LThresholdBB, LThresholdIA);
    }

    // Analyse for invariants if we didn't establish that the loop terminates.
    if((!LPA) || (LPA->Iterations.back()->iterStatus != IterationStatusFinal)) {
      analyseLoopPBs(BBL, CacheThresholdBB, CacheThresholdIA);
    }
    else {
      // Loop terminated, permit a within-loop-threshold (block certainty constraint implies
      // there is no path around the loop).
      CacheThresholdBB = LThresholdBB;
      CacheThresholdIA = LThresholdIA;
      LPDEBUG("Accept loop threshold adv -> " << CacheThresholdBB->getName() << "\n");
    }

    // Advance the main loop past this loop.
    blockIdx = i;

  }
  else {

    if((!withinUnboundedLoop) && BB->status == BBSTATUS_CERTAIN) {

      LPDEBUG("Advance threshold to " << BB->getName() << "\n");
      CacheThresholdBB = BB;
      CacheThresholdIA = this;

    }
    
    // Else we should just analyse this block here.
    analyseBlockInstructions(BB, withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA);

  }

}

void IntegrationAttempt::analyseBlockInstructions(ShadowBB* BB, bool withinUnboundedLoop, BasicBlock*& CacheThresholdBB, IntegrationAttempt*& CacheThresholdIA) {

  const Loop* MyL = L;

  for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* SI = BB->insts[i];
    ShadowInstructionInvar* SII = SI->invar;
    Instruction* I = SII->I;

    if(BranchInst* BrI = dyn_cast<BranchInst>(I)) {
      if(!BrI->isConditional())
	break;
    }

    if(SII->scope != MyL)
      continue;
    
    if(CallInst* CI = dyn_cast<CallInst>(BI)) {

      if(tryPromoteOpenCall(SI))
	continue;
      if(tryResolveVFSCall(SI))
	continue;
      if(InlineAttempt* IA = getOrCreateInlineAttempt(SI))
	IA->analyseWithArgs(withinUnboundedLoop, CacheThresholdBB, CacheThresholdIA);

      // Fall through to try to get the call's return value

    }

    tryEvaluate(BI);

    if(LoadInst* LI = dyn_cast<LoadInst>(BI)) {
      if(isUnresolved(LI))
	checkLoad(LI);
    }

    // Don't use isUnresolved here because the PB solver requires that we *do*
    // evaluate GEPs and casts with a known base. This will go away when its single-value
    // mode is merged with the ordinary constant folder.
    if(!improvedValues.count(BI)) {
      // This works for either LF or ordinary const prop:
      updateBasePointer(BI, true, 0, CacheThresholdBB, CacheThresholdIA);
      tryPromoteSingleValuedPB(BI);
    }

  }

}

void IntegrationAttempt::createTopOrderingFrom(BasicBlock* BB, std::vector<BasicBlock*>& Result, SmallSet<BasicBlock*, 8>& Visited, const Loop* MyL, bool enterLoops) {

  if(!Visited.insert(BB))
    return;

  const Loop* BBL = LI[&F]->getLoopFor(BB);
  
  // Drifted out of scope?
  if(MyL != BBL && ((!BBL) || (BBL->contains(MyL))))
    return;

  if(enterLoops && (MyL != BBL)) {

    // Child loop. Use the loop successors rather than the block successors.
    SmallVector<BasicBlock*, 4> ExitBlocks;
    BBL->getExitBlocks(ExitBlocks);
    for(SmallVector<BasicBlock*, 4>::iterator it = ExitBlocks.begin(), it2 = ExitBlocks.end(); it != it2; ++it) {
      
      createTopOrderingFrom(*it, Result, Visited, MyL, enterLoops);
      
    }

  }
  else {

    for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {

      createTopOrderingFrom(*SI, Result, Visited, MyL, enterLoops);

    }

  }

  Result.push_back(BB);

}
