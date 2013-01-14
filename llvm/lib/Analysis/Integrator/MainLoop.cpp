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

void InlineAttempt::analyseWithArgs() {

  for(Function::arg_iterator it = F.arg_begin(), it2 = F.arg_end(); it != it2; ++it) {
    tryEvaluate(it);
    if(!improvedValues.count(it)) {
      updateBasePointer(it, true);
      tryPromoteSingleValuedPB(it);
    }
  }
  analyse();

}

void IntegrationAttempt::analyse() {

  std::vector<BasicBlock*> topOrderedBlocks;
  SmallSet<BasicBlock*, 8> visited;

  createTopOrderingFrom(getEntryBlock(), topOrderedBlocks, visited, getLoopContext(), true);

  for(std::vector<BasicBlock*>::reverse_iterator it = topOrderedBlocks.rbegin(), it2 = topOrderedBlocks.rend(); it != it2; ++it) {

    analyseBlock(*it);

  }

}

void PeelAttempt::analyse() {
  
  for(PeelIteration* PI = Iterations[0]; PI; PI = PI->getOrCreateNextIteration()) {

    PI->analyse();

  }

  Iterations.back()->checkFinalIteration();

}

void IntegrationAttempt::analyseBlock(BasicBlock* BB) {

  const Loop* MyL = getLoopContext();

  checkBlock(BB);
  if(blockIsDead(BB))
    return;

  // Use getLoopFor instead of getBlockScopeVariant because even if the loop is explicitly
  // ignored we want to notice that it exists so we can call analyseLoopPBs.
  const Loop* BBL = LI[&F]->getLoopFor(BB);
    
  if(BBL != MyL) {

    // By construction of our top-ordering, must be a loop entry block.
   
    // First, examine each block in the loop to discover invariants, including invariant dead blocks.
    std::vector<BasicBlock*> topOrderedBlocks;
    SmallSet<BasicBlock*, 8> visited;

    createTopOrderingFrom(BBL->getHeader(), topOrderedBlocks, visited, BBL, false);

    for(std::vector<BasicBlock*>::reverse_iterator it = topOrderedBlocks.rbegin(), it2 = topOrderedBlocks.rend(); it != it2; ++it) {

      checkBlock(*it);
      if(!blockIsDead(*it))
	analyseBlockInstructions(*it);

    }

    // Now explore the loop, if possible.
    PeelAttempt* LPA = getOrCreatePeelAttempt(BBL);
    if(LPA)
      LPA->analyse();

    // Analyse for invariants if we didn't establish that the loop terminates.
    if((!LPA) || (LPA->Iterations.back()->iterStatus != IterationStatusFinal)) {
      analyseLoopPBs(BBL);
    }

  }
  else {

    // Else we should just analyse this block here.
    analyseBlockInstructions(BB);

  }

}

void IntegrationAttempt::analyseBlockInstructions(BasicBlock* BB) {

  const Loop* MyL = getLoopContext();

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

    if(BranchInst* BrI = dyn_cast<BranchInst>(BI)) {
      if(!BrI->isConditional())
	break;
    }

    if(getValueScope(BI) != MyL)
      continue;
    
    if(CallInst* CI = dyn_cast<CallInst>(BI)) {

      if(tryPromoteOpenCall(CI))
	continue;
      if(tryResolveVFSCall(CI))
	continue;
      if(InlineAttempt* IA = getOrCreateInlineAttempt(CI))
	IA->analyseWithArgs();

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
      updateBasePointer(BI, true);
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
