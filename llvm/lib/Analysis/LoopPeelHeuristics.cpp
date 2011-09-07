//===- LoopPeelHeuristics.cpp - Find loops that we might want to try peeling --------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass uses some heuristics to figure out loops that might be worth peeling.
// Right now it's focussed on finding loops that access arrays with defined contents
// for use with the SimpleVFSEval pass.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "looppeelheuristics"
#include "llvm/Pass.h"
#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include <deque>
#include <string>
#include <algorithm>

#include <stdio.h>
#include <errno.h>
#include <string.h>

using namespace llvm;

namespace {
  
  class LoopPeelHeuristicsPass : public LoopPass {

    int loopBenefit;

  public:

    static char ID;

    explicit LoopPeelHeuristicsPass() : LoopPass(ID) { }
    bool runOnLoop(Loop *L, LPPassManager&);
    void print(raw_ostream &OS, const Module*) const;
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {

      AU.setPreservesAll();

    }

  };

  char LoopPeelHeuristicsPass::ID = 0;

}

LoopPass *llvm::createLoopPeelHeuristicsPass() {
  return new LoopPeelHeuristicsPass();
}

INITIALIZE_PASS(LoopPeelHeuristicsPass, "peelheuristics", "Score loops for peeling benefit", false, false);

int getRemoveBlockPredBenefit(Loop* L, BasicBlock* BB, BasicBlock* BBPred, DenseMap<Instruction*, Constant*>& constInstructions,
			      DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& blockPreds);

int getConstantBenefit(Loop* L, Instruction* I, DenseMap<Instruction*, Constant*>& constInstructions, 
		       DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& blockPreds);

// This whole thing is basically a constant propagation simulation -- rather than modifying the code in place like the real constant prop,
// we maintain shadow structures indicating which instructions have been folded and which basic blocks eliminated.
// It might turn out to be a better idea to find out whether peeling is useful by just doing it and optimising! I'll see...

int getRemoveBlockPredBenefit(Loop* L, BasicBlock* BB, BasicBlock* BBPred, DenseMap<Instruction*, Constant*>& constInstructions,
			      DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& blockPreds) {

  int benefit = 0;

  if(!L->contains(BB))
    return 0;

  SmallSet<BasicBlock*, 4>& thisBlockPreds = blockPreds[BB];

  thisBlockPreds.erase(BBPred);
  if(thisBlockPreds.size() == 0) {
    // This BB is dead! Remove it as a predecessor to all successor blocks and see if that helps anything.
    for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      benefit += getRemoveBlockPredBenefit(L, *SI, BB, constInstructions, blockPreds);
      return benefit;
    }
  }
  else {
    // See if any of our PHI nodes are now effectively constant
    for(BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E && isa<PHINode>(*I); ++I) {
      PHINode* PN = cast<PHINode>(I);
      DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(PN);
      if(it != constInstructions.end()) // If this PHI node has already been rendered constant.
	continue;
      Constant* constValue = 0;
      for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; PI++) {
	Value* predValue = PN->getIncomingValueForBlock(*PI);
	if(predValue && !constValue) {
	  Constant* C;
	  if((C = dyn_cast<Constant>(predValue)))
	    constValue = C;
	  else
	    break;
	}
	else if((!predValue) || predValue != constValue) {
	  constValue = 0;
	  break;
	}
	// else this predecessor matches the others.
      }
      if(constValue) {
	constInstructions[PN] = constValue;
	benefit += getConstantBenefit(L, PN, constInstructions, blockPreds);
      }
    }
  }

  return benefit;

}

int getConstantBenefit(Loop* L, Instruction* ArgI, DenseMap<Instruction*, Constant*>& constInstructions, 
		       DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& blockPreds) {

  int benefit = 0;

  if(!L->contains(ArgI)) // Instructions outside the loop are neither here nor there if we're unrolling the loop.
    return 0;
  
  Constant* instVal = constInstructions[ArgI];
  // A null value means we know the result will be constant, but we're not sure what.

  for (Value::use_iterator UI = ArgI->use_begin(), E = ArgI->use_end(); UI != E;++UI){

    Instruction* I;
    if(!(I = dyn_cast<Instruction>(*UI)))
      continue;

    DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(I);
    if(it != constInstructions.end()) // Have we already rendered this instruction constant?
      continue;

    // These bonuses apply whether or not we manage to render all the instruction's arguments constant:

    if (CallInst *CI = dyn_cast<CallInst>(I)) {
      // Turning an indirect call into a direct call is a BIG win
      if (CI->getCalledValue() == ArgI)
	benefit += 500;
    } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
      // Turning an indirect call into a direct call is a BIG win
      if (II->getCalledValue() == ArgI)
	benefit += 500;
    }
    
    if (isa<BranchInst>(I) || isa<SwitchInst>(I)) {
      // Both Branches and Switches have one potentially non-const arg which we now know is constant.
      // The mechanism used by InlineCosts.cpp here emphasises code size. I try to look for
      // time instead, by searching for PHIs that will be made constant.
      if(instVal) {
	BasicBlock* target;
	if(BranchInst* BI = dyn_cast<BranchInst>(I)) {
	  // This ought to be a boolean.
	  if((cast<ConstantInt>(instVal))->isZero())
	    target = BI->getSuccessor(0);
	  else
	    target = BI->getSuccessor(1);
	}
	else {
	  SwitchInst* SI = cast<SwitchInst>(I);
	  unsigned targetidx = SI->findCaseValue(cast<ConstantInt>(instVal));
	  target = SI->getSuccessor(targetidx);
	}
	if(target) {
	  // We know where the instruction is going -- remove this block as a predecessor for its other targets.
	  TerminatorInst* TI = cast<TerminatorInst>(I);
	  const unsigned NumSucc = TI->getNumSuccessors();
	  for (unsigned I = 0; I != NumSucc; ++I) {
	    BasicBlock* otherTarget = TI->getSuccessor(I);
	    benefit += getRemoveBlockPredBenefit(L, otherTarget, TI->getParent(), constInstructions, blockPreds);
	  }
	}
	else {
	  // We couldn't be sure which block the branch will go to, but its target will be constant.
	  // Give a static bonus to indicate that more advanced analysis might be able to eliminate the branch.
	  benefit += 50;
	}

      }
      else {
	// We couldn't be sure where the branch will go because we only know the operand is constant, not its value.
	// We usually don't know because this is the return value of a call, or the result of a load. Give a small bonus
	// as the call might be inlined or similar.
	benefit += 10;
      }
    }
    else {
      // An ordinary instruction. Give bonuses or penalties for particularly fruitful or difficult instructions,
      // then count the benefits of that instruction becoming constant.
      if (isa<CallInst>(I) || isa<InvokeInst>(I))
	  benefit += 50;

      // Try to calculate a constant value resulting from this instruction. Only possible if
      // this instruction is simple (e.g. arithmetic) and its arguments have known values, or don't matter.

      SmallVector<Constant*, 4> instOperands;

      // This isn't as good as it could be, because the constant-folding library wants an array of constants,
      // whereas we might have somethig like 1 && x, which could fold but x is not a Constant*. Could work around this,
      // don't at the moment.
      for(unsigned i = 0; i < I->getNumOperands(); i++) {
	Value* op = I->getOperand(i);
	Constant* C;
	Instruction* OperandI;
	if((C = dyn_cast<Constant>(op)))
	  instOperands.push_back(C);
	else if((OperandI = dyn_cast<Instruction>(op))) {
	  DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(OperandI);
	  if(it != constInstructions.end())
	    instOperands.push_back(it->second);
	  else {
	    break;
	  }
	}
	else {
	  DEBUG(dbgs() << (*ArgI) << " has a non-instruction, non-constant user: " << (*op) << std::endl);
	  break;
	}
      }

      if(instOperands.size() == I->getNumOperands()) {
	Constant* newConst = ConstantFoldInstOperands(I->getOpcode(), I->getType(), instOperands.data(), I->getNumOperands(), 0);
	// InlineCosts.cpp doesn't count side-effecting instructions or memory reads here.
	// I count memory reads because having made their operand constant there's at least a
	// chance we'll be able to store-to-load forward them out of existence.

	// The following comment from InlineCosts.cpp, which I don't quite understand yet:
	// FIXME: It would be nice to capture the fact that a load from a
	// pointer-to-constant-global is actually a *really* good thing to zap.
	// Unfortunately, we don't know the pointer that may get propagated here,
	// so we can't make this decision.
	if (!(I->mayHaveSideEffects() || isa<AllocaInst>(I))) // A particular side-effect
	  benefit++; // Elimination of this instruction.
	constInstructions[I] = newConst;
	benefit += getConstantBenefit(L, I, constInstructions, blockPreds);
      }

    }
  }

  return benefit;

}

bool LoopPeelHeuristicsPass::runOnLoop(Loop* L, LPPassManager& LPM) {
  
  BasicBlock* loopHeader = L->getHeader();
  BasicBlock* loopPreheader = L->getLoopPreheader();
  if((!loopHeader) || (!loopPreheader)) {
    DEBUG(dbgs() << "Can't evaluate loop " << L << " because it doesn't have a header or preheader" << std::endl);
    return false;
  }
  DenseMap<Instruction*, Constant*> constInstructions;

  for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {
    PHINode* PI = cast<PHINode>(I);
    Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
    if(preheaderVal) {
      if(Constant* C = dyn_cast<Constant>(preheaderVal)) {
	constInstructions[PI] = C;
      }
    }
  }

  if(constInstructions.size() == 0)
    return false;

  // Proceed to push the frontier of instructions with all-constant operands! Count a score as we go,
  // using some bonuses suggested from code in InlineCost.cpp attempting a similar game.

  DenseMap<Instruction*, int> nonConstOperands;
  DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> > blockPreds;

  std::vector<BasicBlock*> loopBlocks = L->getBlocks();

  for(std::vector<BasicBlock*>::iterator I = loopBlocks.begin(), E = loopBlocks.end(); I != E; ++I) {

    BasicBlock* block = *I;

    for(pred_iterator PI = pred_begin(block), E = pred_end(block); PI != E; ++PI) {
      blockPreds[block].insert(*PI);
    }

  }

  loopBenefit = 0;

  for(DenseMap<Instruction*, Constant*>::iterator I = constInstructions.begin(), E = constInstructions.end(); I != E; ++I) {

    loopBenefit += getConstantBenefit(L, I->first, constInstructions, blockPreds);

  }

  return false;

}

void LoopPeelHeuristicsPass::print(raw_ostream &OS, const Module*) const {

  OS << "Score: " << loopBenefit << "\n";

}
