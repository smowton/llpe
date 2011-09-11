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
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ProfileInfo.h"
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
    std::string loopHeaderName;

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

int getConstantBenefit(Loop* L, Instruction* I, Constant* C, DenseMap<Instruction*, Constant*>& constInstructions, 
		       DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& blockPreds);

int getPHINodeBenefit(Loop* L, PHINode* PN, DenseMap<Instruction*, Constant*>& constInstructions, DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >&blockPreds);

// This whole thing is basically a constant propagation simulation -- rather than modifying the code in place like the real constant prop,
// we maintain shadow structures indicating which instructions have been folded and which basic blocks eliminated.
// It might turn out to be a better idea to find out whether peeling is useful by just doing it and optimising! I'll see...

int getRemoveBlockPredBenefit(Loop* L, BasicBlock* BB, BasicBlock* BBPred, DenseMap<Instruction*, Constant*>& constInstructions,
			      DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& blockPreds) {

  int benefit = 0;
  
  DEBUG(dbgs() << "--> Getting benefit due elimination of predecessor " << BBPred->getName() << " from BB " << BB->getName() << "\n");

  if(!L->contains(BB)) {
    DEBUG(dbgs() << "<-- Returning constant bonus because " << BB->getName() << " not in loop" << "\n");
    return 1;
  }

  if(BBPred == L->getLoopLatch()) {
    DEBUG(dbgs() << "<-- Eliminated the latch branch! Returning large bonus");
    return 1000;
  }

  SmallSet<BasicBlock*, 4>& thisBlockPreds = blockPreds[BB];

  thisBlockPreds.erase(BBPred);
  if(thisBlockPreds.size() == 0) {
    // This BB is dead! Remove it as a predecessor to all successor blocks and see if that helps anything.
    DEBUG(dbgs() << "Block is dead! Eliminating edges from successors..." << "\n");
    for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI)
      benefit += getRemoveBlockPredBenefit(L, *SI, BB, constInstructions, blockPreds);
  }
  else {
    // See if any of our PHI nodes are now effectively constant
    for(BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E && isa<PHINode>(*I); ++I) {
      PHINode* PN = cast<PHINode>(I);
      benefit += getPHINodeBenefit(L, PN, constInstructions, blockPreds);
    }
  }

  DEBUG(dbgs() << "<-- Total benefit due to " << BBPred->getName() << " -/-> " << BB->getName() << ": " << benefit << "\n");

  return benefit;

}

int getPHINodeBenefit(Loop* L, PHINode* PN, DenseMap<Instruction*, Constant*>& constInstructions, DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >&blockPreds) {

  DEBUG(dbgs() << "Checking if PHI " << *PN << " is now constant" << "\n");

  BasicBlock* BB = PN->getParent();
  SmallSet<BasicBlock*, 4>& thisBlockPreds = blockPreds[BB];
  Constant* constValue = 0;

  if(BB == L->getHeader()) {
    DEBUG(dbgs() << "Ignoring because in the loop header\n");
    return 0;
  }

  for(SmallSet<BasicBlock*, 4>::iterator PI = thisBlockPreds.begin(), PE = thisBlockPreds.end(); PI != PE; PI++) {
    Value* predValue = PN->getIncomingValueForBlock(*PI);
    Constant* predConst = dyn_cast<Constant>(predValue);
    Instruction* predInst;
    if(!predConst) {
      if((predInst = dyn_cast<Instruction>(predValue))) {
	DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(predInst);
	if(it != constInstructions.end())
	  predConst = it->second;
      }
    }
    if(!predConst) {
      constValue = 0;
      break;
    }
    if(!constValue)
      constValue = predConst;
    else if(predConst != constValue) {
      constValue = 0;
      break;
    }
    // else this predecessor matches the others.
  }
  if(constValue) {
    DEBUG(dbgs() << "Constant at " << *constValue << "\n");
    return getConstantBenefit(L, PN, constValue, constInstructions, blockPreds);
  }
  else {
    DEBUG(dbgs() << "Not constant\n");
    return 0;
  }

}

int getConstantBenefit(Loop* L, Instruction* ArgI, Constant* ArgC, DenseMap<Instruction*, Constant*>& constInstructions, 
		       DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& blockPreds) {

  int benefit = 0;

  if(!L->contains(ArgI)) { // Instructions outside the loop are neither here nor there if we're unrolling the loop.
    DEBUG(dbgs() << *ArgI << " not in loop, no benefit\n");
    return 0;
  }

  DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(ArgI);
  if(it != constInstructions.end()) { // Have we already rendered this instruction constant?
    DEBUG(dbgs() << *ArgI << " already constant, no additional benefit\n");
    return 0;
  }
  else
    constInstructions[ArgI] = ArgC;

  // A null value means we know the result will be constant, but we're not sure what.

  if(ArgC)
    DEBUG(dbgs() << "--> Getting benefit due to instruction " << *ArgI << " having constant value " << *ArgC << "\n");
  else
    DEBUG(dbgs() << "--> Getting benefit due to instruction " << *ArgI << " having an unknown constant value" << "\n");

  for (Value::use_iterator UI = ArgI->use_begin(), E = ArgI->use_end(); UI != E;++UI){

    Instruction* I;
    if(!(I = dyn_cast<Instruction>(*UI))) {
      DEBUG(dbgs() << "Instruction has a non-instruction user: " << *UI << "\n");
      continue;
    }

    DEBUG(dbgs() << "Considering user instruction " << *I << "\n");

    // These bonuses apply whether or not we manage to render all the instruction's arguments constant:

    if (CallInst *CI = dyn_cast<CallInst>(I)) {
      // Turning an indirect call into a direct call is a BIG win
      if (CI->getCalledValue() == ArgI) {
	DEBUG(dbgs() << "Awarded indirect->direct call bonus" << "\n");
	benefit += 500;
      }
    } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
      // Turning an indirect call into a direct call is a BIG win
      if (II->getCalledValue() == ArgI) {
	DEBUG(dbgs() << "Awarded indirect->direct call bonus" << "\n");
	benefit += 500;
      }
    }
    
    if (isa<BranchInst>(I) || isa<SwitchInst>(I)) {
      // Both Branches and Switches have one potentially non-const arg which we now know is constant.
      // The mechanism used by InlineCosts.cpp here emphasises code size. I try to look for
      // time instead, by searching for PHIs that will be made constant.
      if(ArgC) {
	BasicBlock* target;
	if(BranchInst* BI = dyn_cast<BranchInst>(I)) {
	  // This ought to be a boolean.
	  if((cast<ConstantInt>(ArgC))->isZero())
	    target = BI->getSuccessor(1);
	  else
	    target = BI->getSuccessor(0);
	}
	else {
	  SwitchInst* SI = cast<SwitchInst>(I);
	  unsigned targetidx = SI->findCaseValue(cast<ConstantInt>(ArgC));
	  target = SI->getSuccessor(targetidx);
	}
	if(target) {
	  // We know where the instruction is going -- remove this block as a predecessor for its other targets.
	  DEBUG(dbgs() << "Branch or switch instruction given known target: " << target->getName() << "\n");
	  TerminatorInst* TI = cast<TerminatorInst>(I);
	  const unsigned NumSucc = TI->getNumSuccessors();
	  for (unsigned I = 0; I != NumSucc; ++I) {
	    BasicBlock* otherTarget = TI->getSuccessor(I);
	    if(otherTarget != target)
	      benefit += getRemoveBlockPredBenefit(L, otherTarget, TI->getParent(), constInstructions, blockPreds);
	  }
	}
	else {
	  // We couldn't be sure which block the branch will go to, but its target will be constant.
	  // Give a static bonus to indicate that more advanced analysis might be able to eliminate the branch.
	  DEBUG(dbgs() << "Awarded unconditional branch to unknown target bonus" << "\n");
	  benefit += 50;
	}

      }
      else {
	// We couldn't be sure where the branch will go because we only know the operand is constant, not its value.
	// We usually don't know because this is the return value of a call, or the result of a load. Give a small bonus
	// as the call might be inlined or similar.
	DEBUG(dbgs() << "Awarded unknown constant in branch or switch bonus" << "\n");
	benefit += 10;
      }
    }
    else {
      // An ordinary instruction. Give bonuses or penalties for particularly fruitful or difficult instructions,
      // then count the benefits of that instruction becoming constant.
      if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
	DEBUG(dbgs() << "Awarded constant call arguments bonus" << "\n");
	benefit += 50;
      }

      // Try to calculate a constant value resulting from this instruction. Only possible if
      // this instruction is simple (e.g. arithmetic) and its arguments have known values, or don't matter.

      PHINode* PN;
      if((PN = dyn_cast<PHINode>(I))) {
	// PHI nodes are special because of their BB arguments, and the special-case "constant folding" that affects them
	benefit += getPHINodeBenefit(L, PN, constInstructions, blockPreds);
      }
      else {

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
	      DEBUG(dbgs() << "Not constant folding yet due to non-constant argument " << *OperandI << "\n");
	      break;
	    }
	  }
	  else {
	    DEBUG(dbgs() << (*ArgI) << " has a non-instruction, non-constant argument: " << (*op) << "\n");
	    break;
	  }
	}

	if(instOperands.size() == I->getNumOperands()) {
	  Constant* newConst;
	  if (const CmpInst *CI = dyn_cast<CmpInst>(I))
	    newConst = ConstantFoldCompareInstOperands(CI->getPredicate(), instOperands[0], instOperands[1], 0);
	  else
	    newConst = ConstantFoldInstOperands(I->getOpcode(), I->getType(), instOperands.data(), I->getNumOperands(), 0);
	  // InlineCosts.cpp doesn't count side-effecting instructions or memory reads here.
	  // I count memory reads because having made their operand constant there's at least a
	  // chance we'll be able to store-to-load forward them out of existence.

	  // The following comment from InlineCosts.cpp, which I don't quite understand yet:
	  // FIXME: It would be nice to capture the fact that a load from a
	  // pointer-to-constant-global is actually a *really* good thing to zap.
	  // Unfortunately, we don't know the pointer that may get propagated here,
	  // so we can't make this decision.
	  if(newConst)
	    DEBUG(dbgs() << "User " << *I << " now constant at " << *newConst << "\n");
	  else
	    DEBUG(dbgs() << "User " << *I << " has all-constant arguments, but couldn't be constant folded" << "\n");
	  if (!(I->mayHaveSideEffects() || isa<AllocaInst>(I))) // A particular side-effect
	    benefit++; // Elimination of this instruction.
	  else
	    DEBUG(dbgs() << "Not eliminating instruction due to side-effects" << "\n");
	  benefit += getConstantBenefit(L, I, newConst, constInstructions, blockPreds);
	}

      }

    }
  }

  if(ArgC)
    DEBUG(dbgs() << "<-- Total benefit, setting " << *ArgI << " to " << *ArgC << ": " << benefit << "\n");
  else
    DEBUG(dbgs() << "<-- Total benefit, setting " << *ArgI << " to an unknown constant: " << benefit << "\n");

  return benefit;

}

bool LoopPeelHeuristicsPass::runOnLoop(Loop* L, LPPassManager& LPM) {
  
  BasicBlock* loopHeader = L->getHeader();
  BasicBlock* loopPreheader = L->getLoopPreheader();

  loopBenefit = 0;
  if(loopHeader)
    loopHeaderName = loopHeader->getNameStr();
  else
    loopHeaderName = "Unknown";

  if((!loopHeader) || (!loopPreheader)) {
    DEBUG(dbgs() << "Can't evaluate loop " << L << " because it doesn't have a header or preheader" << "\n");
    return false;
  }

  DenseMap<Instruction*, Constant*> constInstructions;
  DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> > blockPreds;

  std::vector<BasicBlock*> loopBlocks = L->getBlocks();

  for(std::vector<BasicBlock*>::iterator I = loopBlocks.begin(), E = loopBlocks.end(); I != E; ++I) {

    BasicBlock* block = *I;

    for(pred_iterator PI = pred_begin(block), E = pred_end(block); PI != E; ++PI) {
      blockPreds[block].insert(*PI);
    }

  }

  loopBenefit = 0;
  // Proceed to push the frontier of instructions with all-constant operands! Count a score as we go,
  // using some bonuses suggested from code in InlineCost.cpp attempting a similar game.

  for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {

    PHINode* PI = cast<PHINode>(I);
    Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
    if(preheaderVal) {
      if(Constant* C = dyn_cast<Constant>(preheaderVal)) {
	DEBUG(dbgs() << "--> Top level setting constant PHI node\n");
	loopBenefit += getConstantBenefit(L, I, C, constInstructions, blockPreds);
	DEBUG(dbgs() << "<-- Top level setting constant PHI node\n");	
      }
      else {
	DEBUG(dbgs() << "Top level: " << *PI << " not constant on edge from preheader\n");
      }
    }
    else {
      DEBUG(dbgs() << "Top level: " << *PI << ": no value on preheader incoming edge??\n");
    }

  }

  return false;

}

void LoopPeelHeuristicsPass::print(raw_ostream &OS, const Module*) const {

  OS << "Loop " << loopHeaderName << " peel score: " << loopBenefit << "\n";

}
