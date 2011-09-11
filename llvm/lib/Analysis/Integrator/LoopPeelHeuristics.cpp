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
  
  class PeelHeuristicsRun {

    Loop* L;

    unsigned int exitEdges;
    unsigned int exitEdgesEliminated;
    unsigned int blocksKilled;
    unsigned int totalBlocks;
    unsigned int headerPhis;
    unsigned int headerPhisDefined;
    unsigned int callsMadeDirect;
    unsigned int callArgumentsMadeConstant;
    unsigned int nonPhiInstructionsEliminated;
    unsigned int totalNonPhiInstructions;
    unsigned int unknownConstantBranches;
    bool latchBranchEliminated;
    bool allPhisConstantFromPreheader;
    std::string loopHeaderName;

    DenseMap<Instruction*, Constant*> constInstructions;
    DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> > blockPreds;

    void getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
    void getConstantBenefit(Instruction* I, Constant* C);
    void getPHINodeBenefit(PHINode* PN);

  public:

    PeelHeuristicsRun() {
      exitEdges = 0;
      exitEdgesEliminated = 0;
      blocksKilled = 0;
      totalBlocks = 0;
      headerPhis = 0;
      headerPhisDefined = 0;
      callsMadeDirect = 0;
      callArgumentsMadeConstant = 0;
      nonPhiInstructionsEliminated = 0;
      totalNonPhiInstructions = 0;
      unknownConstantBranches = 0;
      latchBranchEliminated = false;
      allPhisConstantFromPreheader = true;
    }
    bool runOnLoop(Loop *L, LPPassManager&);
    void print(raw_ostream &OS, const Module*) const;

  };

  class LoopPeelHeuristicsPass : public LoopPass {

    PeelHeuristicsRun currentRun;

  public:

    static char ID;

    explicit LoopPeelHeuristicsPass() : LoopPass(ID) { DEBUG(dbgs() << "Constructor!\n"); }
    bool runOnLoop(Loop *L, LPPassManager& LPM) {
      currentRun = PeelHeuristicsRun();
      return currentRun.runOnLoop(L, LPM);
    }
    void print(raw_ostream &OS, const Module* M) const {
      currentRun.print(OS, M);
    }
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

// This whole thing is basically a constant propagation simulation -- rather than modifying the code in place like the real constant prop,
// we maintain shadow structures indicating which instructions have been folded and which basic blocks eliminated.
// It might turn out to be a better idea to find out whether peeling is useful by just doing it and optimising! I'll see...

void PeelHeuristicsRun::getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred) {

  DEBUG(dbgs() << "--> Getting benefit due elimination of predecessor " << BBPred->getName() << " from BB " << BB->getName() << "\n");

  if(!L->contains(BB)) {
    DEBUG(dbgs() << "<-- Returning constant bonus because " << BB->getName() << " not in loop" << "\n");
    exitEdgesEliminated++;
    return;
  }

  if(BBPred == L->getLoopLatch()) {
    DEBUG(dbgs() << "<-- Eliminated the latch branch!");
    latchBranchEliminated = true;
    return;
  }

  SmallSet<BasicBlock*, 4>& thisBlockPreds = blockPreds[BB];

  thisBlockPreds.erase(BBPred);
  if(thisBlockPreds.size() == 0) {
    // This BB is dead! Remove it as a predecessor to all successor blocks and see if that helps anything.
    DEBUG(dbgs() << "Block is dead!\n");
    blocksKilled++;
    for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      BasicBlock* deadBB = *SI;
      for(BasicBlock::iterator BI = deadBB->begin(), BE = deadBB->end(); BI != BE; BI++) {
	if(!isa<PHINode>(BI)) {
	  DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(BI);
	  if(it != constInstructions.end()) {
	    DEBUG(dbgs() << "Dead instruction " << *BI << " had already been constant folded\n");
	  }
	  else {
	    DEBUG(dbgs() << "Instruction " << *BI << " eliminated\n");
	    nonPhiInstructionsEliminated++;
	  }
	}
      }
      getRemoveBlockPredBenefit(*SI, BB);
    }
  }
  else {
    // See if any of our PHI nodes are now effectively constant
    for(BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E && isa<PHINode>(*I); ++I) {
      PHINode* PN = cast<PHINode>(I);
      getPHINodeBenefit(PN);
    }
  }

  DEBUG(dbgs() << "<--\n");

}

void PeelHeuristicsRun::getPHINodeBenefit(PHINode* PN) {

  DEBUG(dbgs() << "Checking if PHI " << *PN << " is now constant" << "\n");

  BasicBlock* BB = PN->getParent();
  SmallSet<BasicBlock*, 4>& thisBlockPreds = blockPreds[BB];
  Constant* constValue = 0;

  if(BB == L->getHeader()) {
    headerPhisDefined++;
    DEBUG(dbgs() << "Ignoring because in the loop header\n");
    return;
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
    getConstantBenefit(PN, constValue);
  }
  else {
    DEBUG(dbgs() << "Not constant\n");
    return;
  }

}

void PeelHeuristicsRun::getConstantBenefit(Instruction* ArgI, Constant* ArgC) {

  if(!L->contains(ArgI)) { // Instructions outside the loop are neither here nor there if we're unrolling the loop.
    DEBUG(dbgs() << *ArgI << " not in loop, ignoring\n");
    return;
  }

  DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(ArgI);
  if(it != constInstructions.end()) { // Have we already rendered this instruction constant?
    DEBUG(dbgs() << *ArgI << " already constant\n");
    return;
  }

  constInstructions[ArgI] = ArgC;
  if(!isa<PHINode>(ArgI)) {
    if (!(ArgI->mayHaveSideEffects() || isa<AllocaInst>(ArgI))) // A particular side-effect
      nonPhiInstructionsEliminated++;
    else
      DEBUG(dbgs() << "Not eliminating instruction due to side-effects\n");
  }

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
	DEBUG(dbgs() << "Found indirect->direct call promotion\n");
	callsMadeDirect++;
      }
    } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
      // Turning an indirect call into a direct call is a BIG win
      if (II->getCalledValue() == ArgI) {
	DEBUG(dbgs() << "Found indirect->direct call promotion\n");
	callsMadeDirect++;
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
	      getRemoveBlockPredBenefit(otherTarget, TI->getParent());
	  }
	}
	else {
	  // We couldn't be sure which block the branch will go to, but its target will be constant.
	  // Give a static bonus to indicate that more advanced analysis might be able to eliminate the branch.
	  DEBUG(dbgs() << "Awarded unconditional branch to unknown target bonus" << "\n");
	  unknownConstantBranches++;
	}

      }
      else {
	// We couldn't be sure where the branch will go because we only know the operand is constant, not its value.
	// We usually don't know because this is the return value of a call, or the result of a load. Give a small bonus
	// as the call might be inlined or similar.
	DEBUG(dbgs() << "Unknown constant in branch or switch" << "\n");
	unknownConstantBranches++;
      }
    }
    else {
      // An ordinary instruction. Give bonuses or penalties for particularly fruitful or difficult instructions,
      // then count the benefits of that instruction becoming constant.
      if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
	DEBUG(dbgs() << "Constant call argument\n");
	callArgumentsMadeConstant++;
      }

      // Try to calculate a constant value resulting from this instruction. Only possible if
      // this instruction is simple (e.g. arithmetic) and its arguments have known values, or don't matter.

      PHINode* PN;
      if((PN = dyn_cast<PHINode>(I))) {
	// PHI nodes are special because of their BB arguments, and the special-case "constant folding" that affects them
	getPHINodeBenefit(PN);
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
	  getConstantBenefit(I, newConst);
	}

      }

    }
  }

  DEBUG(dbgs() << "<--\n");

}

bool PeelHeuristicsRun::runOnLoop(Loop* L, LPPassManager& LPM) {
  
  this->L = L;
  BasicBlock* loopHeader = L->getHeader();
  BasicBlock* loopPreheader = L->getLoopPreheader();

  if(loopHeader)
    loopHeaderName = loopHeader->getNameStr();
  else
    loopHeaderName = "Unknown";

  if((!loopHeader) || (!loopPreheader)) {
    DEBUG(dbgs() << "Can't evaluate loop " << L << " because it doesn't have a header or preheader" << "\n");
    return false;
  }

  std::vector<BasicBlock*> loopBlocks = L->getBlocks();

  for(std::vector<BasicBlock*>::iterator I = loopBlocks.begin(), E = loopBlocks.end(); I != E; ++I) {

    BasicBlock* block = *I;
    totalBlocks++;

    for(pred_iterator PI = pred_begin(block), E = pred_end(block); PI != E; ++PI) {
      blockPreds[block].insert(*PI);
    }

    for(BasicBlock::iterator BI = (*I)->begin(), BE = (*I)->end(); BI != BE; BI++) {
      if(!isa<PHINode>(BI))
	totalNonPhiInstructions++;
    }

  }

  // Proceed to push the frontier of instructions with all-constant operands! Count a score as we go,
  // using some bonuses suggested from code in InlineCost.cpp attempting a similar game.

  for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {

    PHINode* PI = cast<PHINode>(I);
    headerPhis++;
    Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
    if(preheaderVal) {
      if(Constant* C = dyn_cast<Constant>(preheaderVal)) {
	DEBUG(dbgs() << "--> Top level setting constant PHI node\n");
	getConstantBenefit(I, C);
	DEBUG(dbgs() << "<-- Top level setting constant PHI node\n");	
      }
      else {
	allPhisConstantFromPreheader = false;
	DEBUG(dbgs() << "Top level: " << *PI << " not constant on edge from preheader\n");
      }
    }
    else {
      allPhisConstantFromPreheader = false;
      DEBUG(dbgs() << "Top level: " << *PI << ": no value on preheader incoming edge??\n");
    }

  }

  SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> exitEdges;
  L->getExitEdges(exitEdges);

  this->exitEdges = exitEdges.size();

  return false;

}

void PeelHeuristicsRun::print(raw_ostream &OS, const Module*) const {

    OS << "Loop " << loopHeaderName << ":\n";
    OS << "Killed " << blocksKilled << "/" << totalBlocks << " blocks\n";
    OS << "Eliminated " << nonPhiInstructionsEliminated << "/" << totalNonPhiInstructions << "\n";
    if(!allPhisConstantFromPreheader)
      OS << "Not all header PHIs were constant\n";
    else
      OS << "Defined " << headerPhisDefined << "/" << headerPhis << "next-iteration PHIs\n";
    OS << "Call arguments defined: " << callArgumentsMadeConstant << "\n";
    OS << "Indirect to direct call promotions: " << callsMadeDirect << "\n";
    OS << "Branch or switch instructions given unknown constant argument: " << unknownConstantBranches << "\n";
    if(latchBranchEliminated)
      OS << "Latch branch eliminated!\n";

}
