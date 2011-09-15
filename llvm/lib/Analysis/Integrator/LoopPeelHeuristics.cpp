//===- LoopPeelHeuristics.cpp - Find loops that we might want to try peeling --------===//
//
// The LLVM Compiler Infrastructure
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
#include "llvm/IntrinsicInst.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ProfileInfo.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include <string>

using namespace llvm;

namespace {
  
  class PeelHeuristicsLoopRunStats {

  public:

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

    PeelHeuristicsLoopRunStats() {
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
      allPhisConstantFromPreheader = false;
    }

  };

  class PeelHeuristicsLoopRun {

    LoopInfo* LI;

    DenseMap<Loop*, PeelHeuristicsLoopRun> childLoops;

    DenseMap<Instruction*, Constant*> constInstructions;
    DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> > blockPreds;

    std::string loopHeaderName;
    bool doConstProp;

    void getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
    void getConstantBenefit(Instruction* I, Constant* C);
    void getPHINodeBenefit(PHINode* PN);
    void accountElimInstruction(Instruction*);
    void doForAllLoops(void (*callback)(PeelHeuristicsLoopRun*), llvm::Instruction*);

  public:

    Loop* L;
    PeelHeuristicsLoopRun* parentRun;

    PeelHeuristicsLoopRunStats stats;
    PeelHeuristicsLoopRunStats statsBefore;

    PeelHeuristicsLoopRun() : doConstProp(true) { }

    bool doSimulatedPeel(DenseMap<Instruction*, Constant*>&, DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >&, PeelHeuristicsLoopRun* parent);
    void getAllChildren(std::vector<PeelHeuristicsLoopRun*>&, bool topLevel);
    void doInitialStats(Loop*, LoopInfo*);
    void print(raw_ostream &OS, int indent) const;

  };

  class LoopPeelHeuristicsPass : public FunctionPass {

    DenseMap<Loop*, PeelHeuristicsLoopRun> topLevelLoops;

  public:

    static char ID;

    explicit LoopPeelHeuristicsPass() : FunctionPass(ID) { }
    bool runOnFunction(Function& F);
    void print(raw_ostream &OS, const Module* M) const {
      for(DenseMap<Loop*, PeelHeuristicsLoopRun>::const_iterator LI = topLevelLoops.begin(), LE = topLevelLoops.end(); LI != LE; LI++) {
	LI->second.print(OS, 0);
      }
    }
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {

      AU.addRequired<LoopInfo>();
      AU.setPreservesAll();

    }

  };

  char LoopPeelHeuristicsPass::ID = 0;

}

FunctionPass *llvm::createLoopPeelHeuristicsPass() {
  return new LoopPeelHeuristicsPass();
}

INITIALIZE_PASS(LoopPeelHeuristicsPass, "peelheuristics", "Score loops for peeling benefit", false, false);

// This whole thing is basically a constant propagation simulation -- rather than modifying the code in place like the real constant prop,
// we maintain shadow structures indicating which instructions have been folded and which basic blocks eliminated.
// It might turn out to be a better idea to find out whether peeling is useful by just doing it and optimising! I'll see...

void incConstBranches(PeelHeuristicsLoopRun* run) {

  run->stats.unknownConstantBranches++;

}


void incBlocksElim(PeelHeuristicsLoopRun* run) {

  run->stats.blocksKilled++;

}

void incCallArgs(PeelHeuristicsLoopRun* run) {

  run->stats.callArgumentsMadeConstant++;

}

void incElimInstructions(PeelHeuristicsLoopRun* run) {

  run->stats.nonPhiInstructionsEliminated++;

}

void incDirectCalls(PeelHeuristicsLoopRun* run) {

  run->stats.callsMadeDirect++;

}

bool instructionCounts(Instruction* I) {

  if(isa<PHINode>(I))
    return false;
  if (isa<DbgInfoIntrinsic>(I))
    return false;
  if(BranchInst* BI = dyn_cast<BranchInst>(I))
    if(BI->isUnconditional()) // Don't count unconditional branches as they're already as specified as they're getting
      return false;
  return true;

}

void PeelHeuristicsLoopRun::doForAllLoops(void (*callback)(PeelHeuristicsLoopRun*), Instruction* I) {

  Loop* innermostLoop = LI->getLoopFor(I->getParent());
  Loop* thisL = innermostLoop;
  SmallVector<Loop*, 4> elimLoops;
  while(thisL != L) {
    elimLoops.push_back(thisL);
    thisL = thisL->getParentLoop();
  }
  PeelHeuristicsLoopRun* currentRun = this;
  callback(this);
      
  for(int i = elimLoops.size() - 1; i >= 0; i--) {
    currentRun = &(currentRun->childLoops[elimLoops[i]]);
    callback(currentRun);
  }

}

void PeelHeuristicsLoopRun::getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred) {

  DEBUG(dbgs() << "--> Getting benefit due elimination of predecessor " << BBPred->getName() << " from BB " << BB->getName() << "\n");

  if(!L->contains(BB)) {
    DEBUG(dbgs() << "<-- Returning constant bonus because " << BB->getName() << " not in loop" << "\n");
    // The following signifies that this branch exits not just this loop, but also some of our parents.
    Loop* outsideLimit = LI->getLoopFor(BB);
    PeelHeuristicsLoopRun* thisRun = this;
    while(thisRun && thisRun->L != outsideLimit) {
      thisRun->stats.exitEdgesEliminated++;
      thisRun = thisRun->parentRun;
    }
    return;
  }

  if(BBPred == L->getLoopLatch()) {
    DEBUG(dbgs() << "<-- Eliminated the latch branch!");
    stats.latchBranchEliminated = true;
    return;
  }

  SmallSet<BasicBlock*, 4>& thisBlockPreds = blockPreds[BB];

  thisBlockPreds.erase(BBPred);
  if(thisBlockPreds.size() == 0) {
    // This BB is dead! Kill its instructions, then remove it as a predecessor to all successor blocks and see if that helps anything.
    DEBUG(dbgs() << "Block is dead!\n");
    doForAllLoops(&incBlocksElim, BB->begin());
    for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; BI++) {
      if(!isa<PHINode>(BI)) {
	DenseMap<Instruction*, Constant*>::iterator it = constInstructions.find(BI);
	if(it != constInstructions.end()) {
	  DEBUG(dbgs() << "Dead instruction " << *BI << " had already been constant folded\n");
	}
	else {
	  DEBUG(dbgs() << "Instruction " << *BI << " eliminated\n");
	  accountElimInstruction(BI);
	}
      }
    }
    for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
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

void PeelHeuristicsLoopRun::getPHINodeBenefit(PHINode* PN) {

  DEBUG(dbgs() << "Checking if PHI " << *PN << " is now constant" << "\n");

  BasicBlock* BB = PN->getParent();
  SmallSet<BasicBlock*, 4>& thisBlockPreds = blockPreds[BB];
  Constant* constValue = 0;

  if(BB == L->getHeader()) {
    stats.headerPhisDefined++;
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

void PeelHeuristicsLoopRun::accountElimInstruction(Instruction* I) {

  if(instructionCounts(I))
    doForAllLoops(&incElimInstructions, I);

}

void PeelHeuristicsLoopRun::getConstantBenefit(Instruction* ArgI, Constant* ArgC) {

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
    if (!(ArgI->mayHaveSideEffects() || isa<AllocaInst>(ArgI))) { // A particular side-effect
      accountElimInstruction(ArgI);
    }
    else {
      DEBUG(dbgs() << "Not eliminating instruction due to side-effects\n");
    }
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

    if(blockPreds[I->getParent()].size() == 0) {
      DEBUG(dbgs() << "User instruction " << *I << " already eliminated\n");
      continue;
    }

    DEBUG(dbgs() << "Considering user instruction " << *I << "\n");

    // These bonuses apply whether or not we manage to render all the instruction's arguments constant:

    if (CallInst *CI = dyn_cast<CallInst>(I)) {
      // Turning an indirect call into a direct call is a BIG win
      if (CI->getCalledValue() == ArgI) {
	DEBUG(dbgs() << "Found indirect->direct call promotion\n");
	doForAllLoops(&incDirectCalls, CI);
      }
    } else if (InvokeInst *II = dyn_cast<InvokeInst>(I)) {
      // Turning an indirect call into a direct call is a BIG win
      if (II->getCalledValue() == ArgI) {
	DEBUG(dbgs() << "Found indirect->direct call promotion\n");
	doForAllLoops(&incDirectCalls, CI);
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
	  DEBUG(dbgs() << "Promoted conditional to unconditional branch to unknown target\n");
	  doForAllLoops(&incConstBranches, I);
	}

      }
      else {
	// We couldn't be sure where the branch will go because we only know the operand is constant, not its value.
	// We usually don't know because this is the return value of a call, or the result of a load. Give a small bonus
	// as the call might be inlined or similar.
	DEBUG(dbgs() << "Unknown constant in branch or switch\n");
	doForAllLoops(&incConstBranches, I);
      }
      accountElimInstruction(I);
    }
    else {
      // An ordinary instruction. Give bonuses or penalties for particularly fruitful or difficult instructions,
      // then count the benefits of that instruction becoming constant.
      if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
	DEBUG(dbgs() << "Constant call argument\n");
	doForAllLoops(incCallArgs, I);
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

void PeelHeuristicsLoopRun::doInitialStats(Loop* L, LoopInfo* LI) {

  this->L = L;
  this->LI = LI;

  for(LoopInfo::iterator LIt = L->begin(), LE = L->end(); LIt != LE; LIt++) {

    Loop* thisLoop = *LIt;
    PeelHeuristicsLoopRun& thisRun = childLoops[thisLoop];
    thisRun.doInitialStats(thisLoop, LI);
    stats.totalNonPhiInstructions += thisRun.stats.totalNonPhiInstructions;
    stats.totalBlocks += thisRun.stats.totalBlocks;

  }

  std::vector<BasicBlock*> blocks = L->getBlocks();

  for(std::vector<BasicBlock*>::iterator BI = blocks.begin(), BE = blocks.end(); BI != BE; BI++) {

    BasicBlock* BB = *BI;

    if(LI->getLoopFor(BB) == L) { 

      for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; II++) {
	if(instructionCounts(II))
	  stats.totalNonPhiInstructions++;
      }

      stats.totalBlocks++;

    }

  }

  SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> exitEdges;
  L->getExitEdges(exitEdges);
  
  stats.exitEdges = exitEdges.size();

}

void PeelHeuristicsLoopRun::getAllChildren(std::vector<PeelHeuristicsLoopRun*>& children, bool topLevel) {

  for(LoopInfo::iterator LIt = L->begin(), LE = L->end(); LIt != LE; LIt++) {
    
    Loop* thisLoop = *LIt;
    PeelHeuristicsLoopRun& thisRun = childLoops[thisLoop];
    thisRun.getAllChildren(children, false);

  }

  if(!topLevel)
    children.push_back(this);

}

bool PeelHeuristicsLoopRun::doSimulatedPeel(DenseMap<Instruction*, Constant*>& outerConsts, DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> >& outerBlockPreds, PeelHeuristicsLoopRun* parentRun) {
  
  // Deep copies to avoid work on this loop affecting our parent loops.
  constInstructions = outerConsts;
  blockPreds = outerBlockPreds;
  statsBefore = stats;

  this->parentRun = parentRun;

  BasicBlock* loopHeader = L->getHeader();
  BasicBlock* loopPreheader = L->getLoopPreheader();

  if(loopHeader)
    loopHeaderName = loopHeader->getNameStr();
  else
    loopHeaderName = "Unknown";

  if((!loopHeader) || (!loopPreheader)) {
    DEBUG(dbgs() << "Can't evaluate loop " << *L << " because it doesn't have a header or preheader" << "\n");
    return false;
  }

  // Proceed to push the frontier of instructions with all-constant operands!

  if(parentRun) {
    
    bool anyPhiImproved = false;

    for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {

      PHINode* PI = cast<PHINode>(I);
      Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
      if(!preheaderVal)
	continue;
      Constant* preheaderConst = dyn_cast<Constant>(preheaderVal);
      if(preheaderConst)
	continue;
      Instruction* preheaderInst = cast<Instruction>(preheaderVal);
      DenseMap<Instruction*, Constant*>::iterator outerConst = constInstructions.find(preheaderInst);
      if(outerConst != constInstructions.end()) {
	anyPhiImproved = true;
	break;
      }

    }

    if(!anyPhiImproved) {

      DEBUG(dbgs() << "Not peeling loop with header " << L->getHeader()->getName() << " because none of its PHI nodes are improved by concurrent unrolling of its parents\n");
      doConstProp = false;

    }

  }

  if(doConstProp) {

    stats.allPhisConstantFromPreheader = true;

    for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {

      PHINode* PI = cast<PHINode>(I);
      stats.headerPhis++;
      Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
      if(!preheaderVal) {
	stats.allPhisConstantFromPreheader = false;
	DEBUG(dbgs() << "Top level: " << *PI << ": no value on preheader incoming edge??\n");
	continue;
      }

      Constant* preheaderConst = dyn_cast<Constant>(preheaderVal);
      if(!preheaderConst) {
	Instruction* I = cast<Instruction>(preheaderVal);
	DenseMap<Instruction*, Constant*>::iterator outerConst = constInstructions.find(I);
	if(outerConst != constInstructions.end())
	  preheaderConst = outerConst->second;
      }

      if(preheaderConst) {
	DEBUG(dbgs() << "--> Top level setting constant PHI node\n");
	getConstantBenefit(I, preheaderConst);
	DEBUG(dbgs() << "<-- Top level setting constant PHI node\n");	
      }
      else {
	stats.allPhisConstantFromPreheader = false;
	DEBUG(dbgs() << "Top level: " << *PI << " not constant on edge from preheader\n");
      }

    }

  }

  // Try concurrently peeling child loops

  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator CI = childLoops.begin(), CE = childLoops.end(); CI != CE; CI++) {

    DEBUG(dbgs() << "--> Considering benefit of concurrently peeling child loop " << CI->first->getHeader()->getName() << "\n");
    CI->second.doSimulatedPeel(constInstructions, blockPreds, this);
    DEBUG(dbgs() << "<--\n");

  }

  return false;

}

std::string ind(int i) {

  char* arr = (char*)alloca(i+1);
  for(int j = 0; j < i; j++)
    arr[j] = ' ';
  arr[i] = '\0';
  return std::string(arr);

}

void PeelHeuristicsLoopRun::print(raw_ostream &OS, int indent) const {

  if(doConstProp) {
    OS << ind(indent) << "Peeling loop " << loopHeaderName << ":\n";
    OS << ind(indent+2) << "Killed " << statsBefore.blocksKilled << "->" << stats.blocksKilled << "/" << stats.totalBlocks << " blocks\n";
    OS << ind(indent+2) << "Eliminated " << statsBefore.nonPhiInstructionsEliminated << "->" << stats.nonPhiInstructionsEliminated << "/" << stats.totalNonPhiInstructions << " non-PHI instructions\n";
    if(!stats.allPhisConstantFromPreheader)
      OS << ind(indent+2) << "Not all header PHIs were constant\n";
    OS << ind(indent+2) << "Defined " << statsBefore.headerPhisDefined << "->" << stats.headerPhisDefined << "/" << stats.headerPhis << " next-iteration PHIs\n";
    OS << ind(indent+2) << "Eliminated " << statsBefore.exitEdgesEliminated << "->" << stats.exitEdgesEliminated << "/" << stats.exitEdges << " exit edges\n";
    OS << ind(indent+2) << "Call arguments defined: " << statsBefore.callArgumentsMadeConstant << "->" << stats.callArgumentsMadeConstant << "\n";
    OS << ind(indent+2) << "Indirect to direct call promotions: " << statsBefore.callsMadeDirect << "->" << stats.callsMadeDirect << "\n";
    OS << ind(indent+2) << "Branch or switch instructions given unknown constant argument: " << statsBefore.unknownConstantBranches << "->" << stats.unknownConstantBranches << "\n";
    if(stats.latchBranchEliminated)
      OS << ind(indent+2) << "Latch branch eliminated!\n";
    indent += 4;
  }

  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::const_iterator LI = childLoops.begin(), LE = childLoops.end(); LI != LE; LI++)
    LI->second.print(OS, indent);

}

bool LoopPeelHeuristicsPass::runOnFunction(Function& F) {

  LoopInfo& LI = getAnalysis<LoopInfo>();

  // No initial constants at top level
  DenseMap<Instruction*, Constant*> initialConsts;

  // All basic block predecessors intact at top level
  DenseMap<BasicBlock*, SmallSet<BasicBlock*, 4> > initialBlockPreds;

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; FI++) {

    BasicBlock* block = cast<BasicBlock>(FI);

    for(pred_iterator PI = pred_begin(block), E = pred_end(block); PI != E; ++PI) {
      initialBlockPreds[block].insert(*PI);
    }

  }

  // Count blocks and instructions in all loops
  for(LoopInfo::iterator L = LI.begin(), LE = LI.end(); L != LE; L++) {

    Loop* thisLoop = *L;
    topLevelLoops[thisLoop].doInitialStats(thisLoop, &LI);

  }

  // Copy all children so that we can consider unrolling child loops in isolation or in combination with their parent
  for(LoopInfo::iterator L = LI.begin(), LE = LI.end(); L != LE; L++) {

    std::vector<PeelHeuristicsLoopRun*> childRuns;
    Loop* thisLoop = *L;
    topLevelLoops[thisLoop].getAllChildren(childRuns, true);
    for(std::vector<PeelHeuristicsLoopRun*>::iterator CI = childRuns.begin(), CE = childRuns.end(); CI != CE; CI++)
      topLevelLoops[(*CI)->L] = **CI;

  }

  // Now finally simulate peeling on each top-level target. The targets will recursively peel their child loops if it seems warranted.
  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator RI = topLevelLoops.begin(), RE = topLevelLoops.end(); RI != RE; RI++) {
   
    RI->second.doSimulatedPeel(initialConsts, initialBlockPreds, 0);

  }

  return false;

}
