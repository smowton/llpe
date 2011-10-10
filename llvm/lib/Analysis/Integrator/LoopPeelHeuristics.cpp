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
// Basically this is simplistic SCCP plus some use of MemDep to find out how many instructions
// from the loop body would likely get evaluated if we peeled an iterations.
// We also consider the possibility of concurrently peeling a group of nested loops.
// The hope is that the information provided is both more informative and quicker to obtain than just speculatively
// peeling and throwing a round of -std-compile-opt at the result.
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
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include <string>
#include <algorithm>

#define LPDEBUG(x) DEBUG(dbgs() << dbgind() << x)

using namespace llvm;

namespace {
  
  class HypotheticalConstantFolder {

    Function* F;
    DenseMap<Value*, Constant*>& constInstructions;
    // Edges considered removed for the purpose of estimating constant prop benefit
    SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& ignoreEdges;
    SmallSet<BasicBlock*, 4>& outBlocks;
    SmallVector<Instruction*, 16> eliminatedInstructions;
    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> eliminatedEdges;

    TargetData* TD;
    AliasAnalysis* AA;

    int debugIndent;

    void getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
    void getConstantBenefit(Value* V, Constant* C);
    void realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred);
    void realGetConstantBenefit(Value* V, Constant* C);
    void getPHINodeBenefit(PHINode* PN);
    bool tryForwardLoad(LoadInst* LI, const MemDepResult& Res);
    std::string dbgind();

  public:

    HypotheticalConstantFolder(Function* FIn,
			       DenseMap<Value*, Constant*>& insts, 
			       SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& edges, 
			       SmallSet<BasicBlock*, 4> oobBlocks, 
			       SmallVector<Instruction*, 16>& elimResult, 
			       SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>& edgeResult,
			       AliasAnalysis* AA,
			       TargetData* _TD) : 
      F(FIn), constInstructions(insts), ignoreEdges(edges), outBlocks(oobBlocks), 
      eliminatedInstructions(elimResult), eliminatedEdges(edgeResult), TD(_TD) { }

    void getBenefit(const SmallVector<Value*, 4>& roots);

  };

  class PeelHeuristicsLoopRunStats {

  public:

    unsigned int exitEdges;
    unsigned int exitEdgesEliminated;
    unsigned int blocksKilled;
    unsigned int totalBlocks;
    unsigned int headerPhis;
    unsigned int headerPhisDefined;
    unsigned int nonPhiInstructionsEliminated;
    unsigned int totalNonPhiInstructions;
    bool latchBranchEliminated;
    bool allPhisConstantFromPreheader;

    PeelHeuristicsLoopRunStats() {
      exitEdges = 0;
      exitEdgesEliminated = 0;
      blocksKilled = 0;
      totalBlocks = 0;
      headerPhis = 0;
      headerPhisDefined = 0;
      nonPhiInstructionsEliminated = 0;
      totalNonPhiInstructions = 0;
      latchBranchEliminated = false;
      allPhisConstantFromPreheader = false;
    }

  };

  class PeelHeuristicsLoopRun {

    LoopInfo* LI;
    TargetData* TD;

    DenseMap<Loop*, PeelHeuristicsLoopRun> childLoops;

    std::string loopHeaderName;
    bool doConstProp;

    int debugIndent;

    void accountElimInstruction(Instruction*);
    void doForAllLoops(void (*callback)(PeelHeuristicsLoopRun*), llvm::Instruction*);

    std::string dbgind();

  public:

    Loop* L;
    PeelHeuristicsLoopRun* parentRun;

    PeelHeuristicsLoopRunStats stats;
    PeelHeuristicsLoopRunStats statsBefore;

    PeelHeuristicsLoopRun() : doConstProp(true) { }

    bool doSimulatedPeel(DenseMap<Value*, Constant*>&, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>&, PeelHeuristicsLoopRun* parent, TargetData*, AliasAnalysis*);
    void getAllChildren(std::vector<PeelHeuristicsLoopRun*>&, bool topLevel);
    void doInitialStats(Loop*, LoopInfo*);
    void setDebugIndent(int);
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
      AU.addRequired<AliasAnalysis>();
      AU.setPreservesAll();

    }

  };

  char LoopPeelHeuristicsPass::ID = 0;

}

bool blockIsDead(BasicBlock*, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>&);

FunctionPass *llvm::createLoopPeelHeuristicsPass() {
  return new LoopPeelHeuristicsPass();
}

INITIALIZE_PASS(LoopPeelHeuristicsPass, "peelheuristics", "Score loops for peeling benefit", false, false);

// This whole thing is basically a constant propagation simulation -- rather than modifying the code in place like the real constant prop,
// we maintain shadow structures indicating which instructions have been folded and which basic blocks eliminated.
// It might turn out to be a better idea to find out whether peeling is useful by just doing it and optimising! I'll see...

std::string ind(int i) {

  char* arr = (char*)alloca(i+1);
  for(int j = 0; j < i; j++)
    arr[j] = ' ';
  arr[i] = '\0';
  return std::string(arr);

}

void incBlocksElim(PeelHeuristicsLoopRun* run) {

  run->stats.blocksKilled++;

}

void incElimInstructions(PeelHeuristicsLoopRun* run) {

  run->stats.nonPhiInstructionsEliminated++;

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

std::string HypotheticalConstantFolder::dbgind() {

  return ind(debugIndent);

}

std::string PeelHeuristicsLoopRun::dbgind() {

  return ind(debugIndent);

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

void HypotheticalConstantFolder::realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred) {

  LPDEBUG("Getting benefit due elimination of predecessor " << BBPred->getName() << " from BB " << BB->getName() << "\n");

  eliminatedEdges.push_back(std::make_pair(BBPred, BB));

  if(outBlocks.count(BB)) {
    LPDEBUG(BB->getName() << " not under consideration" << "\n");
    return;
  }

  ignoreEdges.insert(std::make_pair(BBPred, BB));

  if(blockIsDead(BB, ignoreEdges)) {
    // This BB is dead! Kill its instructions, then remove it as a predecessor to all successor blocks and see if that helps anything.
    LPDEBUG("Block is dead!\n");
    for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; BI++) {
      if(!isa<PHINode>(BI)) {
	DenseMap<Value*, Constant*>::iterator it = constInstructions.find(BI);
	if(it != constInstructions.end()) {
	  LPDEBUG("Dead instruction " << *BI << " had already been constant folded\n");
	}
	else {
	  LPDEBUG("Instruction " << *BI << " eliminated\n");
	  eliminatedInstructions.push_back(BI);
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

}

void HypotheticalConstantFolder::getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred) {

  debugIndent += 2;
  realGetRemoveBlockPredBenefit(BB, BBPred);
  debugIndent -= 2;

}

void HypotheticalConstantFolder::getPHINodeBenefit(PHINode* PN) {

  LPDEBUG("Checking if PHI " << *PN << " is now constant" << "\n");

  if(constInstructions.find(PN) != constInstructions.end()) {
    LPDEBUG("Already constant");
    return;
  }

  BasicBlock* BB = PN->getParent();
  Constant* constValue = 0;

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {

    if(ignoreEdges.count(std::make_pair(*PI, BB)))
      continue;

    Value* predValue = PN->getIncomingValueForBlock(*PI);
    Constant* predConst = dyn_cast<Constant>(predValue);
    Instruction* predInst;
    if(!predConst) {
      if((predInst = dyn_cast<Instruction>(predValue))) {
	DenseMap<Value*, Constant*>::iterator it = constInstructions.find(predInst);
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
    LPDEBUG("Constant at " << *constValue << "\n");
    getConstantBenefit(PN, constValue);
  }
  else {
    LPDEBUG("Not constant\n");
    return;
  }

}

void PeelHeuristicsLoopRun::accountElimInstruction(Instruction* I) {

  if(instructionCounts(I))
    doForAllLoops(&incElimInstructions, I);

}

bool blockIsDead(BasicBlock* BB, const SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& ignoreEdges) {

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; PI++) {
      
    if(!ignoreEdges.count(std::make_pair(*PI, BB)))
      return false;

  }

  return true;

}

void HypotheticalConstantFolder::realGetConstantBenefit(Value* ArgV, Constant* ArgC) {

  Instruction* ArgI = dyn_cast<Instruction>(ArgV);

  if(ArgI && outBlocks.count(ArgI->getParent())) { 
    LPDEBUG(*ArgI << " not under consideration, ignoring\n");
    return;
  }

  DenseMap<Value*, Constant*>::iterator it = constInstructions.find(ArgV);
  if(it != constInstructions.end()) { // Have we already rendered this instruction constant?
    LPDEBUG(*ArgV << " already constant\n");
    return;
  }
 
  constInstructions[ArgV] = ArgC;
  if(ArgI && !isa<PHINode>(ArgI)) {
    if (!(ArgI->mayHaveSideEffects() || isa<AllocaInst>(ArgI))) { // A particular side-effect
      eliminatedInstructions.push_back(ArgI);
    }
    else {
      LPDEBUG("Not eliminating instruction due to side-effects\n");
    }
  }

  // A null value means we know the result will be constant, but we're not sure what.

  if(ArgC)
    LPDEBUG("Getting benefit due to value " << *ArgV << " having constant value " << *ArgC << "\n");
  else
    LPDEBUG("Getting benefit due to value " << *ArgV << " having an unknown constant value" << "\n");

  for (Value::use_iterator UI = ArgV->use_begin(), E = ArgV->use_end(); UI != E;++UI){

    Instruction* I;
    if(!(I = dyn_cast<Instruction>(*UI))) {
      LPDEBUG("Instruction has a non-instruction user: " << *UI << "\n");
      continue;
    }

    if(blockIsDead(I->getParent(), ignoreEdges)) {
      LPDEBUG("User instruction " << *I << " already eliminated (in dead block)\n");
      continue;
    }

    LPDEBUG("Considering user instruction " << *I << "\n");

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
	  LPDEBUG("Branch or switch instruction given known target: " << target->getName() << "\n");
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
	  LPDEBUG("Promoted conditional to unconditional branch to unknown target\n");
	}

      }
      else {
	// We couldn't be sure where the branch will go because we only know the operand is constant, not its value.
	// We usually don't know because this is the return value of a call, or the result of a load. Give a small bonus
	// as the call might be inlined or similar.
	LPDEBUG("Unknown constant in branch or switch\n");
      }
      eliminatedInstructions.push_back(I);
    }
    else {
      // An ordinary instruction. Give bonuses or penalties for particularly fruitful or difficult instructions,
      // then count the benefits of that instruction becoming constant.
      if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
	LPDEBUG("Constant call argument\n");
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

	bool someArgumentUnknownConstant = false;

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
	    DenseMap<Value*, Constant*>::iterator it = constInstructions.find(OperandI);
	    if(it != constInstructions.end()) {
	      instOperands.push_back(it->second);
	      if(!it->second)
		someArgumentUnknownConstant = true;
	    }
	    else {
	      LPDEBUG("Not constant folding yet due to non-constant argument " << *OperandI << "\n");
	      break;
	    }
	  }
	  else {
	    LPDEBUG((*ArgV) << " has a non-instruction, non-constant argument: " << (*op) << "\n");
	    if(isa<CastInst>(I) || isa<GetElementPtrInst>(I)) {
	      
	    }
	    break;
	  }
	}

	if(instOperands.size() == I->getNumOperands()) {
	  Constant* newConst = 0;
	  if(!someArgumentUnknownConstant) {
	    if (const CmpInst *CI = dyn_cast<CmpInst>(I))
	      newConst = ConstantFoldCompareInstOperands(CI->getPredicate(), instOperands[0], instOperands[1], this->TD);
	    else if(isa<LoadInst>(I))
	      newConst = ConstantFoldLoadFromConstPtr(instOperands[0], this->TD);
	    else
	      newConst = ConstantFoldInstOperands(I->getOpcode(), I->getType(), instOperands.data(), I->getNumOperands(), this->TD);
	  }

	  if(newConst) {
	    LPDEBUG("User " << *I << " now constant at " << *newConst << "\n");
	  }
	  else {
	    if(I->mayReadFromMemory() || I->mayHaveSideEffects()) {
	      LPDEBUG("User " << *I << " may read or write global state; not propagating\n");
	      continue;
	    }
	    else if(someArgumentUnknownConstant) {
	      LPDEBUG("User " << *I << " will have an unknown constant value too\n");
	    } 
	    else {
	      LPDEBUG("User " << *I << " has all-constant arguments, but couldn't be constant folded" << "\n");
	    }
	  }
	  getConstantBenefit(I, newConst);
	}

      }

    }
  }

}

void HypotheticalConstantFolder::getConstantBenefit(Value* ArgV, Constant* ArgC) {

  debugIndent += 2;
  realGetConstantBenefit(ArgV, ArgC);
  debugIndent -= 2;

}

bool HypotheticalConstantFolder::tryForwardLoad(LoadInst* LI, const MemDepResult& Res) {

  if(StoreInst* SI = dyn_cast<StoreInst>(Res.getInst())) {
    if(Constant* SC = dyn_cast<Constant>(SI->getOperand(0))) {

      LPDEBUG(*LI << " defined by " << *SI << "\n");
      eliminatedInstructions.push_back(LI);
      getConstantBenefit(LI, SC);
      return true;

    }
    else {
      LPDEBUG(*LI << " is defined by " << *SI << " with a non-constant operand\n");
    }
  }
  else if(LoadInst* DefLI = dyn_cast<LoadInst>(Res.getInst())) {
		
    DenseMap<Value*, Constant*>::iterator DefLIIt = constInstructions.find(DefLI);
    if(DefLIIt != constInstructions.end()) {
		  
      LPDEBUG(*LI << " defined by " << *(DefLIIt->second) << "\n");
      eliminatedInstructions.push_back(LI);
      getConstantBenefit(LI, DefLIIt->second);
      return true;

    }

  }
  else {
    LPDEBUG(*LI << " is defined by " << *(Res.getInst()) << " which is not a simple store\n");
  }

  return false;

}

void HypotheticalConstantFolder::getBenefit(const SmallVector<Value*, 4>& roots) {

  for(SmallVector<Value*, 4>::const_iterator RI = roots.begin(), RE = roots.end(); RI != RE; RI++) {

    getConstantBenefit(*RI, constInstructions[*RI]);

  }

  bool anyStoreForwardingBenefits = true;

  while(anyStoreForwardingBenefits) {

    LPDEBUG("Considering store-to-load forwards...\n");
    anyStoreForwardingBenefits = false;

    MemoryDependenceAnalyser MD;
    MD.init(AA);

    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; FI++) {

      BasicBlock* BB = FI;

      if(outBlocks.count(BB))
	continue;

      if(blockIsDead(BB, ignoreEdges))
	continue;

      for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; II++) {

	if(LoadInst* LI = dyn_cast<LoadInst>(II)) {

	  DenseMap<Value*, Constant*>::iterator it = constInstructions.find(LI);

	  if(it != constInstructions.end()) {
	    LPDEBUG("Ignoring " << *LI << " because it's already constant\n");
	    continue;
	  }

	  MemDepResult Res = MD.getDependency(LI, constInstructions, ignoreEdges);

	  if(Res.isClobber()) {
	    LPDEBUG(*LI << " is locally clobbered by " << Res.getInst() << "\n");
	    continue;
	  }
	  else if(Res.isDef()) {
	    anyStoreForwardingBenefits |= tryForwardLoad(LI, Res);
	  }
	  else { // Nonlocal
	      
	    Value* LPointer = LI->getOperand(0);

	    if(Instruction* LPointerI = dyn_cast<Instruction>(LPointer)) {
	      DenseMap<Value*, Constant*>::iterator it = constInstructions.find(LPointerI);
	      if(it != constInstructions.end())
		LPointer = it->second;
	    }

	    SmallVector<NonLocalDepResult, 4> NLResults;

	    MD.getNonLocalPointerDependency(LPointer, true, BB, NLResults, constInstructions, ignoreEdges);

	    assert(NLResults.size() > 0);

	    const MemDepResult* TheResult = 0;
	      
	    for(unsigned int i = 0; i < NLResults.size(); i++) {
		
	      const MemDepResult& Res = NLResults[i].getResult();
	      if(Res.isNonLocal())
		continue;
	      else if(Res.isClobber()) {
		LPDEBUG(*LI << " is nonlocally clobbered by " << *(Res.getInst()) << "\n");
		break;
	      }
	      else {
		if(TheResult) {
		  LPDEBUG(*LI << " depends on multiple instructions, ignoring\n");
		  TheResult = 0;
		  break;
		}
		else {
		  TheResult = &Res;
		}
	      }
		
	    }

	    if(TheResult)
	      anyStoreForwardingBenefits |= tryForwardLoad(LI, *TheResult);

	  }
	    
	}

      }

    }

    if(anyStoreForwardingBenefits) {
      LPDEBUG("At least one load was made constant; trying again\n");
    }
    else {
      LPDEBUG("No loads were made constant\n");
    }

  }
  

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

bool PeelHeuristicsLoopRun::doSimulatedPeel(DenseMap<Value*, Constant*>& outerConsts, SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4>& outerIgnoreEdges, PeelHeuristicsLoopRun* parentRun, TargetData* TD, AliasAnalysis* AA) {
  
  // Deep copies to avoid work on this loop affecting our parent loops.
  this->TD = TD;
  DenseMap<Value*, Constant*> constInstructions = outerConsts;
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> ignoreEdges = outerIgnoreEdges;
  statsBefore = stats;

  this->parentRun = parentRun;

  BasicBlock* loopHeader = L->getHeader();
  BasicBlock* loopPreheader = L->getLoopPreheader();
  BasicBlock* loopLatch = L->getLoopLatch();

  if(loopHeader)
    loopHeaderName = loopHeader->getNameStr();
  else
    loopHeaderName = "Unknown";

  if((!loopHeader) || (!loopPreheader) || (!loopLatch)) {
    LPDEBUG("Can't evaluate loop " << *L << " because it doesn't have a header, preheader or latch" << "\n");
    return false;
  }

  LPDEBUG("Peeling loop with header '" << loopHeader->getName() << "'\n");

  ignoreEdges.insert(std::make_pair(loopLatch, loopHeader));

  // Is it worth doing constant prop here at all? We say it is if any PHI nodes are rendered constant by peeling
  // which would not have been if it weren't for our parent. That is, peeling is especially effective if conducted
  // in concert with our parent loop. If this loop would yield a constant regardless, we will find that out later
  // as the pass considers all loops as a root at top level.

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
      DenseMap<Value*, Constant*>::iterator outerConst = constInstructions.find(preheaderInst);
      if(outerConst != constInstructions.end()) {
	anyPhiImproved = true;
	break;
      }

    }

    if(!anyPhiImproved) {

      LPDEBUG("Not peeling loop with header " << L->getHeader()->getName() << " because none of its PHI nodes are improved by concurrent unrolling of its parents\n");
      doConstProp = false;

    }

  }

  // Proceed to push the frontier of instructions with all-constant operands!

  if(doConstProp) {

    stats.allPhisConstantFromPreheader = true;
    SmallVector<Value*, 4> rootInstructions;

    SmallSet<Instruction*, 4> headerLatchInputs;

    for(BasicBlock::iterator I = loopHeader->begin(), E = loopHeader->end(); I != E && isa<PHINode>(*I); I++) {

      PHINode* PI = cast<PHINode>(I);
      stats.headerPhis++;
      Value* latchValue = PI->getIncomingValueForBlock(loopLatch);
      if(Instruction* latchInstruction = dyn_cast<Instruction>(latchValue))
	headerLatchInputs.insert(latchInstruction);
      else
	stats.headerPhisDefined++; // This PHI is already defined! It's an almost-invariant (different on the first run, i.e. 'bool firsttime')
      Value* preheaderVal = PI->getIncomingValueForBlock(loopPreheader);
      if(!preheaderVal) {
	stats.allPhisConstantFromPreheader = false;
	LPDEBUG("Top level: " << *PI << ": no value on preheader incoming edge??\n");
	continue;
      }

      Constant* preheaderConst = dyn_cast<Constant>(preheaderVal);
      if(!preheaderConst) {
	Instruction* I = cast<Instruction>(preheaderVal);
	DenseMap<Value*, Constant*>::iterator outerConst = constInstructions.find(I);
	if(outerConst != constInstructions.end())
	  preheaderConst = outerConst->second;
      }

      if(preheaderConst) {
	LPDEBUG("Top level setting constant PHI node\n");
	rootInstructions.push_back(PI);
	constInstructions[PI] = preheaderConst;
      }
      else {
	stats.allPhisConstantFromPreheader = false;
	LPDEBUG("Top level: " << *PI << " not constant on edge from preheader\n");
      }

    }

    Function* F = loopHeader->getParent();
    SmallSet<BasicBlock*, 4> outerBlocks;
    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; FI++) {
      if(!L->contains(FI))
	outerBlocks.insert(FI);
    }

    SmallVector<Instruction*, 16> eliminatedInstructions;
    SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> eliminatedEdges;

    HypotheticalConstantFolder H(F, constInstructions, ignoreEdges, outerBlocks, eliminatedInstructions, eliminatedEdges, AA, TD);
    H.getBenefit(rootInstructions);

    for(SmallVector<Instruction*, 16>::iterator II = eliminatedInstructions.begin(), IE = eliminatedInstructions.end(); II != IE; II++) {

      Instruction* I = *II;
      accountElimInstruction(I);
      if(headerLatchInputs.count(I))
	stats.headerPhisDefined++;

    }

    SmallVector<BasicBlock*, 4> blocksKilled;

    for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator EI = eliminatedEdges.begin(), EE = eliminatedEdges.end(); EI != EE; EI++) {

      if(blockIsDead(EI->second, ignoreEdges))
	blocksKilled.push_back(EI->second);

      if(!L->contains(EI->second)) {
	Loop* outsideLimit = LI->getLoopFor(EI->second);
	PeelHeuristicsLoopRun* thisRun = this;
	while(thisRun && thisRun->L != outsideLimit) {
	  thisRun->stats.exitEdgesEliminated++;
	  thisRun = thisRun->parentRun;
	}
      }

      if((*EI) == std::make_pair(loopLatch, loopHeader)) {

	stats.latchBranchEliminated = true;

      }

    }

    std::sort(blocksKilled.begin(), blocksKilled.end());
    std::unique(blocksKilled.begin(), blocksKilled.end());
    for(SmallVector<BasicBlock*, 4>::iterator BI = blocksKilled.begin(), BE = blocksKilled.end(); BI != BE; BI++) {
      doForAllLoops(&incBlocksElim, (*BI)->begin());
    }

  }

  // Try concurrently peeling child loops

  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator CI = childLoops.begin(), CE = childLoops.end(); CI != CE; CI++) {

    LPDEBUG("======>\n");
    CI->second.doSimulatedPeel(constInstructions, ignoreEdges, this, TD, AA);
    LPDEBUG("<======\n");

  }

  return false;

}

void PeelHeuristicsLoopRun::setDebugIndent(int x) {

  debugIndent = x;
  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator CI = childLoops.begin(), CE = childLoops.end(); CI != CE; CI++) {

    CI->second.setDebugIndent(x+2);

  }

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
    if(stats.latchBranchEliminated)
      OS << ind(indent+2) << "Latch branch eliminated!\n";
    indent += 4;
  }

  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::const_iterator LI = childLoops.begin(), LE = childLoops.end(); LI != LE; LI++)
    LI->second.print(OS, indent);

}

bool LoopPeelHeuristicsPass::runOnFunction(Function& F) {

  LoopInfo& LI = getAnalysis<LoopInfo>();
  TargetData* TD = getAnalysisIfAvailable<TargetData>();

  // No initial constants at top level
  DenseMap<Value*, Constant*> initialConsts;

  // Ignore no edges at top level
  SmallSet<std::pair<BasicBlock*, BasicBlock*>, 4> initialIgnoreEdges;

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

  AliasAnalysis* AA = &getAnalysis<AliasAnalysis>();

  // Now finally simulate peeling on each top-level target. The targets will recursively peel their child loops if it seems warranted.
  for(DenseMap<Loop*, PeelHeuristicsLoopRun>::iterator RI = topLevelLoops.begin(), RE = topLevelLoops.end(); RI != RE; RI++) {
   
    RI->second.setDebugIndent(0);
    RI->second.doSimulatedPeel(initialConsts, initialIgnoreEdges, 0, TD, AA);

  }

  return false;

}
