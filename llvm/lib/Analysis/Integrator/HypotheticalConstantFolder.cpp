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

#define DEBUG_TYPE "hypotheticalconstantfolder"

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h" // For isIdentifiedObject
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

#define LPDEBUG(x) DEBUG(dbgs() << dbgind() << x)

using namespace llvm;

static std::string ind(int i) {

  char* arr = (char*)alloca(i+1);
  for(int j = 0; j < i; j++)
    arr[j] = ' ';
  arr[i] = '\0';
  return std::string(arr);

}

std::string HypotheticalConstantFolder::dbgind() {

  return ind(debugIndent);

}

ValCtx HypotheticalConstantFolder::getReplacement(Value* V) {

  return parent.getReplacement(V, 0);

}

Constant* HypotheticalConstantFolder::getConstReplacement(Value* V) {

  if(Constant* C = const_cast<Constant*>(dyn_cast<Constant>(V)))
    return C;
  else
    return const_cast<Constant*>(dyn_cast<Constant>(getReplacement(V).first));

}

void HypotheticalConstantFolder::realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred) {

  LPDEBUG("Edge " << BBPred->getName() << "->" << BB->getName() << " killed\n");

  parent.setEdgeDead(BBPred, BB);

  if(parent.shouldIgnoreEdge(BBPred, BB)) {
    LPDEBUG(BBPred->getName() << "->" << BB->getName() << " ignored for const-prop purposes\n");
    return;
  }

  if(parent.shouldIgnoreBlockForDCE(BB)) {
    LPDEBUG(BB->getName() << " not under consideration" << "\n");
    return;
  }

  BlocksImproved.push_back(BB);

}

void HypotheticalConstantFolder::getRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred) {

  debugIndent += 2;
  realGetRemoveBlockPredBenefit(BB, BBPred);
  debugIndent -= 2;

}

void HypotheticalConstantFolder::getPHINodeBenefit(PHINode* PN) {

  LPDEBUG("Checking if PHI " << *PN << " is improved" << "\n");

  BasicBlock* BB = PN->getParent();
  ValCtx onlyValue = VCNull;

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {

    if(parent.edgeIsDead(*PI, BB))
      continue;

    ValCtx oldValue = make_vc(PN->getIncomingValueForBlock(*PI), 0);
    ValCtx predValue = getReplacement(oldValue.first);
    if(!onlyValue.first)
      onlyValue = predValue;
    else if(onlyValue != predValue) {
      onlyValue = VCNull;
      break;
    }

  }
  if(onlyValue.first) {
    if(getReplacement(PN) == onlyValue) {
      LPDEBUG("Already improved");
      return;
    }
    else {
      LPDEBUG("Improved to " << onlyValue << "\n");
      tryGetImprovementBenefit(PN, onlyValue, true);
    }
  }
  else {
    LPDEBUG("Not improved\n");
    return;
  }

}

void HypotheticalConstantFolder::realGetImprovementBenefit(Value* ArgV /* Local */, ValCtx Replacement) {

  parent.setReplacement(ArgV, Replacement);

  LPDEBUG("Getting benefit due to value " << *ArgV << " having improved value " << Replacement << "\n");

  for (Value::use_iterator UI = ArgV->use_begin(), E = ArgV->use_end(); UI != E;++UI) {

    Instruction* I;
    if(!(I = dyn_cast<Instruction>(*UI))) {
      LPDEBUG("Instruction has a non-instruction user: " << *UI << "\n");
      continue;
    }

    if(parent.blockIsDead(I->getParent())) {
      LPDEBUG("User instruction " << *I << " already eliminated (in dead block)\n");
      continue;
    }

    if(parent.shouldIgnoreInstruction(I)) {
      LPDEBUG(*I << " instruction not under consideration, ignoring\n");
      continue;
    }

    LPDEBUG("Considering user instruction " << *I << "\n");

    if (isa<BranchInst>(I) || isa<SwitchInst>(I)) {
      if(Constant* C = dyn_cast<Constant>(Replacement.first)) {
	// Both Branches and Switches have one potentially non-const arg which we now know is constant.
	// The mechanism used by InlineCosts.cpp here emphasises code size. I try to look for
	// time instead, by searching for PHIs that will be made constant.
	BasicBlock* target;
	if(BranchInst* BI = dyn_cast<BranchInst>(I)) {
	  // This ought to be a boolean.
	  if((cast<ConstantInt>(C))->isZero())
	    target = BI->getSuccessor(1);
	  else
	    target = BI->getSuccessor(0);
	}
	else {
	  SwitchInst* SI = cast<SwitchInst>(I);
	  unsigned targetidx = SI->findCaseValue(cast<ConstantInt>(C));
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
      }
    }
    else {
      // An ordinary instruction. Give bonuses or penalties for particularly fruitful or difficult instructions,
      // then count the benefits of that instruction becoming constant.
      if (isa<CallInst>(I) || isa<InvokeInst>(I)) {
	LPDEBUG("Improved call argument\n");
      }

      // Try to calculate a constant value resulting from this instruction. Only possible if
      // this instruction is simple (e.g. arithmetic) and its arguments have known values, or don't matter.

      if(PHINode* PN = dyn_cast<PHINode>(I)) {
	// PHI nodes are special because of their BB arguments, and the special-case "constant folding" that affects them
	getPHINodeBenefit(PN);
      }
      else if(SelectInst* SI = dyn_cast<SelectInst>(I)) {
        Constant* Cond = getConstReplacement(SI->getCondition());
	if(Cond) {
	  ValCtx newVal;
	  if(cast<ConstantInt>(Cond)->isZero())
	    newVal = make_vc(SI->getFalseValue(), 0);
	  else
	    newVal = make_vc(SI->getTrueValue(), 0);
	  if(getReplacement(SI) != newVal)
	    tryGetImprovementBenefit(SI, newVal);
	}
      }
      else {

	SmallVector<Constant*, 4> instOperands;

	// This isn't as good as it could be, because the constant-folding library wants an array of constants,
	// whereas we might have somethig like 1 && x, which could fold but x is not a Constant*. Could work around this,
	// don't at the moment.
	for(unsigned i = 0; i < I->getNumOperands(); i++) {
	  Value* op = I->getOperand(i);
	  if(Constant* C = getConstReplacement(op))
	    instOperands.push_back(C);
	  else {
	    LPDEBUG("Not constant folding yet due to non-constant argument " << *op << "\n");
	    break;
	  }
	}

	if(instOperands.size() == I->getNumOperands()) {
	  Constant* newConst = 0;
	  if (const CmpInst *CI = dyn_cast<CmpInst>(I))
	    newConst = ConstantFoldCompareInstOperands(CI->getPredicate(), instOperands[0], instOperands[1], this->TD);
	  else if(isa<LoadInst>(I))
	    newConst = ConstantFoldLoadFromConstPtr(instOperands[0], this->TD);
	  else
	    newConst = ConstantFoldInstOperands(I->getOpcode(), I->getType(), instOperands.data(), I->getNumOperands(), this->TD);

	  if(newConst) {
	    LPDEBUG("User " << *I << " now constant at " << *newConst << "\n");
	  }
	  else {
	    if(I->mayReadFromMemory() || I->mayHaveSideEffects()) {
	      LPDEBUG("User " << *I << " may read or write global state; not propagating\n");
	    }
	    else {
	      LPDEBUG("User " << *I << " has all-constant arguments, but couldn't be constant folded" << "\n");
	    }
	    continue;
	  }
	  tryGetImprovementBenefit(I, make_vc(newConst, 0));
	}

      }

    }
  }

}

void HypotheticalConstantFolder::getImprovementBenefit(Value* ArgV, ValCtx ArgC) {

  debugIndent += 2;
  realGetImprovementBenefit(ArgV, ArgC);
  debugIndent -= 2;

}

void HypotheticalConstantFolder::tryGetImprovementBenefit(Value* ArgV, ValCtx ArgC, bool force) {

  if(!force) {
    if(getReplacement(ArgV) != make_vc(ArgV, 0)) {
      LPDEBUG(*ArgV << " already constant\n");
      return;
    }
  }

  if(Instruction* ArgI = dyn_cast<Instruction>(ArgV)) {
  
    if(ArgI && parent.shouldIgnoreBlockForConstProp(ArgI->getParent())) { 
      LPDEBUG(*ArgI << " block not under consideration, ignoring\n");
      return;
    }

  }

  getImprovementBenefit(ArgV, ArgC);

}

bool HypotheticalConstantFolder::collectDeadBlocks() {

  bool anyImprovements = false;
  bool improvedThisTime = true;

  while(improvedThisTime) {

    improvedThisTime = false;

    LPDEBUG("Collecting dead BBs...\n");

    SmallSet<BasicBlock*, 8> LiveBlocks;
    SmallVector<BasicBlock*, 4> BlockWL;

    BlockWL.push_back(parent.getEntryBlock());

    while(BlockWL.size()) {

      SmallVector<BasicBlock*, 4> BBs = BlockWL;
      BlockWL.clear();

      for(SmallVector<BasicBlock*, 4>::iterator BI = BBs.begin(), BE = BBs.end(); BI != BE; ++BI) {

	BasicBlock* BB = *BI;

	if(LiveBlocks.insert(BB))
	  for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
	    if(!parent.edgeIsDead(BB, *SI))
	      BlockWL.push_back(*SI);
	  }

      }

    }

    SmallVector<BasicBlock*, 4> NewlyDeadBlocks;

    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

      BasicBlock* BB = FI;

      if(parent.shouldIgnoreBlockForDCE(BB))
	continue;

      if(!LiveBlocks.count(BB)) {
	if(!parent.blockIsDead(BB)) {
	  improvedThisTime = true;
	  anyImprovements = true;
	  LPDEBUG("Block " << BB->getName() << " killed\n");
	  parent.setBlockDead(BB);
	  NewlyDeadBlocks.push_back(BB);
	}
      }

    }

    for(SmallVector<BasicBlock*, 4>::iterator BI = NewlyDeadBlocks.begin(), BE = NewlyDeadBlocks.end(); BI != BE; ++BI) {

      BasicBlock* BB = *BI;

      for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
	BasicBlock* SuccBB = *SI;
	getRemoveBlockPredBenefit(SuccBB, BB);
      }

    }

  }

  return anyImprovements;

}

bool HypotheticalConstantFolder::improvePHINodes() {

  SmallVector<BasicBlock*, 4> CheckBlocks = BlocksImproved;
  BlocksImproved.clear();

  for(SmallVector<BasicBlock*, 4>::iterator BI = CheckBlocks.begin(), BE = CheckBlocks.end(); BI != BE; ++BI) {

    BasicBlock* BB = *BI;

    if(!parent.blockIsDead(BB)) {
      // See if any of our PHI nodes are now defined
      for(BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E && isa<PHINode>(*I); ++I) {
	PHINode* PN = cast<PHINode>(I);
	getPHINodeBenefit(PN);
      }
    }

  }

  return CheckBlocks.size() > 0;

}

bool HypotheticalConstantFolder::improveLoadInsts() {

  bool improvedThisTime = true;
  bool anyImprovements = false;

  LPDEBUG("Considering store-to-load forwards...\n");

  while(improvedThisTime) {

    improvedThisTime = false;

    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

      BasicBlock* BB = FI;

      if(parent.shouldIgnoreBlockForConstProp(BB))
	continue;

      if(parent.blockIsDead(BB))
	continue;

      for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; II++) {

	if(LoadInst* LI = dyn_cast<LoadInst>(II)) {

	  ValCtx Repl = getReplacement(LI);

	  if(Repl.first != LI || Repl.second > 0) {
	    LPDEBUG("Ignoring " << *LI << " because it's already improved\n");
	    continue;
	  }
	  else {
	    ValCtx Result = parent.tryForwardLoad(LI);
	    if(Result.first) {
	      tryGetImprovementBenefit(LI, Result);
	      anyImprovements = true;
	      improvedThisTime = true;
	    }
	  }

	}

      }

    }

    if(improvedThisTime) {
      LPDEBUG("At least one load was improved; trying again\n");
    }
    else {
      LPDEBUG("No loads were made constant\n");
    }

  }

  return anyImprovements;

}

void HypotheticalConstantFolder::getBenefit(Value* V, ValCtx Replacement) {

  getImprovementBenefit(V, Replacement);

  bool anyImprovements = true;

  while(anyImprovements) {

    anyImprovements = false;
    
    anyImprovements |= collectDeadBlocks();
    anyImprovements |= improvePHINodes();
    anyImprovements |= improveLoadInsts();

  }
  
}

void HypotheticalConstantFolder::killEdge(BasicBlock* B1, BasicBlock* B2) {

  getRemoveBlockPredBenefit(B2, B1);

}

namespace llvm { 

  raw_ostream& operator<<(raw_ostream& Stream, const ValCtx& VC) {

    if(!VC.first)
      Stream << "NULL";
    else if(isa<Constant>(VC.first) || !VC.second)
      Stream << *VC.first;
    else
      Stream << *VC.first << "@" << VC.second;

    return Stream;

  }

  raw_ostream& operator<<(raw_ostream& Stream, const MemDepResult& MDR) {

    if(MDR.isNonLocal()) {
      Stream << "NonLocal";
    }
    else {
      if(MDR.isClobber()) {
	Stream << "Clobber(";
      }
      else if(MDR.isDef()) {
	Stream << "Def(";
      }
      Stream << *MDR.getInst() << ")";
    }

    return Stream;

  }

}

void SymThunk::describe(raw_ostream& OS) {
  
  OS << RealVal;

}

void SymGEP::describe(raw_ostream& OS) {
  OS << "GEP(";
  for(SmallVector<Value*, 4>::iterator OI = Offsets.begin(), OE = Offsets.end(); OI != OE; OI++) {
    if(OI != Offsets.begin())
      OS << ", ";
    OS << **OI;
  }
  OS << ")";
}

void SymCast::describe(raw_ostream& OS) {
  OS << "Cast(" << *ToType << ")";
}
