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

std::pair<Value*, int> HypotheticalConstantFolder::getReplacement(const Value* V) {

  return parent.getReplacement(std::make_pair(V, 0));

}

Constant* HypotheticalConstantFolder::getConstReplacement(const Value* V) {

  if(Constant* C = dyn_cast<Constant>(V))
    return C;
  else
    return dyn_cast<Constant>(getReplacement(V).first);

}

bool HypotheticalConstantFolder::blockIsDead(BasicBlock* BB) {

  if(&(BB->getParent()->getEntryBlock()) == BB)
    return false;

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; PI++) {
      
    if(!parent.edgeIsDead(*PI, BB))
      return false;

  }

  return true;

}

void HypotheticalConstantFolder::realGetRemoveBlockPredBenefit(BasicBlock* BB, BasicBlock* BBPred) {

  LPDEBUG("Getting benefit due elimination of predecessor " << BBPred->getName() << " from BB " << BB->getName() << "\n");

  parent.setEdgeDead(BBPred, BB);

  if(parent.shouldIgnoreBlock(BB)) {
    LPDEBUG(BB->getName() << " not under consideration" << "\n");
    return;
  }

  if(blockIsDead(BB, ignoreEdges)) {
    // This BB is dead! Kill its instructions, then remove it as a predecessor to all successor blocks and see if that helps anything.
    LPDEBUG("Block is dead; killing successor edges\n");
    for(succ_iterator SI = succ_begin(BB), SE = succ_end(BB); SI != SE; ++SI) {
      getRemoveBlockPredBenefit(*SI, BB);
    }
  }
  else {
    // See if any of our PHI nodes are now defined
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

  LPDEBUG("Checking if PHI " << *PN << " is improved" << "\n");

  BasicBlock* BB = PN->getParent();
  std::pair<Value*, int> onlyValue = 0;
  bool improved = false;

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {

    if(parent.edgeIsDead(*PI, BB))
      continue;

    std::pair<Value*, int> oldValue = std::make_pair(PN->getIncomingValueForBlock(*PI), 0);
    std::pair<Value*, int> predValue = getReplacement(oldValue);
    if(oldValue != predValue)
      improved = true;
    if(!onlyValue)
      onlyValue = predValue;
    else if(onlyValue != predValue) {
      onlyValue = 0;
      break;
    }

  }
  if(onlyValue) {
    if(getReplacement(PN) == onlyValue) {
      LPDEBUG("Already improved");
      return;
    }
    else {
      LPDEBUG("Improved to " << *onlyValue << "\n");
      getImprovementBenefit(PN, onlyValue, true);
    }
  }
  else {
    LPDEBUG("Not improved\n");
    return;
  }

}

void HypotheticalConstantFolder::realGetImprovementBenefit(Value* ArgV /* Local */, std::pair<Value*, int> Replacement, bool force) {

  Instruction* ArgI = dyn_cast<Instruction>(ArgV);

  if(ArgI && parent.shouldIgnoreBlock(ArgI->getParent())) { 
    LPDEBUG(*ArgI << " not under consideration, ignoring\n");
    return;
  }

  if(!force) {
    if(getReplacement(ArgV) != std::make_pair(ArgV, 0)) {
      LPDEBUG(*ArgV << " already constant\n");
      return;
    }
  }

  parent.setReplacement(ArgV, Replacement);

  LPDEBUG("Getting benefit due to value " << *ArgV << " having improved value " << Replacement << "\n");

  for (Value::use_iterator UI = ArgV->use_begin(), E = ArgV->use_end(); UI != E;++UI){

    Instruction* I;
    if(!(I = dyn_cast<Instruction>(*UI))) {
      LPDEBUG("Instruction has a non-instruction user: " << *UI << "\n");
      continue;
    }

    if(blockIsDead(I->getParent())) {
      LPDEBUG("User instruction " << *I << " already eliminated (in dead block)\n");
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

      if((PHINode* PN = dyn_cast<PHINode>(I))) {
	// PHI nodes are special because of their BB arguments, and the special-case "constant folding" that affects them
	getPHINodeBenefit(PN);
      }
      else if(SelectInst* SI = dyn_cast<SelectInst>(I)) {
        Constant* Cond = getConstReplacement(SI->getCondition());
	if(Cond) {
	  std::pair<Value*, int> newVal;
	  if(cast<ConstantInt>(Cond)->isZero())
	    newVal = std::make_pair(SI->getFalseValue(), 0);
	  else
	    newVal = std::make_pair(SI->getTrueValue(), 0);
	  if(getReplacement(SI) != newVal)
	    getImprovementBenefit(SI, newVal);
	}
      }
      else {

	SmallVector<Constant*, 4> instOperands;

	bool someArgumentUnknownConstant = false;

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
	      continue;
	    }
	    else {
	      LPDEBUG("User " << *I << " has all-constant arguments, but couldn't be constant folded" << "\n");
	    }
	  }
	  getImprovementBenefit(I, std::make_pair(newConst, 0));
	}

      }

    }
  }

}

void HypotheticalConstantFolder::getImprovementBenefit(Value* ArgV, std::pair<Value*, int> ArgC, bool force = false) {

  debugIndent += 2;
  realGetImprovementBenefit(ArgV, ArgC, force);
  debugIndent -= 2;

}

// Returns true if V is a useful value to forward from a store to a load.
// Useful values are:
// 1) Constants
// 2) Pointers to a known object

bool shouldForwardValue(Value* V) {

  if(isa<Constant>(V))
    return true;

  if(V->getType()->isPointerTy()) {
    
    int frame = 0;
    while(1) {
      Value* O = V->getUnderlyingObject();
      if(isIdentifiedObject(O) || isa<Constant>(O))
	return true;
      std::pair<Value*, int> NewV = parent.getReplacement(O, frame);
      if(NewV.first == V && NewV.second == frame)
	break;
      frame = NewV.second;
      V = NewV.first;
    }

    return false;

  }

  return false;

}

bool HypotheticalConstantFolder::tryForwardLoad(LoadInst* LI, const MemDepResult& Res) {

  if(StoreInst* SI = dyn_cast<StoreInst>(Res.getInst())) {
    if(shouldForwardValue(SI->getOperand(0))) {

      LPDEBUG(*LI << " defined by " << *SI << "\n");
      getImprovementBenefit(LI, SC);
      return true;

    }
    else {
      LPDEBUG(*LI << " is defined by " << *SI << " with a non-constant operand\n");
    }
  }
  else if(LoadInst* DefLI = dyn_cast<LoadInst>(Res.getInst())) {
		
    Value* improvedLoad = getReplacement(DefLI);
    if(improvedLoad != DefLI) {
      LPDEBUG(*LI << " defined by " << *(DefLIIt->second) << "\n");
      getImprovementBenefit(LI, improvedLoad);
      return true;
    }

  }
  else {
    LPDEBUG(*LI << " is defined by " << *(Res.getInst()) << " which is not a simple load or store\n");
  }

  return false;

}

bool HypotheticalConstantFolder::tryForwardLoadFromParent(LoadInst* LI) {

  // Precondition: LI is clobbered in exactly one place: the entry instruction to its parent function.
  // This might mean that instruction actually clobbers it, or it's defined by instructions outside this function.
  // If there's a chance it's the latter, ask our parent to see if it knows anything about out parent
  // That is, if our parent is InlineHeuristics.
  
  Value* Ptr = LI->getPointerOperand();

  LPDEBUG("Trying to resolve load from " << *LI << " by exploring callers\n");

  // Check that we're trying to fetch a cast-of-constGEP-of-cast-of... an argument or an outer object,
  // and construct a symbolic expression to pass to our parent as we go.

  SmallVector<SymExpr*, 4> Expr;

  while(1) {

    if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
      SmallVector<Value*, 4> idxs;
      for (unsigned i = 1, e = GEP->getNumOperands(); i != e; ++i) {
	Value* idx = GEP->getOperand(i);
	DenseMap<Value*, Value*>::iterator it;
	if(ConstantInt* CI = dyn_cast<ConstantInt>(idx)) {
	  idxs.push_back(CI);
	}
	else if((it = improvedValues.find(idx)) != improvedValues.end()) {
	  idxs.push_back(cast<ConstantInt>(it->second));
	}
	else {
	  LPDEBUG("Can't investigate external dep with non-const index " << *idx << "\n");
	  return false;
	}
      }
      Expr.push_back(new SymGEP(idxs));
      Ptr = GEP->getPointerOperand();
    }
    else if(BitCastInst* C = dyn_cast<BitCastInst>(Ptr)) {
      Expr.push_back(new SymCast(C->getType()));
      Ptr = C->getOperand(0);
    }
    else if(Argument* A = dyn_cast<Argument>(Ptr)) {
      Expr.push_back(new SymThunk(A));
      break;
    }
    else if(PHINode* PI = dyn_cast<PHINode>(Ptr)) {
      Value* uniquePred = 0;
      unsigned livePreds = 0;
      for(unsigned i = 0; i < PI->getNumIncomingValues() && livePreds < 2; i++) {
	if(!blockIsDead(PI->getIncomingBlock(i), ignoreEdges)) {
	  livePreds++;
	  uniquePred = PI->getIncomingValue(i);
	}
      }
      if(livePreds == 0) {
	LPDEBUG("Anomaly! In trying to forward load from parent for " << *LI << " found a PHINode " << *PI << " with no live preds!\n");
      }
      else if(livePreds == 1) {
	Ptr = uniquePred;
      }
      else {
	LPDEBUG("Won't investigate load from parent function due to ambiguous PHI " << *PI << "\n");
	return false;
      }
    }
    else if(SelectInst* SI = dyn_cast<SelectInst>(Ptr)) {
      Value* Cond = SI->getCondition();
      DenseMap<Value*, Value*>::iterator it;
      if((it = improvedValues.find(Cond)) != improvedValues.end()) {
	ConstantInt* CCond = cast<ConstantInt>(Cond);
	if(CCond->isZero())
	  Ptr = SI->getFalseValue();
	else
	  Ptr = SI->getTrueValue();
      }
      else {
	LPDEBUG("Won't investigate load from parent function due to unresolved Select " << *SI << "\n");
	return false;
      }
    }
    else {
      LPDEBUG("Won't investigate load from parent function due to unhandled instruction " << *Ptr << "\n");
      return false;
    }
    
  }

  // If we make it here, we have a series of friendly cast and GEP ops that end up at an argument.
  // Ask our parent to figure out what's going on!

  LPDEBUG("Will resolve ");

  for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
    if(it != Expr.begin())
      DEBUG(dbgs() << " of ");
    DEBUG((*it)->describe(dbgs()));
  }

  DEBUG(dbgs() << "\n");
  
  SmallVector<SymExpr*, 4> resultExpr;
  parent.tryResolveInParentContext(Expr, resultExpr);

  if(resultExpr.size()) {
    LPDEBUG("Resolved to ");
    for(SmallVector<SymExpr*, 4>::iterator it = resultExpr.begin(), it2 = resultExpr.end(); it != it2; it++) {
      if(it != resultExpr.begin())
	DEBUG(dbgs() << " of ");
      DEBUG((*it)->describe(dbgs()));      
    }
    DEBUG(dbgs() << "\n");
    if(isa<SymOuter>(resultExpr[0]))
      outerValues[LI] = resultExpr;
    else {
      assert(resultExpr.size() == 1);
      Constant* C = cast<Constant>(cast<SymThunk>(resultExpr[0])->RealVal);
      getConstantBenefit(LI, C);
    }
  }

  for(SmallVector<SymExpr*, 4>::iterator it = Expr.begin(), it2 = Expr.end(); it != it2; it++) {
    delete (*it);
  }

  return (resultExpr.size() != 0);

}

void HypotheticalConstantFolder::getBenefit(const SmallVector<std::pair<Value*, Value*>, 4>& roots) {

  for(SmallVector<std::pair<Value*, Value*>, 4>::const_iterator RI = roots.begin(), RE = roots.end(); RI != RE; RI++) {

    getConstantBenefit(RI->first, RI->second);

  }

  bool anyStoreForwardingBenefits = true;

  while(anyStoreForwardingBenefits) {

    LPDEBUG("Considering store-to-load forwards...\n");
    anyStoreForwardingBenefits = false;

    MemoryDependenceAnalyser MD;
    MD.init(AA, &this.parent);

    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; FI++) {

      BasicBlock* BB = FI;

      if(parent.shouldIgnoreBlock(BB))
	continue;

      if(blockIsDead(BB, ignoreEdges))
	continue;

      for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; II++) {

	if(LoadInst* LI = dyn_cast<LoadInst>(II)) {

	  DenseMap<Value*, Value*>::iterator it = improvedValues.find(LI);

	  if(it != improvedValues.end()) {
	    LPDEBUG("Ignoring " << *LI << " because it's already constant\n");
	    continue;
	  }

	  if(outerValues.find(LI) != outerValues.end()) {
	    LPDEBUG(*LI << " result already resolved to an outer value\n");
	    continue;
	  }

	  MemDepResult Res = MD.getDependency(LI, improvedValues, ignoreEdges);

	  if(Res.isClobber()) {
	    LPDEBUG(*LI << " is locally clobbered by " << Res.getInst() << "\n");
	    if(BB == &F->getEntryBlock()) {
	      BasicBlock::iterator TestII(Res.getInst());
	      if(TestII == BB->begin()) {
		anyStoreForwardingBenefits |= tryForwardLoadFromParent(LI);
	      }
	    }
	  }
	  else if(Res.isDef()) {
	    anyStoreForwardingBenefits |= tryForwardLoad(LI, Res);
	  }
	  else { // Nonlocal
	      
	    Value* LPointer = LI->getOperand(0);

	    if(Instruction* LPointerI = dyn_cast<Instruction>(LPointer)) {
	      DenseMap<Value*, Value*>::iterator it = improvedValues.find(LPointerI);
	      if(it != improvedValues.end())
		LPointer = it->second;
	    }

	    SmallVector<NonLocalDepResult, 4> NLResults;

	    MD.getNonLocalPointerDependency(LPointer, true, BB, NLResults, improvedValues, ignoreEdges);

	    assert(NLResults.size() > 0);

	    const MemDepResult* TheResult = 0;
	    const NonLocalDepResult* TheClobber = 0;
	    bool seenClobber = false;
	      
	    for(unsigned int i = 0; i < NLResults.size(); i++) {
		
	      const MemDepResult& Res = NLResults[i].getResult();
	      if(Res.isNonLocal())
		continue;
	      else if(Res.isClobber()) {
		LPDEBUG(*LI << " is nonlocally clobbered by " << *(Res.getInst()) << "\n");
		if(!seenClobber) {
		  TheClobber = &NLResults[i];
		}
		else {
		  TheClobber = 0;
		}
		seenClobber = true;
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

	    if((!seenClobber) && TheResult)
	      anyStoreForwardingBenefits |= tryForwardLoad(LI, *TheResult);
	    else if(TheClobber) {
	      BasicBlock* clobberBlock = TheClobber->getBB();
	      if(&clobberBlock->getParent()->getEntryBlock() == clobberBlock) {
		BasicBlock::iterator TestBBI(TheClobber->getResult().getInst());
		if(TestBBI == clobberBlock->begin()) {
		  anyStoreForwardingBenefits |= tryForwardLoadFromParent(LI);
		}
	      }
	    }

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

void SymThunk::describe(raw_ostream& OS) {
  OS << *RealVal;
}

void SymOuter::describe(raw_ostream& OS) {
  OS << "Outer expression";
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
