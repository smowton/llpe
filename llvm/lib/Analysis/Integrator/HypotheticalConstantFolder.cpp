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
#include "llvm/IntrinsicInst.h"
#include "llvm/BasicBlock.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h" // For isIdentifiedObject
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
// For elaboration of Calculate et al in Dominators.h:
#include "llvm/Analysis/DominatorInternals.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include "PostDoms.h"

#include <string>

using namespace llvm;

namespace llvm {

  std::string ind(int i) {

    char* arr = (char*)alloca(i+1);
    for(int j = 0; j < i; j++)
      arr[j] = ' ';
    arr[i] = '\0';
    return std::string(arr);

  }

  const Loop* immediateChildLoop(const Loop* Parent, const Loop* Child) {

    // Doh, this makes walking the tree o' loops n^2. Oh well.
    const Loop* immediateChild = Child;
    while(immediateChild->getParentLoop() != Parent)
      immediateChild = immediateChild->getParentLoop();
    return immediateChild;

  }

}

bool IntegrationAttempt::openCallSucceeds(Value* V) {

  return forwardableOpenCalls[cast<CallInst>(V)]->success;

}

bool IntegrationAttempt::isForwardableOpenCall(Value* V) {

  if(CallInst* CI = dyn_cast<CallInst>(V))
    return forwardableOpenCalls.count(CI);
  else
    return false;

}

bool IntegrationAttempt::shouldForwardValue(ValCtx V) {

  if(isa<Constant>(V.first))
    return true;

  if(V.isPtrAsInt())
    return true;

  if(V.isVaArg())
    return true;
  
  if(V.first->getType()->isPointerTy()) {
    
    ValCtx O = V.second->getUltimateUnderlyingObject(V.first);
    // Reject forwarding expressions based on constant pointers because this means we're something like %1 in:
    // %0 = (some pointer-typed expression that resolves to a constant (so either null or a constexpr of a global))
    // %1 = cast or gep of %0, ...
    // This means %1 will evaluate to a constexpr; we should reconsider at that time.
    if(isGlobalIdentifiedObject(O) && !isa<Constant>(O.first))
      return true;

  }

  if(V.second->isForwardableOpenCall(V.first))
    return true;

  return false;

}

bool IntegrationAttempt::checkLoopSpecialEdge(BasicBlock* FromBB, BasicBlock* ToBB) {

  // Check for a loop header being entered for the first time (i.e., a child loop should perhaps be expanded?)
  const Loop* L = getBlockScopeVariant(ToBB);

  if(!L)
    return false;

  bool isSpecialEdge = (ToBB == L->getHeader()) && (FromBB == L->getLoopPreheader());

  if(isSpecialEdge) {
    // I *think* this is necessarily an immediate child of this loop.

    if(!getPeelAttempt(L)) {

      if(edgeIsDead(FromBB, ToBB)) {

	LPDEBUG("Loop header " << ToBB->getName() << " killed. Marking exit edges dead, and successors for consideration.\n");

	for(Loop::block_iterator BI = L->block_begin(), BE = L->block_end(); BI != BE; ++BI) {

	  deadBlocks.insert(*BI);

	} 

	SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4> exitEdges;

	L->getExitEdges(exitEdges);

	for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 4>::iterator it = exitEdges.begin(), endit = exitEdges.end(); it != endit; ++it) {

	  /*
	  const Loop* edgeScope = getEdgeScope(it->first, it->second);
	  if(edgeScope == getLoopContext() || L->contains(edgeScope)) {
	    // The edge is either invariant at our scope, or ordinarily a loop variant
	    // Use contains(edgeScope) rather than L == edgeScope to catch edges which break
	    // out of more than one loop.
	    LPDEBUG("Killed edge to " << it->second->getName() << "\n");
	    deadEdges.insert(*it);
	  }
	  else {
	    LPDEBUG("Ignored edge to " << it->second->getName() << " (invariant)\n");
	  }
	  */

	  deadEdges.insert(*it);

	}

      }

    }

  }

  return isSpecialEdge;

}

bool PeelAttempt::allNonFinalIterationsDoNotExit() {

  for(unsigned i = 0; i < Iterations.size() - 1; ++i) {

    if(!Iterations[i]->allExitEdgesDead())
      return false;

  }

  return true;

}

bool PeelIteration::isOnlyExitingIteration() {

  if(iterStatus != IterationStatusFinal)
    return false;

  if(!parentPA->OptimisticEdge.first)
    return true;

  return parentPA->allNonFinalIterationsDoNotExit();

}

void IntegrationAttempt::markBlockCertain(ShadowBBInvar* BB) {

  LPDEBUG("Block " << BB->getName() << " is certain to execute\n");
  if(!BBs[BB->idx])
    createBB(BB->idx);
  BB->status = BBSTATUS_CERTAIN;
    
}

void IntegrationAttempt::markBlockAssumed(ShadowBBInvar* BB) {

  if(!BBs[BB->idx])
    createBB(BB->idx);
  BB->status = BBSTATUS_ASSUMED;

}

PostDominatorTree* IntegrationHeuristicsPass::getPostDomTree(Function* F) {

  DenseMap<Function*, PostDominatorTree*>::iterator it = PDTs.find(F);
  if(it != PDTs.end())
    return it->second;
  else {

    PostDominatorTree* PDT = new PostDominatorTree();
    PDT->runOnFunction(*F);
    PDTs[F] = PDT;
    return PDT;

  }

}

PostDominatorTree* IntegrationAttempt::getPostDomTree() {

  return pass->getPostDomTree(&F);

}

// specialise WriteAsOperand to allow printing of our special DomTree's BBWrapper nodes:
namespace llvm {

  void WriteAsOperand(raw_ostream& os, const BBWrapper* BBW, bool ign) {

    if(BBW->BB) {
      WriteAsOperand(os, BBW->BB, ign);
    }
    else {
      os << "<<next iteration>>";
    }

  }

}

DomTreeNodeBase<const BBWrapper>* IntegrationHeuristicsPass::getPostDomTreeNode(const Loop* L, BasicBlock* BB) {

  std::pair<const LoopWrapper*, DominatorTreeBase<const BBWrapper>*> P;

  DenseMap<const Loop*, std::pair<const LoopWrapper*, DominatorTreeBase<const BBWrapper>*> >::iterator it = LoopPDTs.find(L);
  if(it != LoopPDTs.end()) {

    P = it->second;

  }
  else {
    
    const LoopWrapper* LW = new LoopWrapper(L);
    DominatorTreeBase <const BBWrapper>* LPDT = new DominatorTreeBase<const BBWrapper>(true);
    LPDT->recalculate(*LW);

    /*
    DEBUG(dbgs() << "Calculated postdom tree for loop " << (L->getHeader()->getName()) << ":\n");
    DEBUG(LPDT->print(dbgs()));
    */

    LoopPDTs[L] = P = std::make_pair(LW, LPDT);

  }

  DenseMap<const BasicBlock*, BBWrapper>::const_iterator it2 = P.first->Map.find(BB);
  if(it2 == P.first->Map.end())
    return 0;
  else  
    return P.second->getNode(&it2->second);

}

bool InlineAttempt::isOptimisticPeel() {
  
  return false;

}

bool PeelIteration::isOptimisticPeel() {

  return !!(parentPA->OptimisticEdge.first);

}

void PeelAttempt::eraseBlockValues(BasicBlock* BB) {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->eraseBlockValues(BB);

}

void IntegrationAttempt::markContextDead() {

  contextIsDead = true;

   for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

     it->second->markContextDead();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->markContextDead();

  }


}

void IntegrationAttempt::eraseBlockValues(BasicBlock* BB) {

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {
    
    improvedValues.erase(BI);
    // This can happen when calls are always-inlined.
    // Cowardly non-deletion here, TODO delete it and deal with the fallout.
    if(CallInst* CI = dyn_cast<CallInst>(BI)) {
      if(InlineAttempt* IA = getInlineAttempt(CI))
	IA->markContextDead();
      inlineChildren.erase(CI);
    }
    
  }
  
  const Loop* L = getBlockScopeVariant(BB);
  const Loop* MyL = getLoopContext();
  if(L != MyL) {

    const Loop* ChildL = immediateChildLoop(MyL, L);
    if(PeelAttempt* PA = getPeelAttempt(ChildL))
      PA->eraseBlockValues(BB);

  }

}

bool InlineAttempt::entryBlockIsCertain() {

  if(!parent)
    return true;
  return parent->blockCertainlyExecutes(CIBB);

}

bool PeelIteration::entryBlockIsCertain() {

  if(iterationCount == 0)
    return parent->blockCertainlyExecutes(parentPA->preheaderBB);

  // Otherwise it's certain if we're certain to iterate and at least the previous header was certain.
  PeelIteration* prevIter = parentPA->Iterations[iterationCount - 1];
  return prevIter->blockCertainlyExecutes(parentPA->latchIdx) && prevIter->allExitEdgesDead();

}

bool InlineAttempt::entryBlockAssumed() {

  if(!parent)
    return true;
  return parent->blockAssumed(CI->getParent());

}

bool PeelIteration::entryBlockAssumed() {

  // Having been entered at all currently signifies at least the assumption that we will run.
  return true;

}

// Create the ShadowBB structure for the given block index.
void IntegrationAttempt::createBB(uint32_t blockIdx) {

  release_assert((!BBs[blockIdx]) && "Creating block for the second time");
  ShadowBB* newBB = new ShadowBB();
  newBB->invar = invarInfo->BBs[blockIdx];
  newBB->succsAlive = new bool[newBB->invar->predIdxs.size()];
  for(unsigned i = 0, ilim = newBB->invar->predIdxs.size(); i != ilim; ++i)
    newBB->succsAlive[i] = true;
  newBB->status = BBSTATUS_UNKNOWN;

}

void IntegrationAttempt::checkBlock(uint32_t blockIdx) {

  const ShadowBBInvar& SBBI = invarInfo->BBs[blockIdx];
  BasicBlock* BB = SBBI.BB;

  LPDEBUG("Checking status of block " << BB->getName() << "\n");

  if(getBB(blockIdx)) {
    DEBUG(dbgs() << "Status already known\n");
    return;
  }

  // Check whether this block has become dead or certain
  
  bool isDead = true;
  bool isCertain = true;
  bool isAssumed = true;

  if(BB == getEntryBlock()) {

    isCertain = entryBlockIsCertain();
    isAssumed = isCertain || entryBlockAssumed();
    isDead = false;

  }
  else {

    for(unsigned i = 0, ilim = SBBI.predIdxs.size(); i < ilim; ++i) {

      const ShadowBBInvar& PSBBI = invarInfo->BBs[SBBI.predIdxs[i]];

      if(!edgeIsDead(PSBBI, SBBI)) {

	isDead = false;

	bool PICertain = blockCertainlyExecutes(PSBBI);
	if(!PICertain)
	  isCertain = false;

	bool PIAssumed = PICertain || blockAssumed(*PI);

	if(PIAssumed) {

	  bool onlySuccessor = true;

	  for(uint32_t j = 0, jlim = PSBBI.succIdxs.size(); j != jlim; ++j) {

	    const ShadowBBInvar& SSBBI = invarInfo->BBs[PSBBI.succIdxs[j]];

	    if(SBBI.BB != SSBBI.BB && !edgeIsDead(PSBBI, SSBBI)) {
	      onlySuccessor = false;
	      break;
	    }

	  }

	  if(!onlySuccessor) {
	    isCertain = false;
	    if(!shouldAssumeEdge(PSBBI.BB, SBBI.BB))
	      isAssumed = false;
	  }

	}
	else {

	  isCertain = false;
	  isAssumed = false;

	}

      }

    }

  }

  if(isDead && (isCertain || isAssumed)) {
    isCertain = false;
    isAssumed = false;
  }

  if(isDead) {

    // Block is implied dead as we do not create a BB structure for it at this point.
    return;

  }
  else if(isCertain || isAssumed) {

    const Loop* MyL = L;

    for(DomTreeNodeBase<const BBWrapper>* DTN = pass->getPostDomTreeNode(MyL, BB); DTN && DTN->getBlock(); DTN = DTN->getIDom()) {
	
      const BBWrapper* BW = DTN->getBlock();
      if(BW->BB) {
	  
	const Loop* BBL = const_cast<ShadowBBInvar*>(BW->BB)->scope;
	if(BBL == MyL) {

	  if(isCertain)
	    markBlockCertain(const_cast<ShadowBBInvar*>(BW->BB));
	  else
	    markBlockAssumed(const_cast<ShadowBBInvar*>(BW->BB));

	}

      }

    }

  }
  else {

    createBB(SBBI.idx);

  }

}

bool IntegrationAttempt::getLoopHeaderPHIValue(PHINode* PN, ValCtx& result) {

  return false;

}

bool PeelIteration::getLoopHeaderPHIValue(PHINode* PN, ValCtx& result) {

  bool isHeaderPHI = PN->getParent() == L->getHeader();

  if(isHeaderPHI) {

    if(iterationCount == 0) {

      LPDEBUG("Pulling PHI value from preheader\n");
      result = parent->getReplacement(PN->getIncomingValueForBlock(L->getLoopPreheader()));

    }
    else {

      LPDEBUG("Pulling PHI value from previous iteration latch\n");
      PeelIteration* PreviousIter = parentPA->getIteration(iterationCount - 1);
      result = PreviousIter->getReplacement(PN->getIncomingValueForBlock(L->getLoopLatch()));

    }

  }

  return isHeaderPHI;

}

ValCtx IntegrationAttempt::getPHINodeValue(PHINode* PN) {

  BasicBlock* BB = PN->getParent();
  ValCtx onlyValue = VCNull;

  if(!getLoopHeaderPHIValue(PN, onlyValue)) {

    LPDEBUG("Trying to evaluate PHI " << itcache(*PN) << " by standard means\n");
    const Loop* phiLoop = getValueScope(PN);
      
    for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI) {
      
      if(edgeIsDead(*PI, BB))
	continue;

      Value* oldValue = PN->getIncomingValueForBlock(*PI);
      ValCtx predValue;

      const Loop* predLoop = getValueScope(oldValue);
      // If the predecessor comes from a descendent of the PHI's loop
      if(((!phiLoop) && predLoop) || (phiLoop && !predLoop->contains(phiLoop))) {

	predValue = getReplacementUsingScopeRising(cast<Instruction>(oldValue), *PI, PN->getParent(), predLoop);
	if(predValue == VCNull) {
	  onlyValue = VCNull;
	  break;
	}

      }
      else {
      
	// Predecessor comes from the same scope or a parent; getReplacement handles both cases
	predValue = getReplacement(oldValue);

      }

      if(onlyValue == VCNull)
	onlyValue = predValue;
      else if(onlyValue != predValue) {
	onlyValue = VCNull;
	break;
      }
      
    }
    
  }

  if(onlyValue.first && shouldForwardValue(onlyValue)) {
    LPDEBUG("Improved to " << itcache(onlyValue) << "\n");
    return onlyValue;
  }
  else {
    LPDEBUG("Not improved\n");
    return VCNull;
  }
  
}

ValCtx IntegrationAttempt::tryFoldOpenCmp(CmpInst* CmpI, ConstantInt* CmpInt, bool flip) {

  if(CmpInt->getBitWidth() > 64) {
    LPDEBUG("Using an int wider than int64 for an FD\n");
    return VCNull;
  }

  CmpInst::Predicate Pred = CmpI->getPredicate();

  if(flip) {

    switch(Pred) {
    case CmpInst::ICMP_SGT:
      Pred = CmpInst::ICMP_SLT;
      break;
    case CmpInst::ICMP_SGE:
      Pred = CmpInst::ICMP_SLE;
      break;
    case CmpInst::ICMP_SLT:
      Pred = CmpInst::ICMP_SGT;
      break;
    case CmpInst::ICMP_SLE:
      Pred = CmpInst::ICMP_SGE;
      break;
    default:
      break;
    }

  }

  int64_t CmpVal = CmpInt->getSExtValue();

  switch(Pred) {

  case CmpInst::ICMP_EQ:
    if(CmpVal < 0)
      return const_vc(ConstantInt::getFalse(CmpI->getContext()));
    break;
  case CmpInst::ICMP_NE:
    if(CmpVal < 0)
      return const_vc(ConstantInt::getTrue(CmpI->getContext()));    
    break;
  case CmpInst::ICMP_SGT:
    if(CmpVal < 0)
      return const_vc(ConstantInt::getTrue(CmpI->getContext()));
    break;
  case CmpInst::ICMP_SGE:
    if(CmpVal <= 0)
      return const_vc(ConstantInt::getTrue(CmpI->getContext()));
    break;
  case CmpInst::ICMP_SLT:
    if(CmpVal <= 0)
      return const_vc(ConstantInt::getFalse(CmpI->getContext()));
    break;
  case CmpInst::ICMP_SLE:
    if(CmpVal < 0)
      return const_vc(ConstantInt::getFalse(CmpI->getContext()));
    break;
  default:
    LPDEBUG("Failed to fold " << itcache(*CmpI) << " because it compares a symbolic FD using an unsupported predicate\n");
    break;
  }

  return VCNull;

}

// Return true if this turned out to be a compare against open
// (and so false if there's any point trying normal const folding)
bool IntegrationAttempt::tryFoldOpenCmp(CmpInst* CmpI, ValCtx& Improved) {

  bool flip;
  bool exists;
  ConstantInt* CmpInt = 0;
  ValCtx op0 = getReplacement(CmpI->getOperand(0));
  ValCtx op1 = getReplacement(CmpI->getOperand(1));
  if(op0.second && op0.second->isForwardableOpenCall(op0.first)) {
    flip = false;
    exists = op0.second->openCallSucceeds(op0.first);
    CmpInt = dyn_cast<ConstantInt>(op1.first);
  }
  else if(op1.second && op1.second->isForwardableOpenCall(op1.first)) {
    flip = true;
    exists = op1.second->openCallSucceeds(op1.first);
    CmpInt = dyn_cast<ConstantInt>(op0.first);
  }
  else {
    return false;
  }
  if(CmpInt) {
    
    if(!exists) {

      ConstantInt *Arg0, *Arg1;
      Arg0 = ConstantInt::getSigned(CmpInt->getType(), -1);
      Arg1 = CmpInt;
      if(flip)
	std::swap(Arg0, Arg1);
      Improved = const_vc(ConstantFoldCompareInstOperands(CmpI->getPredicate(), Arg0, Arg1, TD));
      return true;

    }
    else {

      Improved = tryFoldOpenCmp(CmpI, CmpInt, flip);
      if(Improved.first) {
	LPDEBUG("Comparison against file descriptor resolves to " << itcache(*Improved.first) << "\n");
      }
      else {
	LPDEBUG("Comparison against file descriptor inconclusive\n");
      }

    }

  }

  return true;

}

static unsigned getSignedPred(unsigned Pred) {

  switch(Pred) {
  default:
    return Pred;
  case CmpInst::ICMP_UGT:
    return CmpInst::ICMP_SGT;
  case CmpInst::ICMP_UGE:
    return CmpInst::ICMP_SGE;
  case CmpInst::ICMP_ULT:
    return CmpInst::ICMP_SLT;
  case CmpInst::ICMP_ULE:
    return CmpInst::ICMP_SLE;
  }

}

static unsigned getReversePred(unsigned Pred) {

  switch(Pred) {
   
  case CmpInst::ICMP_UGT:
    return CmpInst::ICMP_ULT;
  case CmpInst::ICMP_ULT:
    return CmpInst::ICMP_UGT;
  case CmpInst::ICMP_UGE:
    return CmpInst::ICMP_ULE;
  case CmpInst::ICMP_ULE:
    return CmpInst::ICMP_UGE;
  case CmpInst::ICMP_SGT:
    return CmpInst::ICMP_SLT;
  case CmpInst::ICMP_SLT:
    return CmpInst::ICMP_SGT;
  case CmpInst::ICMP_SGE:
    return CmpInst::ICMP_SLE;
  case CmpInst::ICMP_SLE:
    return CmpInst::ICMP_SGE;
  default:
    assert(0 && "getReversePred applied to non-integer-inequality");
    return CmpInst::BAD_ICMP_PREDICATE;

  }

}

bool IntegrationAttempt::tryFoldNonConstCmp(CmpInst* CmpI, ValCtx& Improved) {

  // Only handle integer comparison
  unsigned Pred = CmpI->getPredicate();
  if(Pred < CmpInst::FIRST_ICMP_PREDICATE || Pred > CmpInst::LAST_ICMP_PREDICATE)
    return false;

  // Only handle inequalities
  switch(Pred) {
  case CmpInst::ICMP_EQ:
  case CmpInst::ICMP_NE:
    return false;
  default:
    break;
  }

  Constant* Op0C = getConstReplacement(CmpI->getOperand(0));
  Constant* Op1C = getConstReplacement(CmpI->getOperand(1));
  ConstantInt* Op0CI = dyn_cast_or_null<ConstantInt>(Op0C);
  ConstantInt* Op1CI = dyn_cast_or_null<ConstantInt>(Op1C);

  // Only handle constant vs. nonconstant here; 2 constants is handled elsewhere.
  if((!!Op0C) == (!!Op1C))
    return false;

  if(!Op1C) {
    std::swap(Op0C, Op1C);
    std::swap(Op0CI, Op1CI);
    Pred = getReversePred(Pred);
  }

  assert(Op1C);

  // OK, we have a nonconst LHS against a const RHS.
  // Note that the operands to CmpInst must be of the same type.

  switch(Pred) {
  default:
    break;
  case CmpInst::ICMP_UGT:
    // Never u> ~0
    if(Op1CI && Op1CI->isAllOnesValue()) {
      Improved = const_vc(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_UGE:
    // Always u>= 0
    if(Op1C->isNullValue()) {
      Improved = const_vc(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_ULT:
    // Never u< 0
    if(Op1C->isNullValue()) {
      Improved = const_vc(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_ULE:
    // Always u<= ~0
    if(Op1CI && Op1CI->isAllOnesValue()) {
      Improved = const_vc(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SGT:
    // Never s> maxint
    if(Op1CI && Op1CI->isMaxValue(true)) {
      Improved = const_vc(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SGE:
    // Always s>= minint
    if(Op1CI && Op1CI->isMinValue(true)) {
      Improved = const_vc(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SLT:
    // Never s< minint
    if(Op1CI && Op1CI->isMinValue(true)) {
      Improved = const_vc(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SLE:
    // Always s<= maxint
    if(Op1CI && Op1CI->isMaxValue(true)) {
      Improved = const_vc(ConstantInt::getTrue(CmpI->getContext()));
      return true;     
    }
    break;
  }

  return false;

}

// Return value as above: true for "we've handled it" and false for "try constant folding"
bool IntegrationAttempt::tryFoldPointerCmp(CmpInst* CmpI, ValCtx& Improved) {

  // Check for special cases of pointer comparison that we can understand:

  Value* op0 = CmpI->getOperand(0);
  Value* op1 = CmpI->getOperand(1);

  // Only integer and pointer types can possibly represent pointers:
  if(!((op0->getType()->isIntegerTy() || op0->getType()->isPointerTy()) && 
       (op1->getType()->isIntegerTy() || op1->getType()->isPointerTy())))
    return false;
 
  Constant* op0C = getConstReplacement(op0);
  Constant* op1C = getConstReplacement(op1);
  int64_t op0Off = 0, op1Off = 0;
  ValCtx op0O = GetBaseWithConstantOffset(op0, this, op0Off);
  ValCtx op1O = GetBaseWithConstantOffset(op1, this, op1Off);

  // Don't check the types here because we need to accept cases like comparing a ptrtoint'd pointer
  // against an integer null. The code for case 1 works for these; all other cases require that both
  // values resolved to pointers.

  const Type* I64 = Type::getInt64Ty(CmpI->getContext());
  Constant* zero = ConstantInt::get(I64, 0);
  Constant* one = ConstantInt::get(I64, 1);
  
  // 1. Comparison between two null pointers, or a null pointer and a resolved pointer:

  Constant* op0Arg = 0, *op1Arg = 0;
  if(op0C && op0C->isNullValue())
    op0Arg = zero;
  else if(op0O.first->getType()->isPointerTy() && isGlobalIdentifiedObject(op0O))
    op0Arg = one;
  
  if(op1C && op1C->isNullValue())
    op1Arg = zero;
  else if(op1O.first->getType()->isPointerTy() && isGlobalIdentifiedObject(op1O))
    op1Arg = one;

  if(op0Arg && op1Arg && (op0Arg == zero || op1Arg == zero)) {
    
    Improved = const_vc(ConstantFoldCompareInstOperands(CmpI->getPredicate(), op0Arg, op1Arg, this->TD));
    return true;   

  }

  // Only instructions that ultimately refer to pointers from here on

  if(!(op0O.first->getType()->isPointerTy() && op1O.first->getType()->isPointerTy()))
    return false;

  // 2. Comparison of pointers with a common base:

  if(op0O.first == op1O.first && op0O.second == op1O.second) {

    // Always do a signed test here, assuming that negative indexing off a pointer won't wrap the address
    // space and end up with something large and positive.

    op0Arg = ConstantInt::get(I64, op0Off);
    op1Arg = ConstantInt::get(I64, op1Off);
    Improved = const_vc(ConstantFoldCompareInstOperands(getSignedPred(CmpI->getPredicate()), op0Arg, op1Arg, this->TD));
    return true;

  }

  // 3. Restricted comparison of pointers with a differing base: we can compare for equality only
  // as we don't know memory layout at this stage.

  if(isGlobalIdentifiedObject(op0O) && isGlobalIdentifiedObject(op1O) && op0O != op1O) {

    if(CmpI->getPredicate() == CmpInst::ICMP_EQ) {
      Improved = const_vc(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    else if(CmpI->getPredicate() == CmpInst::ICMP_NE) {
      Improved = const_vc(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }

  }

  return false;

}

ValCtx IntegrationAttempt::tryFoldPtrToInt(Instruction* PII) {

  Value* Arg = PII->getOperand(0);
  ValCtx ArgRep = getReplacement(Arg);

  // First try to knock out a trivial CE:
  if(ConstantExpr* CE = dyn_cast<ConstantExpr>(ArgRep.first)) {

    if(CE->getOpcode() == Instruction::IntToPtr) {

      return const_vc(CE->getOperand(0));

    }

  }

  if(shouldForwardValue(ArgRep)) {
   
    return make_vc(ArgRep.first, ArgRep.second, 0);

  }
  else {

    return VCNull;

  }

}

ValCtx IntegrationAttempt::tryFoldIntToPtr(Instruction* IPI) {

  Value* Arg = IPI->getOperand(0);
  ValCtx ArgRep = getReplacement(Arg);
  
  if(ArgRep.offset == 0) {

    return make_vc(ArgRep.first, ArgRep.second);

  }
  else {

    // Could do better: search for a live GEP, or accept pointer-with-offset as a value replacement everywhere,
    // expanding to GEPs as necessary at the output stage.
    return VCNull;

  }

}

static bool containsPtrAsInt(ConstantExpr* CE) {

  if(CE->getOpcode() == Instruction::PtrToInt)
    return true;

  for(unsigned i = 0; i < CE->getNumOperands(); ++i) {

    if(ConstantExpr* SubCE = dyn_cast<ConstantExpr>(CE->getOperand(i))) {      
      if(containsPtrAsInt(SubCE))
	return true;
    }

  }

  return false;

}

static ValCtx evaluatePtrAsIntCE(Constant* C) {

  ConstantExpr* CE = dyn_cast<ConstantExpr>(C);
  if(!CE)
    return const_vc(C);

  if(!containsPtrAsInt(CE))
    return const_vc(CE);

  switch(CE->getOpcode()) {

  case Instruction::PtrToInt:
    return make_vc(CE->getOperand(0), 0, 0);
  case Instruction::SExt:
  case Instruction::ZExt:
    return evaluatePtrAsIntCE(CE->getOperand(0));
  case Instruction::Add:
  case Instruction::Sub:
    {

      ValCtx Op1 = evaluatePtrAsIntCE(CE->getOperand(0));
      ValCtx Op2 = evaluatePtrAsIntCE(CE->getOperand(0));

      if(!(Op1.isPtrAsInt() || Op2.isPtrAsInt())) {

	assert(isa<Constant>(Op1.first) && isa<Constant>(Op2.first));
	if(CE->getOpcode() == Instruction::Add)
	  return const_vc(ConstantExpr::getAdd(cast<Constant>(Op1.first), cast<Constant>(Op2.first)));
	else
	  return const_vc(ConstantExpr::getSub(cast<Constant>(Op1.first), cast<Constant>(Op2.first)));

      }

      if(CE->getOpcode() == Instruction::Add) {

	if(Op2.isPtrAsInt())
	  std::swap(Op1, Op2);

	if(Op2.isPtrAsInt()) // Can't add 2 pointers
	  return const_vc(CE);

	if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.first))
	  return make_vc(Op1.first, Op1.second, Op1.offset + Op2C->getLimitedValue());
	else
	  return const_vc(CE);

      }
      else {
	
	if(Op1.isPtrAsInt()) {
	  
	  if(Op2.isPtrAsInt()) {
	    
	    if(Op1.first == Op2.first && Op1.second == Op2.second) {

	      return const_vc(ConstantInt::get(Type::getInt64Ty(CE->getContext()), Op1.offset - Op2.offset));
	      
	    }
	    // Else can't subtract 2 pointers with unknown base

	  }
	  else {

	    if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.first))
	      return make_vc(Op1.first, Op1.second, Op1.offset - Op2C->getLimitedValue());
	    else
	      return const_vc(CE);

	  }
	  
	}
	
      }

      // Fall through to default

    }	

  default:
    return const_vc(CE);

  }

}

ValCtx IntegrationAttempt::getPtrAsIntReplacement(Value* V) {

  ValCtx VC = getReplacement(V);
  if(VC.first && !VC.isPtrAsInt()) {

    if(ConstantExpr* CE = dyn_cast<ConstantExpr>(VC.first)) {

      return evaluatePtrAsIntCE(CE);

    }

  }
 
  return VC;

}

bool IntegrationAttempt::tryFoldPtrAsIntOp(Instruction* BOp, ValCtx& Improved) {

  if(BOp->getOpcode() != Instruction::Add && BOp->getOpcode() != Instruction::Sub && BOp->getOpcode() != Instruction::And)
    return false;

  ValCtx Op0 = getPtrAsIntReplacement(BOp->getOperand(0));
  ValCtx Op1 = getPtrAsIntReplacement(BOp->getOperand(1));

  bool Op0Ptr = Op0.isPtrAsInt();
  bool Op1Ptr = Op1.isPtrAsInt();

  if((!Op0Ptr) && (!Op1Ptr))
    return false;

  if(BOp->getOpcode() == Instruction::Add) {
  
    if(Op0Ptr && Op1Ptr)
      return false;

    ValCtx PtrV = Op0Ptr ? Op0 : Op1;
    ConstantInt* NumC = dyn_cast<ConstantInt>(Op0Ptr ? Op1.first : Op0.first);
    
    if(!NumC)
      return false;

    Improved = make_vc(PtrV.first, PtrV.second, PtrV.offset + NumC->getSExtValue());
    return true;

  }
  else if(BOp->getOpcode() == Instruction::Sub) {

    if(!Op0Ptr)
      return false;

    if(Op1Ptr) {

      int64_t Op0Off = 0, Op1Off = 0;
      ValCtx Op0Base = GetBaseWithConstantOffset(Op0.first, Op0.second, Op0Off);
      ValCtx Op1Base = GetBaseWithConstantOffset(Op1.first, Op1.second, Op1Off);

      if(Op0Base.first == Op1Base.first && Op0Base.second == Op1Base.second) {

	// Subtracting pointers with a common base.
	Improved = const_vc(ConstantInt::getSigned(BOp->getType(), (Op0.offset + Op0Off) - (Op1.offset + Op1Off)));
	return true;

      }

    }
    else {

      if(ConstantInt* Op1I = dyn_cast<ConstantInt>(Op1.first)) {

	// Subtract int from pointer:
	Improved = make_vc(Op0.first, Op0.second, Op0.offset - Op1I->getSExtValue());
	return true;

      }

    }

  }
  else if(BOp->getOpcode() == Instruction::And) {

    // Common technique to discover a pointer's alignment -- and it with a small integer.
    // Answer if we can.

    if((!Op0Ptr) || Op1Ptr)
      return false;

    ConstantInt* MaskC = dyn_cast<ConstantInt>(Op1.first);
    if(!MaskC)
      return false;

    // Find the offset due to GEP instructions before inttoptr was called.
    int64_t Offset;
    ValCtx PtrBase = GetBaseWithConstantOffset(Op0.first, Op0.second, Offset);
    assert((PtrBase != VCNull) && "Couldn't resolve known pointer?");

    Offset += Op0.offset;

    if(Offset < 0)
      return false;

    uint64_t UOff = (uint64_t)Offset;

    // Try to get alignment:

    unsigned Align = 0;
    if(GlobalValue* GV = dyn_cast<GlobalValue>(PtrBase.first))
      Align = GV->getAlignment();
    else if(AllocaInst* AI = dyn_cast<AllocaInst>(PtrBase.first))
      Align = AI->getAlignment();
    else if(CallInst* CI = dyn_cast<CallInst>(PtrBase.first)) {
      Function* F = PtrBase.second->getCalledFunction(CI);
      if(F && F->getName() == "malloc") {
	Align = pass->getMallocAlignment();
      }
    }
      
    uint64_t Mask = MaskC->getLimitedValue();
	
    if(Align > Mask) {

      Improved = const_vc(ConstantInt::get(BOp->getType(), Mask & UOff));
      return true;

    }

  }

  return false;

}



bool IntegrationAttempt::shouldTryEvaluate(Value* ArgV, bool verbose) {

  Instruction* I;
  Argument* A;

  if((I = dyn_cast<Instruction>(ArgV))) {
    if(blockIsDead(I->getParent())) {
      if(verbose)
	DEBUG(dbgs() << itcache(*ArgV) << " already eliminated (in dead block)\n");
      return false;
    }
  }
  else if((A = dyn_cast<Argument>(ArgV))) {
    // Fall through
  }
  else {
    if(verbose)
      DEBUG(dbgs() << "Improvement candidate " << itcache(*I) << " neither an instruction nor an argument!");
    return false;
  }

  ValCtx Improved = getReplacement(ArgV);
  if(Improved != getDefaultVC(ArgV)) {
    if(verbose)
      DEBUG(dbgs() << itcache(*ArgV) << " already improved\n");
    return false;
  }

  return true;

}

bool IntegrationAttempt::tryFoldBitwiseOp(Instruction* BOp, ValCtx& Improved) {

  switch(BOp->getOpcode()) {
  default:
    return false;
  case Instruction::And:
  case Instruction::Or:
    break;
  }

  Constant* Op0C = getConstReplacement(BOp->getOperand(0));
  Constant* Op1C = getConstReplacement(BOp->getOperand(1));

  if(BOp->getOpcode() == Instruction::And) {

    if((Op0C && Op0C->isNullValue()) || (Op1C && Op1C->isNullValue())) {

      Improved = const_vc(Constant::getNullValue(BOp->getType()));
      return true;

    }

  }
  else {

    bool allOnes = false;

    if(ConstantInt* Op0CI = dyn_cast_or_null<ConstantInt>(Op0C)) {

      if(Op0CI->isAllOnesValue())
	allOnes = true;

    }
      
    if(!allOnes) {
      if(ConstantInt* Op1CI = dyn_cast_or_null<ConstantInt>(Op1C)) {

	if(Op1CI->isAllOnesValue())
	  allOnes = true;

      }
    }

    if(allOnes) {

      Improved = const_vc(Constant::getAllOnesValue(BOp->getType()));
      return true;

    }

  }

  return false;

}

ValCtx IntegrationAttempt::tryEvaluateResult(Value* ArgV) {
  
  if(!shouldTryEvaluate(ArgV)) {
    return VCNull;
  }

  Instruction* I;
  ValCtx Improved = VCNull;
  if((I = dyn_cast<Instruction>(ArgV))) {

    if (isa<BranchInst>(I) || isa<SwitchInst>(I)) {

      Value* Condition;
      // Both Branches and Switches have one potentially non-const arg which we now know is constant.
      // The mechanism used by InlineCosts.cpp here emphasises code size. I try to look for
      // time instead, by searching for PHIs that will be made constant.
      if(BranchInst* BI = dyn_cast<BranchInst>(I))
	Condition = BI->getCondition();
      else {
	SwitchInst* SI = cast<SwitchInst>(I);
	Condition = SI->getCondition();
      }
      
      ConstantInt* ConstCondition = dyn_cast_or_null<ConstantInt>(getConstReplacement(Condition));

      if(ConstCondition) {

	BasicBlock* takenTarget = 0;

	if(BranchInst* BI = dyn_cast<BranchInst>(I)) {
	  // This ought to be a boolean.
	  if(ConstCondition->isZero())
	    takenTarget = BI->getSuccessor(1);
	  else
	    takenTarget = BI->getSuccessor(0);
	}
	else {
	  SwitchInst* SI = cast<SwitchInst>(I);
	  unsigned targetidx = SI->findCaseValue(ConstCondition);
	  takenTarget = SI->getSuccessor(targetidx);
	}
	if(takenTarget) {
	  // We know where the instruction is going -- remove this block as a predecessor for its other targets.
	  LPDEBUG("Branch or switch instruction given known target: " << takenTarget->getName() << "\n");

	  TerminatorInst* TI = cast<TerminatorInst>(I);

	  const unsigned NumSucc = TI->getNumSuccessors();

	  for (unsigned I = 0; I != NumSucc; ++I) {

	    BasicBlock* thisTarget = TI->getSuccessor(I);

	    if(thisTarget != takenTarget) {
	      if(!edgeIsDead(TI->getParent(), thisTarget)) {
		setEdgeDead(TI->getParent(), thisTarget);
		checkLoopSpecialEdge(TI->getParent(), thisTarget);
	      }
	    }

	  }

	}

      }

      return VCNull;

    }
    else {

      // A non-branch instruction. First check for instructions with non-standard ways to evaluate / non-standard things to do with the result:

      bool tryConstFold = false;

      if(CallInst* CI = dyn_cast<CallInst>(I)) {
	
	InlineAttempt* IA = getInlineAttempt(CI);
	if(IA) {
	 
	  Improved = IA->tryGetReturnValue();

	}

      }
      else if(PHINode* PN = dyn_cast<PHINode>(I)) {

	// PHI nodes are special because of their BB arguments, and the special-case "constant folding" that affects them
	Improved = getPHINodeValue(PN);

      }

      // Try to calculate a constant value resulting from this instruction. Only possible if
      // this instruction is simple (e.g. arithmetic) and its arguments have known values, or don't matter.

      else if(SelectInst* SI = dyn_cast<SelectInst>(I)) {

	Constant* Cond = getConstReplacement(SI->getCondition());
	if(Cond) {
	  if(cast<ConstantInt>(Cond)->isZero())
	    Improved = getReplacement(SI->getFalseValue());
	  else
	    Improved = getReplacement(SI->getTrueValue());
	}

      }

      // Special cases for forwarding file descriptors, which are not represented as constants but rather VCs pointing to open instructions and so don't fall into the else case:
      // Allow an FD to be no-op transferred when subject to any cast that preserves 32 bits.

      else if(CastInst* CI = dyn_cast<CastInst>(I)) {

	if(I->getOpcode() == Instruction::PtrToInt) {

	  Improved = tryFoldPtrToInt(I);
	  if(Improved == VCNull)
	    tryConstFold = true;

	}

	else if(I->getOpcode() == Instruction::IntToPtr) {

	  Improved = tryFoldIntToPtr(I);
	  if(Improved == VCNull)
	    tryConstFold = true;
	  
	}

	else {

	  const Type* SrcTy = CI->getSrcTy();
	  const Type* DestTy = CI->getDestTy();
	
	  ValCtx SrcVC = getReplacement(CI->getOperand(0));

	  if(SrcVC.isVaArg()) {

	    Improved = SrcVC;

	  }

	  else if(((SrcVC.second && SrcVC.second->isForwardableOpenCall(SrcVC.first)) || SrcVC.isPtrAsInt())
		  && (SrcTy->isIntegerTy(32) || SrcTy->isIntegerTy(64) || SrcTy->isPointerTy()) 
		  && (DestTy->isIntegerTy(32) || DestTy->isIntegerTy(64) || DestTy->isPointerTy())) {

	    Improved = SrcVC;

	  }
	  else {

	    tryConstFold = true;

	  }

	}

      }

      // Check for a special case making comparisons against symbolic FDs, which we know to be >= 0.
      else if(CmpInst* CmpI = dyn_cast<CmpInst>(I)) {

	tryConstFold = !(tryFoldOpenCmp(CmpI, Improved) || tryFoldPointerCmp(CmpI, Improved) || tryFoldNonConstCmp(CmpI, Improved));

      }

      else if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(I)) {

	tryConstFold = true;
	
	ValCtx Base = getReplacement(GEP->getPointerOperand());
	if(Base.isVaArg()) {

	  if(GEP->getNumIndices() == 1 && !GEP->hasAllZeroIndices()) {

	    if(ConstantInt* CI = dyn_cast_or_null<ConstantInt>(getConstReplacement(*(GEP->idx_begin())))) {

	      uint64_t GEPOff = CI->getLimitedValue();
	      assert(GEPOff % 8 == 0);
	      GEPOff /= 8;

	      int64_t newVaArg = -1;
	      switch(Base.getVaArgType()) {
	      case va_arg_type_baseptr:
		// This is indexing off the frame base pointer.
		// Determine which zone it's in:
		if(GEPOff < 6) {
		  // Non-FP zone:
		  newVaArg = GEPOff - (getInitialBytesOnStack(Base.second->getFunction()) / 8);
		}
		else if(GEPOff >= 6 && GEPOff < 22) {
		  newVaArg = (((GEPOff - 6) / 2) - (getInitialFPBytesOnStack(Base.second->getFunction()) / 16)) + ValCtx::first_fp_arg;
		}
		else {
		  newVaArg = ValCtx::not_va_arg;
		}
		break;
	      case va_arg_type_fp:
	      case va_arg_type_nonfp:
		assert(GEPOff == 1);
		// In the spilled zone. Find the next spilled argument:
		newVaArg = Base.second->getFunctionRoot()->getSpilledVarargAfter(Base.va_arg);
		break;
	      default:
		assert(0);
	      }

	      if(newVaArg != ValCtx::not_va_arg) {
		Improved = make_vc(Base.first, Base.second, ValCtx::noOffset, newVaArg);
	      }
	      tryConstFold = false;

	    }

	  }
	  
	}

      }

      else if(I->getOpcode() == Instruction::Add || I->getOpcode() == Instruction::Sub || I->getOpcode() == Instruction::And || I->getOpcode() == Instruction::Or) {

	tryConstFold = /*(!tryFoldVarargAdd(BOp, Improved)) && */(!tryFoldPtrAsIntOp(I, Improved));
	if(tryConstFold)
	  tryConstFold = !tryFoldBitwiseOp(I, Improved);
	    
      }

      else {

	tryConstFold = true;

      }

      if(tryConstFold) {

	SmallVector<Constant*, 4> instOperands;

	// This isn't as good as it could be, because the constant-folding library wants an array of constants,
	// whereas we might have somethig like 1 && x, which could fold but x is not a Constant*. Could work around this,
	// don't at the moment.
	for(unsigned i = 0; i < I->getNumOperands(); i++) {
	  Value* op = I->getOperand(i);
	  if(Constant* C = getConstReplacement(op))
	    instOperands.push_back(C);
	  else {
	    LPDEBUG("Not constant folding yet due to non-constant argument " << itcache(*op) << "\n");
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
	    newConst = ConstantFoldInstOperands(I->getOpcode(), I->getType(), instOperands.data(), I->getNumOperands(), this->TD, /* preserveGEPSign = */ true);

	  if(newConst) {
	    LPDEBUG(itcache(*I) << " now constant at " << itcache(*newConst) << "\n");
	    Improved = const_vc(newConst);
	  }
	  else {
	    if(I->mayReadFromMemory() || I->mayHaveSideEffects()) {
	      LPDEBUG("User " << itcache(*I) << " may read or write global state; not propagating\n");
	    }
	    else {
	      LPDEBUG("User " << itcache(*I) << " has all-constant arguments, but couldn't be constant folded\n");
	    }
	    Improved = VCNull;
	  }
	}

      }

    }

  }
  else {
    LPDEBUG("Improvement candidate " << itcache(*I) << " neither an instruction nor an argument!\n");
    return VCNull;
  }

  return Improved;

}

ValCtx InlineAttempt::tryEvaluateResult(Value* V) {

  Argument* A;
  if((A = dyn_cast<Argument>(V))) {
    return getImprovedCallArgument(A);
  }
  else {
    return IntegrationAttempt::tryEvaluateResult(V);
  }

}

// Implement a visitor that gets called for every dynamic use of an instruction.

bool IntegrationAttempt::visitNextIterationPHI(Instruction* I, VisitorContext& Visitor) {

  return false;

}

bool PeelIteration::visitNextIterationPHI(Instruction* I, VisitorContext& Visitor) {

  if(PHINode* PN = dyn_cast<PHINode>(I)) {

    if(PN->getParent() == L->getHeader()) {

      if(PeelIteration* PI = getNextIteration()) {

	Visitor.visit(PI, PN);

      }
      else {

	Visitor.notifyUsersMissed();

      }

      return true;

    }

  }

  return false;

}

void PeelIteration::visitVariant(Instruction* VI, const Loop* VILoop, VisitorContext& Visitor) {

  const Loop* immediateChild = immediateChildLoop(L, VILoop);

  PeelAttempt* LPA = getPeelAttempt(immediateChild);
  if(LPA)
    LPA->visitVariant(VI, VILoop, Visitor);
  else 
    Visitor.notifyUsersMissed();

}

void PeelAttempt::visitVariant(Instruction* VI, const Loop* VILoop, VisitorContext& Visitor) {

  if(Iterations.back()->iterStatus != IterationStatusFinal)
    Visitor.notifyUsersMissed();

  // Is this a header PHI? If so, this definition-from-outside can only matter for the preheader edge.
  if(VILoop == L && VI->getParent() == L->getHeader() && isa<PHINode>(VI)) {

    Visitor.visit(Iterations[0], VI);
    return;

  }

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), itend = Iterations.end(); it != itend; ++it) {

    if(VILoop == L)
      Visitor.visit(*it, VI);
    else
      (*it)->visitVariant(VI, VILoop, Visitor);

  }

}

void IntegrationAttempt::visitExitPHI(Instruction* UserI, VisitorContext& Visitor) {

  assert(0 && "Tried to visit exit PHI in non-loop context");

}
  
static void checkExitPHI(const Loop* PHIL, const Loop* L, Instruction* UserI, IntegrationAttempt* IA) {

  if(PHIL && !PHIL->contains(L)) {
    
    errs() << PHIL->getHeader()->getName() << " does not contain " << L->getHeader()->getName() << " forwarding " << IA->itcache(make_vc(UserI, IA)) << "\n";
    assert(0);
    
  }

}

void PeelIteration::visitExitPHI(Instruction* UserI, VisitorContext& Visitor) {

  // Used in a non-this, non-child scope. Because we require that programs are in LCSSA form, that means it's an exit PHI. It could however occur in any parent loop.
  if(parentPA->Iterations.back()->iterStatus == IterationStatusFinal) {
    assert(isa<PHINode>(UserI));
    // No need for getBlockScopeVariant: exit PHI already known to be at lower scope.
    const Loop* PHIL = LI[&F]->getLoopFor(UserI->getParent());
    DEBUG(checkExitPHI(PHIL, L, UserI, this));

    parent->visitExitPHIWithScope(UserI, Visitor, PHIL);
  }

}

void IntegrationAttempt::visitExitPHIWithScope(Instruction* UserI, VisitorContext& Visitor, const Loop* UserL) {

  if(UserL == getLoopContext())
    Visitor.visit(this, UserI);
  else {
    assert(getLoopContext() && "About to leave function in visitExitPHIWithScope!");
    parent->visitExitPHIWithScope(UserI, Visitor, UserL);
  }

}

void IntegrationAttempt::visitUser(Value* UI, VisitorContext& Visitor) {

  // Figure out what context cares about this value. The only possibilities are: this loop iteration, the next iteration of this loop (latch edge of header phi),
  // a child loop (defer to it to decide what to do), or a parent loop (again defer).
  // Note that nested cases (e.g. this is an invariant two children deep) are taken care of in the immediate child or parent's logic.

  Instruction* UserI = dyn_cast<Instruction>(UI);

  if(UserI) {

    const Loop* L = getValueScope(UserI); // The innermost loop on which the user has dependencies (distinct from the loop it actually occupies).

    const Loop* MyL = getLoopContext();

    if(L == MyL) {
	  
      if(!visitNextIterationPHI(UserI, Visitor)) {

	// Just an ordinary user in the same iteration (or out of any loop!).
	Visitor.visit(this, UserI);

      }

    }
    else {

      if((!MyL) || MyL->contains(L)) {

	const Loop* outermostChildLoop = immediateChildLoop(MyL, L);
	// Used in a child loop. Check if that child exists at all and defer to it.

	PeelAttempt* LPA = getPeelAttempt(outermostChildLoop);

	if(LPA)
	  LPA->visitVariant(UserI, L, Visitor);
	else {

	  Visitor.notifyUsersMissed();

	}

      }
      else {

	visitExitPHI(UserI, Visitor);

      }

    }

  }

}

void IntegrationAttempt::visitUsers(Value* V, VisitorContext& Visitor) {

  for(Value::use_iterator UI = V->use_begin(), UE = V->use_end(); UI != UE && Visitor.shouldContinue(); ++UI) {

    visitUser(*UI, Visitor);

  }

}

bool IntegrationAttempt::inDeadValues(Value* V) {

  return deadValues.count(V);

}

bool IntegrationAttempt::valueWillBeReplacedWithConstantOrDeleted(Value* V) {

  return valueWillNotUse(V, VCNull, true);

}

bool IntegrationAttempt::valueWillBeRAUWdOrDeleted(Value* V) {
  
  return valueWillNotUse(V, VCNull);
  
}

bool IntegrationAttempt::valueWillBeDeleted(Value* V) {

  return unusedWriters.count(V) || deadValues.count(V);

}

bool InlineAttempt::loopHeaderPhiWillCopy(Value* V, ValCtx OtherVC) {

  return false;

}

bool PeelIteration::loopHeaderPhiWillCopy(Value* V, ValCtx OtherVC) {

  // The precise problem here: we might have some ptr %alloc and a string of PHIs each resolved to
  // %alloc all of which are dead except the last which has users. This is fine because PHIs are
  // replaced with the pointer, not their predecessor PHI... except when the loop unroller or inliner
  // get involved, then they just forward an immediate argument, so we cheat and bring the immediate
  // arg back to life. The same treatment applies to dead actual args which are used as proxies for
  // formal arguments.
  
  if(PHINode* PN = dyn_cast<PHINode>(V)) {

    if(PN->getParent() == L->getHeader()) {

      if(iterationCount == 0) {
	if(OtherVC == parent->getDefaultVC(PN->getIncomingValueForBlock(L->getLoopPreheader())))
	  return true;
      }
      else {
	PeelIteration* prevIter = parentPA->Iterations[iterationCount-1];
	ValCtx latchVC = prevIter->getDefaultVC(PN->getIncomingValueForBlock(L->getLoopLatch()));
	if(OtherVC == latchVC)
	  return true;
      }

    }

  }

  return false;

}

bool IntegrationAttempt::valueWillNotUse(Value* V, ValCtx OtherVC, bool mustReplWithConstant) {

  Instruction* I = dyn_cast<Instruction>(V);

  if(unusedWriters.count(V))
    return true;
  if(deadValues.count(V))
    return true;
  if(I && blockIsDead(I->getParent()))
    return true;
  ValCtx VC = getReplacement(V);

  // The other value will be replaced with this V, so it will remain a user.
  // This test might be redundant, because such a user is an indirect user so if it's alive
  // we should be alive too.
  if(VC == OtherVC)
    return false;

  // Not replaced with constant?
  if(mustReplWithConstant && VC.second)
    return false;

  // Didn't improve?
  if(VC == getDefaultVC(V))
    return false;

  // Value types that don't get replaced on commit:
  if(VC.isVaArg())
    return false;
  if(VC.isPtrAsInt())
    return false;

  if(VC.second) {

    // Will we be able to fold the replacement?
    if(!VC.second->isAvailableFromCtx(this))
      return false;
  
    // Are we going to naively copy the OtherVC rather than get properly replaced
    // by the pointer we're resolved to? (This happens if we're a header PHI or argument)
    // Arguments analysed like this are already known to be direct users of OtherVC.
    if(isa<Argument>(V))
      return false;

    if(loopHeaderPhiWillCopy(V, OtherVC))
      return false;

  }

  return true;

}

class DIVisitor : public VisitorContext {

  Value* V;
  IntegrationAttempt* OriginCtx;

public:

  bool maybeLive;

  DIVisitor(Value* _V, IntegrationAttempt* _Ctx) : V(_V), OriginCtx(_Ctx), maybeLive(false) { }

  virtual void visit(IntegrationAttempt* Ctx, Instruction* UserI) {

    if(CallInst* CI = dyn_cast<CallInst>(UserI)) {

      if(Ctx->isResolvedVFSCall(CI)) {

	// FD arguments to resolved calls are not needed.
	if(V == CI->getArgOperand(0))
	  return;

	// The buffer argument isn't needed if the read call will be deleted.
	if(Ctx->isUnusedReadCall(CI)) {

	  if(V == CI->getArgOperand(1))
	    return;

	}

      }

      InlineAttempt* IA = Ctx->getInlineAttempt(CI);
      if(!IA) {
	DEBUG(dbgs() << "Must assume instruction alive due to use in unexpanded call " << Ctx->itcache(*CI) << "\n");
	maybeLive = true;
	return;
      }

      if(V == CI->getCalledValue()) {
	maybeLive = true;
	return;
      }
      else {

	Function* CalledF = Ctx->getCalledFunction(CI);

	if(CalledF) {
	  Function::arg_iterator it = CalledF->arg_begin();
	  for(unsigned i = 0; i < CI->getNumArgOperands(); ++i) {

	    if(CI->getArgOperand(i) == V) {

	      if(it == CalledF->arg_end()) {

		// Varargs
		maybeLive = true;
		return;

	      }
	      else if(!IA->valueWillNotUse(&*it, make_vc(V, OriginCtx))) {

		maybeLive = true;
		return;

	      }

	    }

	    if(it != CalledF->arg_end())
	      ++it;

	  }
	}
	else {
	  maybeLive = true;
	  return;
	}

      }

    }
    else if(Ctx->valueWillNotUse(UserI, make_vc(V, OriginCtx)))
      return;
    else {

      maybeLive = true;

    }

  }
  
  virtual void notifyUsersMissed() {
    maybeLive = true;
  }

  virtual bool shouldContinue() {
    return !maybeLive;
  }

};

bool InlineAttempt::isOwnCallUnused() {

  if(!parent)
    return false;
  else
    return parent->valueIsDead(CI);

}

bool IntegrationAttempt::valueIsDead(Value* V) {

  if(isa<ReturnInst>(V)) {
    
    InlineAttempt* CallerIA = getFunctionRoot();
    return CallerIA->isOwnCallUnused();

  }
  else {

    // Check indirect users if any:

    if(Instruction* I = dyn_cast<Instruction>(V)) {

      DenseMap<Instruction*, SmallVector<ValCtx, 4> >::iterator it = instIndirectUsers.find(I);
      if(it != instIndirectUsers.end()) {

	for(SmallVector<ValCtx, 4>::iterator II = it->second.begin(), IE = it->second.end(); II != IE; ++II) {
	  
	  if(!II->second->inDeadValues(II->first))
	    return false;

	}

      }

    }

    // Check direct users:

    DIVisitor DIV(V, this);
    visitUsers(V, DIV);

    return !DIV.maybeLive;

  }

}

class WalkOperandCallback : public Callable {

  Value* V;
  OpCallback& CB;

public:

  WalkOperandCallback(Value* _V, OpCallback& _CB) : V(_V), CB(_CB) { }

  virtual void callback(IntegrationAttempt* Ctx) {

    CB.callback(Ctx, V);

  }

};

bool IntegrationAttempt::shouldDIE(Value* V) {

  if(isa<Argument>(V))
    return true;

  Instruction* I = dyn_cast<Instruction>(V);
  
  // Don't try to DIE blocks, functions, constants.
  if(!I)
    return false;

  if(CallInst* CI = dyn_cast<CallInst>(V)) {
    if(getInlineAttempt(CI))
      return true;
    if(forwardableOpenCalls.count(CI))
      return true;
    return false;
  }

  switch(I->getOpcode()) {
  default:
    return true;
  case Instruction::VAArg:
  case Instruction::Alloca:
  case Instruction::Invoke:
  case Instruction::Store:
  case Instruction::Br:
  case Instruction::IndirectBr:
  case Instruction::Switch:
  case Instruction::Unwind:
  case Instruction::Unreachable:
    return false;
  }

}

void IntegrationAttempt::queueDIE(Value* V) {

  //errs() << "Queue DIE " << itcache(make_vc(V, this)) << "\n";

  if(!shouldDIE(V))
    return;
  if(!valueWillBeReplacedWithConstantOrDeleted(V))
    pass->queueDIE(this, V);

}

void IntegrationAttempt::walkOperand(Value* V, OpCallback& CB) {

  const Loop* MyL = getLoopContext();
  const Loop* L = getValueScope(V);

  if(L != MyL) {

    if((!MyL) || MyL->contains(L)) {

      // V is from a child loop; queue against the last iteration if we can.

      PeelAttempt* LPA = getPeelAttempt(L);
      if(!LPA)
	return;

      PeelIteration* Final = LPA->Iterations[LPA->Iterations.size() - 1];
      if(!Final->isOnlyExitingIteration())
	return;

      CB.callback(Final, V);

    }
    else {

      // V is from a parent loop (or the root function).
      WalkOperandCallback WOC(V, CB);
      callWithScope(WOC, L);

    }

  }
  else {

    CB.callback(this, V);

  }

}

bool InlineAttempt::walkHeaderPHIOperands(PHINode* PN, OpCallback& CB) {

  return false;

}

bool PeelIteration::walkHeaderPHIOperands(PHINode* PN, OpCallback& CB) {

  BasicBlock* PNBB = PN->getParent();
  if(PNBB == L->getHeader()) {
    // Header PHI. Have the preheader or latch do the reconsider.
    if(this == parentPA->Iterations[0]) {
      CB.callback(parent, PN->getIncomingValueForBlock(L->getLoopPreheader()));
    }
    else {
      std::vector<PeelIteration*>::iterator it = std::find(parentPA->Iterations.begin(), parentPA->Iterations.end(), this);
      it--;
      CB.callback(*it, PN->getIncomingValueForBlock(L->getLoopLatch()));
    }
    return true;
  }

  return false;

}

void InlineAttempt::walkOperands(Value* V, OpCallback& CB) {

  // Special case: if we're an argument, have our parent reconsider values used by the call.

  if(Argument* A = dyn_cast<Argument>(V)) {

    if(CI) {
      parent->walkOperand(CI->getArgOperand(A->getArgNo()), CB);
    }

  }
  else {

    IntegrationAttempt::walkOperands(V, CB);

  }

}

void IntegrationAttempt::walkOperands(Value* V, OpCallback& CB) {

  // If we're a header PHI, either some parent context or the previous iteration argument might have died.
  // If we're an exit PHI, our operand in the last loop iteration might have died.

  Instruction* I = dyn_cast<Instruction>(V);
  if(!I)
    return;

  const Loop* MyL = getLoopContext();

  if(PHINode* PN = dyn_cast<PHINode>(I)) {
    
    if(MyL == getValueScope(PN) && walkHeaderPHIOperands(PN, CB))
      return;

    for(unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {

      Value* InV = PN->getIncomingValue(i);
      walkOperand(InV, CB);

    }

  }
  else {

    for(unsigned i = 0; i < I->getNumOperands(); ++i) {
      walkOperand(I->getOperand(i), CB);
    }

  }
  
}

class QueueDIECallback : public OpCallback {
public:

  virtual void callback(IntegrationAttempt* Ctx, Value* V) {

    Ctx->queueDIE(V);

  }

};

void IntegrationAttempt::queueDIEOperands(Value* V) {

  // If this instruction would get replaced with an instruction, recheck that instruction.
  
  ValCtx ReplVC = getReplacement(V);
  if(ReplVC != getDefaultVC(V) && ReplVC.second) {

    //errs() << "Queue DIE " << itcache(*ReplVC.first) << " in ctx " << ReplVC.second->getShortHeader() << "\n";
    ReplVC.second->queueDIE(ReplVC.first);

  }

  QueueDIECallback QDC;
  walkOperands(V, QDC);

}

static uint32_t DIEProgressN = 0;
const uint32_t DIEProgressLimit = 1000;

static void DIEProgress() {

  if(!mainDIE)
    return;

  DIEProgressN++;
  if(DIEProgressN == DIEProgressLimit) {

    errs() << ".";
    DIEProgressN = 0;

  }

}

void IntegrationAttempt::tryKillValue(Value* V) {

  if(deadValues.count(V))
    return;

  DIEProgress();

  //errs() << "Trying to kill " << itcache(make_vc(V, this)) << "\n";

  Instruction* I = dyn_cast<Instruction>(V);
  if(I && I->mayHaveSideEffects()) {

    bool ignoreSideEffects = false;

    if(CallInst* CI = dyn_cast<CallInst>(I)) {

      if(forwardableOpenCalls.count(CI))
	ignoreSideEffects = true;

    }
    if(!ignoreSideEffects) {
      LPDEBUG("Not eliminated because of possible side-effects\n");

      if(CallInst* CI = dyn_cast<CallInst>(I)) {
	if(valueIsDead(V)) {

	  LPDEBUG("Call nontheless unused, queueing return instructions\n");

	  // Even if we can't remove the call, its return value is unused.
	  if(InlineAttempt* IA = getInlineAttempt(CI)) {
	  
	    IA->queueAllReturnInsts();
	
	  }

	}
      }

      return;

    }

  }

  if(valueIsDead(V)) {

    LPDEBUG("Success, queueing operands\n");
    
    improvedValues.erase(V);
    deadValues.insert(V);
    queueDIEOperands(V);
    
  }
  else {
    LPDEBUG("Not killed\n");
  }

}

class AlwaysTrue : public UnaryPred {
public:

  virtual bool operator()(Value*) { 

    return true;

  }

};

template<class T> class MatchT : public UnaryPred {
public:

  virtual bool operator()(Value* V) {

    return isa<T>(V);

  }
  
};

void IntegrationAttempt::queueAllLiveValues() {

  AlwaysTrue AT;
  queueAllLiveValuesMatching(AT);

}

void IntegrationAttempt::queueAllReturnInsts() {

  MatchT<ReturnInst> OnlyReturns;
  queueAllLiveValuesMatching(OnlyReturns);

}

void IntegrationAttempt::queueAllLiveValuesMatching(UnaryPred& P) {

  const Loop* MyL = getLoopContext();

  for(Function::iterator BI = F.begin(), BE = F.end(); BI != BE; ++BI) {

    BasicBlock* BB = BI;

    if(blockIsDead(BB))
      continue;

    if(MyL && (!MyL->contains(BB)))
      continue;

    for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II) {

      Instruction* I = II;
      const Loop* L = getValueScope(I);
      if(L != MyL)
	continue;

      if(P(I)) {
	queueDIE(I);
      }

    }

  }

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->queueAllLiveValuesMatching(P);

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it)
    it->second->queueAllLiveValuesMatching(P);

}

void InlineAttempt::queueAllLiveValuesMatching(UnaryPred& P) {

  for(Function::arg_iterator AI = F.arg_begin(), AE = F.arg_end(); AI != AE; ++AI) {

    Argument* A = AI;
    if((!valueWillBeReplacedWithConstantOrDeleted(A)) && P(A)) {
      queueDIE(A);
    }

  }

  IntegrationAttempt::queueAllLiveValuesMatching(P);

}

void PeelAttempt::queueAllLiveValuesMatching(UnaryPred& P) {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->queueAllLiveValuesMatching(P);

}

void IntegrationAttempt::tryEvaluate(Value* V) {

  ValCtx Improved = tryEvaluateResult(V);
 
  if(Improved.first && shouldForwardValue(Improved)) {

    setReplacement(V, Improved);

    if(Improved.second) {

      Improved.second->addForwardedInst(cast<Instruction>(Improved.first), make_vc(V, this));

    }

  }

}

void IntegrationAttempt::checkLoad(LoadInst* LI) {

  if(!shouldTryEvaluate(LI))
    return;

  ValCtx Result = tryForwardLoad(LI);
  if(Result.first) {
    setReplacement(LI, Result);
  }

}

namespace llvm {

  raw_ostream& operator<<(raw_ostream& Stream, const IntegrationAttempt& P) {

    P.describe(Stream);
    return Stream;

  }

/*
  raw_ostream& operator<<(raw_ostream& Stream, const ValCtx& VC) {

    if(!VC.first)
      Stream << "NULL";
    else if(isa<Constant>(VC.first) || !VC.second)
      Stream << *VC.first;
    else
      Stream << *VC.first << "@" << *VC.second;

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
      Stream << *MDR.getInst();
      if(IntegrationAttempt* P = MDR.getCookie()) {
	Stream << "@" << *P;
      }
      Stream << ")";
    }

    return Stream;

  }
*/

}

