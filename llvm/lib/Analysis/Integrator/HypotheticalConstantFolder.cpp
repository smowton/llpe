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

bool llvm::shouldForwardValue(ShadowValue& V) {

  if(V.getVal() && isa<Constant>(V.getVal()))
    return true;

  if(V.isVaArg())
    return true;
  
  if(ShadowInstruction* SI = V.getInst()) {

    if(!SI->baseObject.isInval())
      return true;

    if(SI->parent->IA->isForwardableOpenCall(SI))
      return true;

  }

  return false;

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

bool IntegrationAttempt::getLoopHeaderPHIValue(ShadowInstruction* SI, ValCtx& result) {

  return false;

}

bool PeelIteration::getLoopHeaderPHIValue(ShadowInstruction* SI, ShadowValue& result) {

  PHINode* PN = cast_inst<PHINode>(SI);
  bool isHeaderPHI = PN->getParent() == L->getHeader();

  if(isHeaderPHI) {

    ShadowValue predValue;
    // PHI node operands go value, block, value, block, so 2*value index = operand index.

    if(iterationCount == 0) {

      LPDEBUG("Pulling PHI value from preheader\n");
      // Can just use normal getOperand/replacement here.
      int predIdx = PN->getBasicBlockIndex(L->getLoopPreheader());
      assert(predIdx >= 0 && "Failed to find preheader block");
      predValue = SI->getOperand(predIdx * 2);

    }
    else {

      LPDEBUG("Pulling PHI value from previous iteration latch\n");
      int predIdx = PN->getBasicBlockIndex(L->getLoopLatch());
      assert(predIdx >= 0 && "Failed to find latch block");
      // Find equivalent instruction in previous iteration:
      IntegrationAttempt* prevIter = parentPA->getIteration(iterationCount - 1);
      ShadowInstIdx& SII = SI->invar->operandIdxs[predIdx * 2];
      if(SII.blockIdx != INVALID_BLOCK_IDX)
	predValue = ShadowValue(prevIter->getInst(SII.blockIdx, SII.instIdx));
      else
	predValue = SI->getOperand(predIdx * 2);

    }

    result = getReplacement(predValue);
    copyBaseAndOffset(predValue, SI);

  }

  return isHeaderPHI;

}

void IntegrationAttempt::getOperandRising(ShadowInstructionInvar* SI, ShadowBBInvar* ExitedBB, SmallVector<ShadowValue, 1>& ops) {

  // SI block dead at this scope?
  // I don't use edgeIsDead here because that recursively checks loop iterations
  // which we're about to do anyway.
  if(!getBB(SI->parent->idx))
    return;

  if(SI->scope != L) {
    
  // Read from child loop if appropriate:
  if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(L, SI->scope))) {

    if(PA->Iterations.back()->iterStatus == IterationStatusFinal) {

      for(unsigned i = 0; i < PA->Iterations.size(); ++i) {

	PeelIteration* Iter = PA->Iterations[i];
	Iter->getOperandRising(SI, ExitedBB, ops);

      }

      return;

    }

  }

  // Value is local, or in a child loop which is unterminated or entirely unexpanded.
  if(!edgeIsDead(SI->parent, ExitedBB))
    ops.push_back(getInst(SI));

}

void IntegrationAttempt::getExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops) {

  ShadowInstructionInvar* SII = SI->invar;
  
  ShadowInstIdx valOp = SII->preds[i];
  ShadowInstIdx blockOp = SII->preds[i+1];

  assert(blockOp.blockIdx != INVALID_BLOCK_IDX);

  // PHI arg is an instruction?
  if(valOp.blockIdx != INVALID_BLOCK_IDX) {

    // PHI arg at child scope?
    ShadowInstructionInvar* PredSII = getInstInvar(valOp.blockIdx, valOp.instIdx);
    if(!((!PredSII->scope) || PredSII->scope->contains(L))) {

      getOperandRising(PredSII, SII->parent, ops);
      return;

    }

  }
  
  // Arg is local or a constant or argument, use normal getOperand.
  ShadowBBInvar* BB = getBBInvar(blockOp.blockIdx);
  if(!edgeIsDead(BB, SI->parent->invar))
    ops.push_back(SI->getOperand(valOpIdx));

}

ShadowValue IntegrationAttempt::getPHINodeValue(ShadowInstruction* SI) {

  PHINode* PN = cast_inst<PHINode>(SI);

  ShadowValue onlyValue;
  ShadowValue onlyValueSource;

  if(!getLoopHeaderPHIValue(SI, onlyValue)) {

    LPDEBUG("Trying to evaluate PHI " << itcache(*PN) << " by standard means\n");
   
    bool breaknow = false;
    ShadowInstructionInvar* SII = SI->invar;

    for(uint32_t i = 0, ilim = SII->preds.size(); i != ilim && !breaknow; i+=2) {
      
      SmallVector<ShadowValue, 1> predValues;
      ShadowValue PredV = getExitPHIOperands(SI, i, predValues);

      for(SmallVector<ShadowValue, 1>::iterator it = predValues.begin(), it2 = predValues.end(); it != it2 && !breaknow; ++it) {

	ShadowValue PredRepl = getReplacement(*it);

	if(onlyValue.isInval()) {
	  onlyValue = PredRepl;
	  onlyValueSource = *it;
	}
	else if(onlyValue != PredRepl) {
	  onlyValue = ShadowValue();
	  breakNow = true;
	}
      
      }
    
    }

  }

  if(!onlyValue.isInval() && shouldForwardValue(onlyValue)) {
    copyBaseAndOffset(predValue, SI);
    LPDEBUG("Improved to " << itcache(onlyValue) << "\n");
    return onlyValue;
  }
  else {
    LPDEBUG("Not improved\n");
    return ShadowValue();
  }
  
}

ShadowValue IntegrationAttempt::tryFoldOpenCmp(CmpInst* CmpI, ConstantInt* CmpInt, bool flip) {

  if(CmpInt->getBitWidth() > 64) {
    LPDEBUG("Using an int wider than int64 for an FD\n");
    return ShadowValue();
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
      return ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
    break;
  case CmpInst::ICMP_NE:
    if(CmpVal < 0)
      return ShadowValue(ConstantInt::getTrue(CmpI->getContext()));    
    break;
  case CmpInst::ICMP_SGT:
    if(CmpVal < 0)
      return ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
    break;
  case CmpInst::ICMP_SGE:
    if(CmpVal <= 0)
      return ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
    break;
  case CmpInst::ICMP_SLT:
    if(CmpVal <= 0)
      return ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
    break;
  case CmpInst::ICMP_SLE:
    if(CmpVal < 0)
      return ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
    break;
  default:
    LPDEBUG("Failed to fold " << itcache(*CmpI) << " because it compares a symbolic FD using an unsupported predicate\n");
    break;
  }

  return ShadowValue();

}

// Return true if this turned out to be a compare against open
// (and so false if there's any point trying normal const folding)
bool IntegrationAttempt::tryFoldOpenCmp(ShadowInstruction* SI, ShadowValue& Improved) {

  CmpInst* CmpI = cast_inst<CmpInst>(SI->invar->I);

  bool flip;
  bool exists;
  ConstantInt* CmpInt = 0;
  ShadowValue op0 = getReplacement(SI->getOperand(0));
  ShadowValue op1 = getReplacement(SI->getOperand(1));
  ShadowInstruction* op0I = op0->getInst();
  ShadowInstruction* op1I = op1->getInst();

  if(op0I && op0I->parent->IA->isForwardableOpenCall(op0->invar->I)) {
    flip = false;
    exists = op0I->parent->IA->openCallSucceeds(op0->invar->I);
    CmpInt = dyn_cast<ConstantInt>(op1.getVal());
  }
  else if(op1I && op1I->parent->IA->isForwardableOpenCall(op1->invar->I)) {
    flip = true;
    exists = op1I->parent->IA->openCallSucceeds(op1->invar->I);
    CmpInt = dyn_cast<ConstantInt>(op0.getVal());
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
      Improved = ShadowValue(ConstantFoldCompareInstOperands(CmpI->getPredicate(), Arg0, Arg1, TD));
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

bool IntegrationAttempt::tryFoldNonConstCmp(ShadowInst* SI, ShadowValue& Improved) {

  CmpInst* CmpI = cast_inst<CmpInst>(SI);

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

  Constant* Op0C = getConstReplacement(SI->getOperand(0));
  Constant* Op1C = getConstReplacement(SI->getOperand(1));
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
      Improved = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_UGE:
    // Always u>= 0
    if(Op1C->isNullValue()) {
      Improved = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_ULT:
    // Never u< 0
    if(Op1C->isNullValue()) {
      Improved = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_ULE:
    // Always u<= ~0
    if(Op1CI && Op1CI->isAllOnesValue()) {
      Improved = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SGT:
    // Never s> maxint
    if(Op1CI && Op1CI->isMaxValue(true)) {
      Improved = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SGE:
    // Always s>= minint
    if(Op1CI && Op1CI->isMinValue(true)) {
      Improved = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SLT:
    // Never s< minint
    if(Op1CI && Op1CI->isMinValue(true)) {
      Improved = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SLE:
    // Always s<= maxint
    if(Op1CI && Op1CI->isMaxValue(true)) {
      Improved = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;     
    }
    break;
  }

  return false;

}

// Return value as above: true for "we've handled it" and false for "try constant folding"
bool IntegrationAttempt::tryFoldPointerCmp(ShadowInstruction* SI, ShadowValue& Improved) {

  CmpInst* CmpI = cast_inst<CmpInst>(SI);

  // Check for special cases of pointer comparison that we can understand:

  ShadowValue op0 = SI->getOperand(0);
  ShadowValue op1 = SI->getOperand(1);

  // Only integer and pointer types can possibly represent pointers:
  if(!((op0.getType()->isIntegerTy() || op0.getType()->isPointerTy()) && 
       (op1.getType()->isIntegerTy() || op1.getType()->isPointerTy())))
    return false;
 
  Constant* op0C = getConstReplacement(op0);
  Constant* op1C = getConstReplacement(op1);
  int64_t op0Off = 0, op1Off = 0;
  
  ShadowValue op0O, op1O;
  if((!getBaseAndOffset(op0, op0O, op0Off)) || (!getBaseAndOffset(op1, op1O, op1Off)))
    return false;

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
  else if(op0O.getType()->isPointerTy() && isGlobalIdentifiedObject(op0O))
    op0Arg = one;
  
  if(op1C && op1C->isNullValue())
    op1Arg = zero;
  else if(op1O.getType()->isPointerTy() && isGlobalIdentifiedObject(op1O))
    op1Arg = one;

  if(op0Arg && op1Arg && (op0Arg == zero || op1Arg == zero)) {
    
    Improved = ShadowValue(ConstantFoldCompareInstOperands(CmpI->getPredicate(), op0Arg, op1Arg, this->TD));
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
    Improved = ShadowValue(ConstantFoldCompareInstOperands(getSignedPred(CmpI->getPredicate()), op0Arg, op1Arg, this->TD));
    return true;

  }

  // 3. Restricted comparison of pointers with a differing base: we can compare for equality only
  // as we don't know memory layout at this stage.

  if(isGlobalIdentifiedObject(op0O) && isGlobalIdentifiedObject(op1O) && op0O != op1O) {

    if(CmpI->getPredicate() == CmpInst::ICMP_EQ) {
      Improved = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    else if(CmpI->getPredicate() == CmpInst::ICMP_NE) {
      Improved = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }

  }

  return false;

}

ShadowValue IntegrationAttempt::tryFoldPtrToInt(ShadowInstruction* SPII) {

  ShadowValue Arg = SPII->getOperand(0);
  ShadowValue ArgRep = getReplacement(Arg);

  // First try to knock out a trivial CE:
  if(Value* V = ArgRep.getVal()) {

    if(ConstantExpr* CE = dyn_cast<ConstantExpr>(V)) {

      if(CE->getOpcode() == Instruction::IntToPtr) {

	return ShadowValue(CE->getOperand(0));

      }

    }

  }

  copyBaseAndOffset(Arg, SPII);
  return ShadowValue();

}

ShadowValue IntegrationAttempt::tryFoldIntToPtr(ShadowInstruction* IPI) {

  ShadowValue Arg = IPI->getOperand(0);
  ShadowValue ArgRep = getReplacement(Arg);
  
  copyBaseAndOffset(Arg, IPI);
  return ShadowValue();

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

struct constPtrAsInt {

  Constant* BaseOrConst;
  bool isPtrAsInt;
  int64_t Offset;

  constPtrAsInt(Constant* B, int64_t O) : BaseOrConst(B), isPtrAsInt(true), Offset(O) { }
  constPtrAsInt(Constant* C) : BaseOrConst(C), isPtrAsInt(false);

};

static constPtrAsInt evaluatePtrAsIntCE(Constant* C) {

  ConstantExpr* CE = dyn_cast<ConstantExpr>(C);
  if(!CE)
    return constPtrAsInt(C);

  if(!containsPtrAsInt(CE))
    return constPtrAsInt(C);

  switch(CE->getOpcode()) {

  case Instruction::PtrToInt:
    {
      int64_t Offset;
      Constant* Base = GetBaseWithConstantOffset(CE->getOperand(0), Offset);
      return constPtrAsInt(Base, Offset);
    }
  case Instruction::SExt:
  case Instruction::ZExt:
    return evaluatePtrAsIntCE(CE->getOperand(0));
  case Instruction::Add:
  case Instruction::Sub:
    {

      constPtrAsInt Op1 = evaluatePtrAsIntCE(CE->getOperand(0));
      constPtrAsInt Op2 = evaluatePtrAsIntCE(CE->getOperand(1));

      if(!(Op1.isPtrAsInt || Op2.isPtrAsInt)) {

	if(CE->getOpcode() == Instruction::Add)
	  return constPtrAsInt(ConstantExpr::getAdd(cast<Constant>(Op1.first), cast<Constant>(Op2.first)));
	else
	  return constPtrAsInt(ConstantExpr::getSub(cast<Constant>(Op1.first), cast<Constant>(Op2.first)));

      }

      if(CE->getOpcode() == Instruction::Add) {

	if(Op2.isPtrAsInt)
	  std::swap(Op1, Op2);

	if(Op2.isPtrAsInt) // Can't add 2 pointers
	  return constPtrAsInt(CE);

	if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.BaseOrConst))
	  return constPtrAsInt(Op1.BaseOrConst, Op1.Offset + Op2C->getLimitedValue());
	else
	  return constPtrAsInt(CE);

      }
      else {
	
	if(Op1.isPtrAsInt()) {
	  
	  if(Op2.isPtrAsInt()) {
	    
	    if(Op1.ConstOrBase == Op2.ConstOrBase) {

	      return constPtrAsInt(ConstantInt::get(Type::getInt64Ty(CE->getContext()), Op1.offset - Op2.offset));
	      
	    }
	    // Else can't subtract 2 pointers with unknown base

	  }
	  else {

	    if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.BaseOrConst))
	      return constPtrAsInt(Op1.BaseOrConst, Op1.Offset - Op2C->getLimitedValue());
	    else
	      return constPtrAsInt(CE);

	  }
	  
	}
	
      }

      // Fall through to default

    }	

  default:
    return constPtrAsInt(CE);

  }

}

void IntegrationAttempt::getPtrAsIntReplacement(ShadowValue& V, bool& isPtr, ShadowValue& Base, int64_t& Offset) {

  ShadowValue VC = getReplacement(V);

  if(Value* VCV = VC.getVal()) {

    if(ConstantExpr* CE = dyn_cast<ConstantExpr>(VCV)) {

      constPtrAsInt CPI = evaluatePtrAsIntCE(CE);
      isPtr = CPI.isPtrAsInt;
      Base = ShadowValue(CPI.BaseOrConst);
      Offset = CPI.Offset;
      return;

    }
    else {

      isPtr = false;
      Base = ShadowValue(VCV);
      return;

    }

  }
  else {

    isPtr = getBaseAndOffset(V, Base, Offset);
    if(!isPtr)
      Base = getReplacement(V);

  }

}

// These two methods are closely related: this one tries to establish a pointer base and offset,
// whilst the one below tries to establish a mundane constant result, e.g. (ptrasint(x) + 1 - ptrasint(x)) = 1.
bool IntegrationAttempt::tryGetPtrOpBase(ShadowInstruction* SI, ShadowValue& Base, int64_t& Offset) {

  Instruction* BOp = SI->invar->I;
  
  if(BOp->getOpcode() != Instruction::Add && BOp->getOpcode() != Instruction::Sub && BOp->getOpcode())
    return false;

  ShadowValue Op0, Op1;
  bool Op0Ptr, Op1Ptr;
  int64_t Op0Offset, Op1Offset;

  getPtrAsIntReplacement(SI->getOperand(0), Op0Ptr, Op0, Op0Offset);
  getPtrAsIntReplacement(SI->getOperand(1), Op1Ptr, Op1, Op1Offset);

  if(BOp->getOpcode() == Instruction::Add) {
  
    if(Op0Ptr && Op1Ptr)
      return false;

    ShadowValue PtrV = Op0Ptr ? Op0 : Op1;
    int64_t PtrOff = Op0Ptr ? Op0Offset : Op1Offset;
    ConstantInt* NumC = dyn_cast_or_null<ConstantInt>(Op0Ptr ? Op1.getVal() : Op0.getVal());
    
    if(!NumC)
      return false;

    Base = PtrV;
    Offset = NumC->getSExtValue() + PtrOff;

    return true;

  }
  else if(BOp->getOpcode() == Instruction::Sub) {

    if((!Op0Ptr) || Op1Ptr)
      return false;

    if(ConstantInt* Op1I = dyn_cast_or_null<ConstantInt>(Op1.getVal())) {

      // Subtract int from pointer:
      Base = Op0;
      Offset = Op0Offset - Op1I->getSExtValue();
      return true;
      
    }
    
  }

}

bool IntegrationAttempt::tryFoldPtrAsIntOp(ShadowInstruction* SI, ShadowValue& Improved) {

  Instruction* BOp = SI->invar->I;

  if(!SI->getType()->isIntegerTy())
    return false;

  tryGetPtrOpBase(SI, SI->i.baseObject, SI->i.baseOffset);
  
  if(BOp->getOpcode() != Instruction::Sub && BOp->getOpcode() != Instruction::And)
    return false;

  ShadowValue Op0, Op1;
  bool Op0Ptr, Op1Ptr;
  int64_t Op0Offset, Op1Offset;

  getPtrAsIntReplacement(SI->getOperand(0), Op0Ptr, Op0, Op0Offset);
  getPtrAsIntReplacement(SI->getOperand(1), Op1Ptr, Op1, Op1Offset);

  if((!Op0Ptr) && (!Op1Ptr))
    return false;

  else if(BOp->getOpcode() == Instruction::Sub) {

    if(!(Op0Ptr && Op1Ptr))
      return false;

    if(Op1Ptr) {

      if(Op0 == Op1) {

	// Subtracting pointers with a common base.
	Improved = ShadowValue(ConstantInt::getSigned(BOp->getType(), Op0Offset - Op1Offset));
	return true;

      }

    }

  }
  else if(BOp->getOpcode() == Instruction::And) {

    // Common technique to discover a pointer's alignment -- and it with a small integer.
    // Answer if we can.

    if((!Op0Ptr) || Op1Ptr)
      return false;

    ConstantInt* MaskC = dyn_cast_or_null<ConstantInt>(Op1.getVal());
    if(!MaskC)
      return false;

    if(Op0Offset < 0)
      return false;

    uint64_t UOff = (uint64_t)Offset;

    // Try to get alignment:

    unsigned Align = 0;
    if(GlobalValue* GV = dyn_cast_or_null<GlobalValue>(Op0.getVal()))
      Align = GV->getAlignment();
    else if(ShadowInstruction* SI = Op0.getInst()) {

      if(AllocaInst* AI = dyn_cast<AllocaInst>(SI->invar->I))
	Align = AI->getAlignment();
      else if(CallInst* CI = dyn_cast<CallInst>(SI->invar->I)) {
	Function* F = getCalledFunction(SI);
	if(F && F->getName() == "malloc") {
	  Align = pass->getMallocAlignment();
	}
      }

    }

    uint64_t Mask = MaskC->getLimitedValue();
	
    if(Align > Mask) {

      Improved = ShadowValue(ConstantInt::get(BOp->getType(), Mask & UOff));
      return true;

    }

  }

  return false;

}

bool IntegrationAttempt::tryFoldBitwiseOp(ShadowInstruction* SI, ShadowValue& Improved) {

  Instruction* BOp = SI->invar->I;

  switch(BOp->getOpcode()) {
  default:
    return false;
  case Instruction::And:
  case Instruction::Or:
    break;
  }

  Constant* Op0C = getConstReplacement(SI->getOperand(0));
  Constant* Op1C = getConstReplacement(SI->getOperand(1));

  if(BOp->getOpcode() == Instruction::And) {

    if((Op0C && Op0C->isNullValue()) || (Op1C && Op1C->isNullValue())) {

      Improved = ShadowValue(Constant::getNullValue(BOp->getType()));
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

      Improved = ShadowValue(Constant::getAllOnesValue(BOp->getType()));
      return true;

    }

  }

  return false;

}

ShadowValue IntegrationAttempt::tryEvaluateResult(ShadowInstruction* SI) {
  
  Instruction* I = SI->invar->I;
  ShadowValue Improved;

  if (isa<BranchInst>(I) || isa<SwitchInst>(I)) {

    // Unconditional branches are already eliminated.
    // Both switches and conditional branches use operand 0 for the condition.
    ShadowValue Condition = SI->getOperand(0);
      
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

	    // Mark outgoing edge dead.
	    SI->parent->succsAlive[I] = false;

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

      // PHI nodes are special because of their BB arguments and the need to route values
      // from child scopes.
      Improved = getPHINodeValue(SI);

    }

    // Try to calculate a constant value resulting from this instruction. Only possible if
    // this instruction is simple (e.g. arithmetic) and its arguments have known values, or don't matter.

    else if(SelectInst* SelI = dyn_cast<SelectInst>(I)) {

      Constant* Cond = getConstReplacement(SI->getOperand(0));
      if(Cond) {
	ShadowValue copy;
	if(cast<ConstantInt>(Cond)->isZero())
	  copy = SI->getOperand(2);
	else
	  copy = SI->getOperand(1);
	Improved = getReplacement(copy);
	copyBaseAndOffset(copy, SI);
      }

    }

    // Special cases for forwarding file descriptors, which are not represented as constants but rather replacements pointing to open instructions and so don't fall into the else case:
    // Allow an FD to be no-op transferred when subject to any cast that preserves 32 bits.

    else if(CastInst* CI = dyn_cast<CastInst>(I)) {

      // All casts 

      if(I->getOpcode() == Instruction::PtrToInt) {

	Improved = tryFoldPtrToInt(SI);
	if(Improved.isInval())
	  tryConstFold = true;

      }

      else if(I->getOpcode() == Instruction::IntToPtr) {

	Improved = tryFoldIntToPtr(SI);
	if(Improved.isInval())
	  tryConstFold = true;
	  
      }

      else {

	const Type* SrcTy = CI->getSrcTy();
	const Type* DestTy = CI->getDestTy();
	
	ShadowValue SrcVal = getReplacement(SI->getCallArgOperand(0));

	if(ShadowInstruction* SI = SrcVal.getInst()) {

	  if(SrcVal.isVaArg()) {

	    Improved = SrcVal;

	  }
	  else if(SI->parent->IA->isForwardableOpenCall(SI->invar->I)) || SrcVal.isPtrAsInt())
		&& (SrcTy->isIntegerTy(32) || SrcTy->isIntegerTy(64) || SrcTy->isPointerTy()) 
		&& (DestTy->isIntegerTy(32) || DestTy->isIntegerTy(64) || DestTy->isPointerTy())) {

	  Improved = SrcVal;

	}
	else {

	  tryConstFold = true;

	}

      }

    }

    // Check for a special case making comparisons against symbolic FDs, which we know to be >= 0.
    else if(CmpInst* CmpI = dyn_cast<CmpInst>(I)) {

      tryConstFold = !(tryFoldOpenCmp(SI, Improved) || tryFoldPointerCmp(SI, Improved) || tryFoldNonConstCmp(SI, Improved));

    }

    else if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(I)) {

      tryConstFold = true;

      // Inherit base object from GEP if known.
      copyBaseAndObject(SI->getOperand(0), SI);

      if(!SI->i.baseObject.isInval()) {
	// Bump base by amount indexed by GEP:
	gep_type_iterator GTI = gep_type_begin(GEP);
	for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
	     ++I, ++GTI) {
	  ConstantInt* OpC = cast_or_null<ConstantInst>(getConstReplacement(*I));

	  if(!OpC) {
	    // Uncertain -- there's no point tracking vague pointers here
	    // as that work is currently done in the PB solver.
	    SI->i.baseObject = ShadowValue();
	    SI->i.baseOffset = 0;
	  }
	  if (OpC->isZero()) continue;
    
	  // Handle a struct and array indices which add their offset to the pointer.
	  if (const StructType *STy = dyn_cast<StructType>(*GTI)) {
	    SI->i.baseOffset += GlobalTD->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
	  } else {
	    uint64_t Size = GlobalTD->getTypeAllocSize(GTI.getIndexedType());
	    SI->i.baseOffset += OpC->getSExtValue()*Size;
	  }
	}
      }
	
      ShadowValue Base = getReplacement(SI->getOperand(0));
      if(Base.isVaArg()) {

	if(GEP->getNumIndices() == 1 && !GEP->hasAllZeroIndices()) {

	  if(ConstantInt* CI = dyn_cast_or_null<ConstantInt>(getConstReplacement(SI->getOperand(1)))) {

	    Function* calledF = Base.getInst()->parent->getFunction();

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
		newVaArg = GEPOff - (getInitialBytesOnStack(calledF) / 8);
	      }
	      else if(GEPOff >= 6 && GEPOff < 22) {
		newVaArg = (((GEPOff - 6) / 2) - (getInitialFPBytesOnStack(calledF) / 16)) + ShadowValue::first_fp_arg;
	      }
	      else {
		newVaArg = ShadowValue::not_va_arg;
	      }
	      break;
	    case va_arg_type_fp:
	    case va_arg_type_nonfp:
	      assert(GEPOff == 1);
	      // In the spilled zone. Find the next spilled argument:
	      newVaArg = Base.getInst()->parent->getFunctionRoot()->getSpilledVarargAfter(Base.va_arg);
	      break;
	    default:
	      assert(0);
	    }

	    if(newVaArg != ValCtx::not_va_arg) {
	      Improved = ShadowValue(Base, ShadowValue::noOffset, newVaArg);
	    }
	    tryConstFold = false;

	  }

	}
	  
      }

    }

    else if(I->getOpcode() == Instruction::Add || I->getOpcode() == Instruction::Sub || I->getOpcode() == Instruction::And || I->getOpcode() == Instruction::Or) {

      tryConstFold = (!tryFoldPtrAsIntOp(SI, Improved)) && (!tryFoldBitwiseOp(SI, Improved));
	    
    }

    else {

      tryConstFold = true;

    }

    if(tryConstFold) {

      SmallVector<Constant*, 4> instOperands;

      for(unsigned i = 0, ilim = I->getNumOperands(); i != ilim; i++) {
	ShadowValue op = SI->getOperand(i);
	if(Constant* C = getConstReplacement(op))
	  instOperands.push_back(C);
	else {
	  LPDEBUG("Not constant folding yet due to non-constant argument " << itcache(op) << "\n");
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
	  Improved = ShadowValue(newConst);
	}
	else {
	  Improved = ShadowValue();
	}
      }

    }

  }

  return Improved;

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

void IntegrationAttempt::tryEvaluate(ShadowInstruction* SI) {

  ShadowValue Improved = tryEvaluateResult(SI);
 
  if((!Improved.isInval()) && shouldForwardValue(Improved)) {
    
    SI->i.replaceWith = Improved;

    if(ShadowInstruction* ImpSI = Improved.getInst()) {

      if(std::find(ImpSI->indirectUsers.begin(), ImpSI->indirectUsers.end(), SI) == ImpSI->indirectUsers.end())
	ImpSI->indirectUsers.push_back(SI);

    }

  }

}

void InlineAttempt::tryEvaluateArg(ShadowArg* SA) {

  ShadowValue& copy = CI->getCallArgOperand(SA->invar->A->getArgNo());
  ShadowValue Repl = getReplacement(copy);
  if(shouldForwardValue(Repl))
    SA->i.replaceWith = Repl;
  copyBaseAndOffset(copy, SA);

}

void IntegrationAttempt::checkLoad(ShadowInstruction* LI) {

  ShadowValue Result = tryForwardLoad(LI);
  if(!Result.isInval())
    LI->i.replaceWith = Result;

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

