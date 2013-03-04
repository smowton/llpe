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

PointerBase& PointerBase::insert(ImprovedVal& V) {

  if(Overdef)
    return *this;
  if(std::count(Values.begin(), Values.end(), V))
    return *this;

  // Pointer merge: if either the new val or any of our own are vague pointers
  // to object X, any exact pointers to X should be merged in.
  // Further, if we're about to become oversized and we contain more than one exact
  // pointer to X, merge them into a vague one.

  if(type == ValSetTypePB) {

    bool doMerge = false;

    if(Values.size() + 1 > PBMAX)
      doMerge = true;
    
    if(V.Offset == LLONG_MAX)
      doMerge = true;

    if(!doMerge) {

      for(unsigned i = 0; i < Values.size(); ++i) {

	if(Values[i].V == V.V && Values[i].Offset == LLONG_MAX)
	  doMerge = true;

      }

    }

    if(doMerge) {

      for(SmallVector<ImprovedVal, 1>::iterator it = Values.end(), endit = Values.begin(); it != endit; --it) {

	ImprovedVal& ThisV = *(it - 1);
	if(ThisV.V == V.V)
	  Values.erase(it);

      }

      if(Values.size() + 1 > PBMAX)
	setOverdef();
      else
	Values.push_back(ImprovedVal(V.V, LLONG_MAX));

      return *this;

    }

  }

  if(Values.size() + 1 > PBMAX) {
    setOverdef();
  }
  else {
    Values.push_back(V);
  }

  return *this;

}

bool IntegrationAttempt::openCallSucceeds(Value* V) {

  return forwardableOpenCalls[cast<CallInst>(V)]->success;

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

bool InlineAttempt::isOptimisticPeel() {
  
  return false;

}

bool PeelIteration::isOptimisticPeel() {

  return !!(parentPA->OptimisticEdge.first);

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

// If finalise is false, we're in the 'incremental upgrade' phase: PHIs and selects take on
// the newest result of their operands.
// If finalise is true, we're in the 'resolution' phase: they take on their true value.
// e.g. in phase 1, PHI(def, undef) = def, in phase 2 it is overdef.
bool IntegrationAttempt::tryEvaluateMerge(ShadowInstruction* I, bool finalise, PointerBase& NewPB) {

  // The case for a resolved select instruction is already resolved.

  bool verbose = false;
  
  SmallVector<ShadowValue, 4> Vals;
  if(inst_is<SelectInst>(I)) {

    Vals.push_back(SI->getOperand(1));
    Vals.push_back(SI->getOperand(2));

  }
  else if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {

    if(CI->getType()->isVoidTy())
      return false;

    if(InlineAttempt* IA = getInlineAttempt(CI)) {

      IA->getLiveReturnVals(Vals);

    }
    else {
      return false;
    }

  }
  else {

    // I is a PHI node, but not a header PHI.
    ShadowInstructionInvar* SII = I->invar;

    for(uint32_t i = 0, ilim = SII->preds.size(); i != ilim && !breaknow; i+=2) {

      SmallVector<ShadowValue, 1> predValues;
      ShadowValue PredV = getExitPHIOperands(SI, i, predValues);

      for(SmallVector<ShadowValue, 1>::iterator it = predValues.begin(), it2 = predValues.end(); it != it2 && !breaknow; ++it) {

	Vals.push_back(*it);

      }

    }

  }

  bool anyInfo = false;

  if(verbose) {

    errs() << "=== START MERGE for " << itcache(*I) << " (finalise = " << finalise << ")\n";

    IntegrationAttempt* PrintCtx = this;
    while(PrintCtx) {
      errs() << PrintCtx->getShortHeader() << ", ";
      PrintCtx = PrintCtx->parent;
    }
    errs() << "\n";

  }

  for(SmallVector<ShadowValue, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2 && !NewPB.Overdef; ++it) {
    
    PointerBase VPB;
    if(!getPointerBase(*it, VPB)) {
      if(verbose)
	errs() << "Predecessor " << itcache(*it) << " undefined\n";
      if(finalise) {
	NewPB = PointerBase::getOverdef();
	if(verbose)
	  errs() << "=== END PHI MERGE\n";
	return true;
      }
      else
	continue;
    }

    if(verbose) {
      errs() << "Predecessor " << itcache(make_vc(V, VCtx)) << " defined by ";
      printPB(errs(), VPB, false);
      errs() << "\n";
    }

    anyInfo = true;
    NewPB.merge(VPB);

  }

  if(verbose)
    errs() << "=== END PHI MERGE\n";

  return anyInfo;

}

ShadowValue PeelIteration::getLoopHeaderForwardedOperand(ShadowInstruction* SI) {

  PHINode* PN = cast_inst<PHINode>(SI);
  // PHI node operands go value, block, value, block, so 2*value index = operand index.

  if(iterationCount == 0) {

    LPDEBUG("Pulling PHI value from preheader\n");
    // Can just use normal getOperand/replacement here.
    int predIdx = PN->getBasicBlockIndex(L->getLoopPreheader());
    assert(predIdx >= 0 && "Failed to find preheader block");
    op = SI->getOperand(predIdx * 2);

  }
  else {

    LPDEBUG("Pulling PHI value from previous iteration latch\n");
    int predIdx = PN->getBasicBlockIndex(L->getLoopLatch());
    assert(predIdx >= 0 && "Failed to find latch block");
    // Find equivalent instruction in previous iteration:
    IntegrationAttempt* prevIter = parentPA->getIteration(iterationCount - 1);
    ShadowInstIdx& SII = SI->invar->operandIdxs[predIdx * 2];
    if(SII.blockIdx != INVALID_BLOCK_IDX)
      op = ShadowValue(prevIter->getInst(SII.blockIdx, SII.instIdx));
    else
      op = SI->getOperand(predIdx * 2);

  }

}


bool IntegrationAttempt::tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, PointerBase& result) {

  return false;

}

bool PeelIteration::tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, PointerBase& result) {

  PHINode* PN = cast_inst<PHINode>(SI);
  bool isHeaderPHI = PN->getParent() == L->getHeader();

  if(isHeaderPHI) {

    ShadowValue predValue = getLoopHeaderForwardedOperand(SI, predValue);
    resultValid = getPointerBase(predValue, result);
    return true;

  }
  // Else, not a header PHI.
  return false;

}

void IntegrationAttempt::getOperandRising(ShadowInstructionInvar* SI, ShadowBBInvar* ExitedBB, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB* 1>& BBs) {

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
	Iter->getOperandRising(SI, ExitedBB, ops, BBs);

      }

      return;

    }

  }

  // Value is local, or in a child loop which is unterminated or entirely unexpanded.
  if(!edgeIsDead(SI->parent, ExitedBB)) {
    ops.push_back(getInst(SI));
    BBs.push_back(getBB(ExitedBB));
  }

}

void IntegrationAttempt::getExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB* 1>& BBs) {

  ShadowInstructionInvar* SII = SI->invar;
  
  ShadowInstIdx valOp = SII->preds[i];
  ShadowInstIdx blockOp = SII->preds[i+1];

  assert(blockOp.blockIdx != INVALID_BLOCK_IDX);

  // PHI arg is an instruction?
  if(valOp.blockIdx != INVALID_BLOCK_IDX && valOp.instIdx != INVALID_INST_IDX) {

    // PHI arg at child scope?
    ShadowInstructionInvar* PredSII = getInstInvar(valOp.blockIdx, valOp.instIdx);
    if(!((!PredSII->scope) || PredSII->scope->contains(L))) {

      getOperandRising(PredSII, SII->parent, ops, BBs);
      return;

    }

  }
  
  // Arg is local or a constant or argument, use normal getOperand.
  ShadowBBInvar* BB = getBBInvar(blockOp.blockIdx);
  if(!edgeIsDead(BB, SI->parent->invar)) {
    ops.push_back(SI->getOperand(valOpIdx));
    BBs.push_back(getBB(BB));
  }

}

static ShadowValue getOpenCmpResult(CmpInst* CmpI, ConstantInt* CmpInt, bool flip) {

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
bool IntegrationAttempt::tryFoldOpenCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved) {

  CmpInst* CmpI = cast_inst<CmpInst>(SI->invar->I);

  if(Ops[0].first != ValSetTypeFD && Ops[1].first != ValSetTypeFD)
    return false;

  bool flip;
  bool exists;
  ConstantInt* CmpInt = 0;
  ShadowValue& op0 = Ops[0].second.V;
  ShadowValue& op1 = Ops[1].second.V;
  ShadowInstruction* op0I = op0.getInst();
  ShadowInstruction* op1I = op1.getInst();

  if(op0I && Ops[0].first == ValSetTypeFD) {
    flip = false;
    exists = op0I->parent->IA->openCallSucceeds(op0I->invar->I);
    CmpInt = dyn_cast_or_null<ConstantInt>(op1.getVal());
  }
  else if(op1I && Ops[1].first == ValSetTypeFD) {
    flip = true;
    exists = op1I->parent->IA->openCallSucceeds(op1I->invar->I);
    CmpInt = dyn_cast_or_null<ConstantInt>(op0.getVal());
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
      Improved.V = ShadowValue(ConstantFoldCompareInstOperands(CmpI->getPredicate(), Arg0, Arg1, TD));
      ImpType = ValSetTypeScalar;

    }
    else {

      Improved.V = getOpenCmpResult(CmpI, CmpInt, flip);
      ImpType = ValSetTypeScalar;
      if(Improved.first) {
	LPDEBUG("Comparison against file descriptor resolves to " << itcache(Improved.V) << "\n");
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

bool IntegrationAttempt::tryFoldNonConstCmp(ShadowInst* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved) {

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

  Constant* Op0C = dyn_cast_or_null<Constant>(Ops[0].second.V);
  Constant* Op1C = dyn_cast_or_null<Constant>(Ops[1].second.V);
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

  ImpType = ValSetTypeScalar;

  switch(Pred) {
  default:
    break;
  case CmpInst::ICMP_UGT:
    // Never u> ~0
    if(Op1CI && Op1CI->isAllOnesValue()) {
      Improved.V = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_UGE:
    // Always u>= 0
    if(Op1C->isNullValue()) {
      Improved.V = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_ULT:
    // Never u< 0
    if(Op1C->isNullValue()) {
      Improved.V = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_ULE:
    // Always u<= ~0
    if(Op1CI && Op1CI->isAllOnesValue()) {
      Improved.V = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SGT:
    // Never s> maxint
    if(Op1CI && Op1CI->isMaxValue(true)) {
      Improved.V = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SGE:
    // Always s>= minint
    if(Op1CI && Op1CI->isMinValue(true)) {
      Improved.V = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SLT:
    // Never s< minint
    if(Op1CI && Op1CI->isMinValue(true)) {
      Improved.V = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      return true;
    }
    break;
  case CmpInst::ICMP_SLE:
    // Always s<= maxint
    if(Op1CI && Op1CI->isMaxValue(true)) {
      Improved.V = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      return true;     
    }
    break;
  }

  ImpType = ValSetTypeUnknown;
  return false;

}

// Return value as above: true for "we've handled it" and false for "try constant folding"
bool IntegrationAttempt::tryFoldPointerCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved) {

  CmpInst* CmpI = cast_inst<CmpInst>(SI);

  // Need scalars or pointers throughout:
  if((Ops[0].first != valSetTypeScalar && Ops[0].first != valSetTypePB) || (Ops[1].first != valSetTypeScalar && Ops[1].first != valSetTypePB))
    return false;

  // Check for special cases of pointer comparison that we can understand:

  ShadowValue& op0 = Ops[0].second.V;
  ShadowValue& op1 = Ops[1].second.V;

  Constant* op0C = dyn_cast_or_null<Constant>(op0.getVal());
  Constant* op1C = dyn_cast_or_null<Constant>(op1.getVal());

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
  else if(op0.getType()->isPointerTy() && isGlobalIdentifiedObject(op0))
    op0Arg = one;
  
  if(op1C && op1C->isNullValue())
    op1Arg = zero;
  else if(op1.getType()->isPointerTy() && isGlobalIdentifiedObject(op1))
    op1Arg = one;

  if(op0Arg && op1Arg && (op0Arg == zero || op1Arg == zero)) {
    
    ImpType = ValSetTypeScalar;
    Improved = ShadowValue(ConstantFoldCompareInstOperands(CmpI->getPredicate(), op0Arg, op1Arg, this->TD));
    return true;   

  }

  // Only instructions that ultimately refer to pointers from here on

  if(Ops[0].first != ValSetTypePB || Ops[1].first != ValSetTypePB)
    return false;

  // 2. Comparison of pointers with a common base:

  if(op0 == op1) {

    // Can't make progress if either pointer is vague:
    if(Ops[0].second.Offset == LLONG_MAX || Ops[1].second.Offset == LLONG_MAX)
      return false;
    
    // Always do a signed test here, assuming that negative indexing off a pointer won't wrap the address
    // space and end up with something large and positive.

    op0Arg = ConstantInt::get(I64, Ops[0].second.Offset);
    op1Arg = ConstantInt::get(I64, Ops[1].second.Offset);
    ImpType = ValSetTypeScalar;
    Improved.V = ShadowValue(ConstantFoldCompareInstOperands(getSignedPred(CmpI->getPredicate()), op0Arg, op1Arg, this->TD));
    return true;

  }

  // 3. Restricted comparison of pointers with a differing base: we can compare for equality only
  // as we don't know memory layout at this stage.

  if(isGlobalIdentifiedObject(op0) && isGlobalIdentifiedObject(op1) && op0 != op1) {

    // This works regardless of the pointers' offset values.

    if(CmpI->getPredicate() == CmpInst::ICMP_EQ) {
      Improved.V = ShadowValue(ConstantInt::getFalse(CmpI->getContext()));
      ImpType = ValSetTypeScalar;
      return true;
    }
    else if(CmpI->getPredicate() == CmpInst::ICMP_NE) {
      Improved.V = ShadowValue(ConstantInt::getTrue(CmpI->getContext()));
      ImpType = ValSetTypeScalar;
      return true;
    }

  }

  return false;

}

bool IntegrationAttempt::tryFoldPtrAsIntOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved) {

  Instruction* BOp = SI->invar->I;

  if(!SI->getType()->isIntegerTy())
    return false;

  if(BOp->getOpcode() != Instruction::Sub && BOp->getOpcode() != Instruction::And && BOp->getOpcode() != Instruction::Add)
    return false;

  bool Op0Ptr = Ops[0].first == ValSetTypePB;
  bool Op1Ptr = Ops[1].first == ValSetTypePB;

  if((!Op0Ptr) && (!Op1Ptr))
    return false;
  
  if(BOp->getOpcode() == Instruction::Sub) {

    if(Op0Ptr) {

      ConstantInt* Op1I = dyn_cast_or_null<ConstantInt>(Ops[1].second.V.getVal());

      ImpType = ValSetTypePB;
      Improved.V = Ops[0].second.V;
      if(Ops[0].second.Offset == LLONG_MAX || !Op1I)
	Improved.Offset = LLONG_MAX;
      else
	Improved.Offset = Ops[0].second.Offset - Op1I->getSExtValue();

      return true;

    }

    else if(Op0Ptr && Op1Ptr && Ops[0].second.V == Ops[1].second.V) {

      // Subtracting pointers with a common base.
      if(Ops[0].second.Offset != LLONG_MAX && Ops[1].second.Offset != LLONG_MAX) {
	ImpType = ValSetTypeScalar;
	Improved = ShadowValue(ConstantInt::getSigned(BOp->getType(), Ops[0].second.Offset - Ops[1].second.Offset));
	return true;
      }

    }

  }
  else if(BOp->getOpcode() == Instruction::Add) {

    if(Op0Ptr && Op1Ptr)
      return false;
    
    std::pair<ValSetType, ImprovedVal>& PtrV = Op0Ptr ? Ops[0].second : Ops[1].second;
    ConstantInt* NumC = dyn_cast_or_null<ConstantInt>(Op0Ptr ? Ops[1].second.V.getVal() : Ops[0].second.V.getVal());

    ImpType = ValSetTypePB;
    Improved.V = PtrV.second.V;
    if(PtrV.second.Offset == LLONG_MAX || !NumC)
      Improved.Offset = LLONG_MAX;
    else
      Improved.Offset = PtrV.second.Offset + NumC->getSExtValue();
    
    return true;

  }
  else if(BOp->getOpcode() == Instruction::And) {

    // Common technique to discover a pointer's alignment -- and it with a small integer.
    // Answer if we can.

    if((!Op0Ptr) || Op1Ptr)
      return false;

    ConstantInt* MaskC = dyn_cast_or_null<ConstantInt>(Ops[1].second.V.getVal());
    if(!MaskC)
      return false;

    if(Ops[0].second.Offset == LLONG_MAX || Ops[0].second.Offset < 0)
      return false;

    uint64_t UOff = (uint64_t)Ops[0].second.Offset;

    // Try to get alignment:

    unsigned Align = 0;
    if(GlobalValue* GV = dyn_cast_or_null<GlobalValue>(Ops[0].second.V.getVal()))
      Align = GV->getAlignment();
    else if(ShadowInstruction* SI = Ops[0].second.V.getInst()) {
      
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
      
      ImpType = ValSetTypeScalar;
      Improved.V = ShadowValue(ConstantInt::get(BOp->getType(), Mask & UOff));
      return true;

    }

  }

  return false;

}

 bool IntegrationAttempt::tryFoldBitwiseOp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved) {
   
  Instruction* BOp = SI->invar->I;

  switch(BOp->getOpcode()) {
  default:
    return false;
  case Instruction::And:
  case Instruction::Or:
    break;
  }

  if(Ops[0].first != ValSetTypeScalar || Ops[1].first != ValSetTypeScalar)
    return false;

  Constant* Op0C = cast<Constant>(Ops[0].second.V.getVal());
  Constant* Op1C = cast<Constant>(Ops[1].second.V.getVal());

  if(BOp->getOpcode() == Instruction::And) {

    if((Op0C && Op0C->isNullValue()) || (Op1C && Op1C->isNullValue())) {

      ImpType = ValSetTypeScalar;
      Improved.V = ShadowValue(Constant::getNullValue(BOp->getType()));
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

      ImpType = ValSetTypeScalar;
      Improved.V = ShadowValue(Constant::getAllOnesValue(BOp->getType()));
      return true;

    }

  }

  return false;

}

bool IntegrationAttempt::tryEvaluateResult(ShadowInstruction* SI, 
					   std::pair<ValSetType, ImprovedVal>* Ops, 
					   ValSetType& ImpType, ImprovedVal& Improved) {
  
  Instruction* I = SI->invar->I;


  if(inst_is<AllocaInst>(SI) || isNoAliasCall(SI->invar->I)) {

    ImpType = ValSetTypePB;
    Improved.V = ShadowValue(SI);
    Improved.Offset = 0;
    return true;
      
  }

  // Try a special case for forwarding FDs: they can be passed through any cast preserving 32 bits.
  // We optimistically pass vararg cookies through all casts.
  else if(inst_is<CastInst>(SI)) {

    CastInst* CI = cast_inst<CastInst>(SI);
    const Type* SrcTy = CI->getSrcTy();
    const Type* DestTy = CI->getDestTy();
	
    if(Ops[0].first == ValSetTypeFD) {
      if(!((SrcTy->isIntegerTy(32) || SrcTy->isIntegerTy(64) || SrcTy->isPointerTy()) &&
	   (DestTy->isIntegerTy(32) || DestTy->isIntegerTy(64) || DestTy->isPointerTy()))) {

	return false;

      }
    }

    if(Ops[0].first != ValSetTypeScalar) {

      // Pass FDs, pointers, vararg cookies through. This includes ptrtoint and inttoptr.
      ImpType = Ops[0].first;
      Improved = Ops[0].second;
      return ImpType != ValSetTypeUnknown;

    }

    // Otherwise pass scalars through the normal constant folder.

  }

  if(CmpInst* CmpI = dyn_cast<CmpInst>(I)) {

    if(tryFoldOpenCmp(SI, Ops, ImpType, Improved))
      return ImpType != ValSetTypeUnknown;
    if(tryFoldPointerCmp(SI, Ops, ImpType, Improved))
      return ImpType != ValSetTypeUnknown;
    if(tryFoldNonConstCmp(SI, Improved))
      return ImpType != ValSetTypeUnknown;

    // Otherwise fall through to normal const folding.

  }

  else if(GetElementPtrInst* GEP = dyn_cast<GetElementPtrInst>(I)) {

    if(Ops[0].first == ValSetTypePB) {

      ImpType = ValSetTypePB;
      Improved = Ops[0].second;

      if(Improved.Offset != LLONG_MAX) {

	// Bump base by amount indexed by GEP:
	gep_type_iterator GTI = gep_type_begin(GEP);
	for (uint32_t i = 1, ilim = SI->getNumOperands(); i != ilim; ++i, ++GTI) {
      
	  if(Ops[i].first != ValSetTypeScalar) {
	    // Uncertain
	    Improved.Offset = LLONG_MAX;
	    break;
	  }
	  else {
	    Constant* OpC = cast<Constant>(Ops[i].second.V);
	    if (OpC->isZero()) continue;
	    // Handle a struct and array indices which add their offset to the pointer.
	    if (const StructType *STy = dyn_cast<StructType>(*GTI)) {
	      Improved.Offset += GlobalTD->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
	    } else {
	      uint64_t Size = GlobalTD->getTypeAllocSize(GTI.getIndexedType());
	      Improved.Offset += OpC->getSExtValue()*Size;
	    }
	  }
	}

      }

      return true;

    }
    else if(Ops[0].first == ValSetTypeVarArg) {
	
      if(SI->getNumOperands() == 2) {

	if(Ops[1].first != ValSetTypeScalar)
	  return false;
	ConstantInt* CI = cast_val<ConstantInt>(Ops[1].second.V);

	InlineAttempt* calledIA = Ops[0].second.V.getInst()->parent->getFunctionRoot();
	Function* calledF = calledIA->getFunction();

	uint64_t GEPOff = CI->getLimitedValue();
	assert(GEPOff % 8 == 0);
	GEPOff /= 8;

	int64_t newVaArg = -1;
	switch(Ops[0].second.getVaArgType()) {
	case va_arg_type_baseptr:
	  // This is indexing off the frame base pointer.
	  // Determine which zone it's in:
	  if(GEPOff < 6) {
	    // Non-FP zone:
	    newVaArg = GEPOff - (getInitialBytesOnStack(calledF) / 8);
	  }
	  else if(GEPOff >= 6 && GEPOff < 22) {
	    newVaArg = (((GEPOff - 6) / 2) - (getInitialFPBytesOnStack(calledF) / 16)) + ImprovedVal::first_fp_arg;
	  }
	  else {
	    newVaArg = ShadowValue::not_va_arg;
	  }
	  break;
	case va_arg_type_fp:
	case va_arg_type_nonfp:
	  assert(GEPOff == 1);
	  // In the spilled zone. Find the next spilled argument:
	  newVaArg = calledIA->getSpilledVarargAfter(Base.va_arg);
	  break;
	default:
	  assert(0);
	}

	if(newVaArg != ImprovedVal::not_va_arg) {
	  ImpType = ValSetTypeVarArg;
	  Improved.V = Ops[0].second.V;
	  Improved.Offset = newVaArg;
	  return true;
	}

      }

    }

    // Else GEP off an unknown value, or off a constant of some sort, or a failure above...
    return false;
	  
  }

  else if(I->getOpcode() == Instruction::Add || I->getOpcode() == Instruction::Sub || I->getOpcode() == Instruction::And || I->getOpcode() == Instruction::Or) {

    if(tryFoldPtrAsIntOp(SI, Ops, ImpType, Improved))
      return true;
    if(tryFoldBitwiseOp(SI, Ops, ImpType, Improved))
      return true;
	    
  }

  // Try ordinary constant folding?

  SmallVector<Constant*, 4> instOperands;

  for(unsigned i = 0, ilim = I->getNumOperands(); i != ilim; i++) {

    if(Ops[i].first != ValSetTypeScalar)
      return false;
    instOperands.push_back(cast<Constant>(Ops[i].second.V.getVal()));

  }

  Constant* newConst = 0;

  if (const CmpInst *CI = dyn_cast<CmpInst>(I))
    newConst = ConstantFoldCompareInstOperands(CI->getPredicate(), instOperands[0], instOperands[1], this->TD);
  else if(isa<LoadInst>(I))
    newConst = ConstantFoldLoadFromConstPtr(instOperands[0], this->TD);
  else
    newConst = ConstantFoldInstOperands(I->getOpcode(), I->getType(), instOperands.data(), I->getNumOperands(), this->TD, /* preserveGEPSign = */ true);

  if(newConst) {
    LPDEBUG(itcache(*I) << " now constant at " << itcache(*newConst) << "\n");
    ImpType = ValSetTypeScalar;
    Improved.V = ShadowValue(newConst);
  }
  
  return !!newConst;

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

std::pair<ValSetType, ImprovedVal> llvm::getValPB(Value* V) {

  Constant* C = dyn_cast<Constant>(V);
  if(C)
    return std::make_pair(ValSetTypeUnknown, ImprovedVal());

  if(ConstantExpr* CE = dyn_cast<ConstantExpr>(C)) {

    switch(CE->getOpcode()) {

    case Instruction::PtrToInt:
    case Instruction::IntToPtr:
    case Instruction::SExt:
    case Instruction::ZExt:
      return getValPB(CE->getOperand(0));
    case Instruction::GetElementPtr:

      {

	std::pair<ValSetType, ImprovedVal> BasePB = getValPB(CE->getOperand(0));

	if(BasePB.first != ValSetTypePB)
	  return std::make_pair(ValSetTypeUnknown, ImprovedVal());
	if(BasePB.second.Offset == LLONG_MAX)
	  return BasePB;

	int64_t Offset;

	gep_type_iterator GTI = gep_type_begin(GEP);
	for (User::op_iterator I = GEP->idx_begin(), E = GEP->idx_end(); I != E;
	     ++I, ++GTI) {
	  ConstantInt* OpC = cast<ConstantInt>(*I);
	  if (OpC->isZero()) continue;
    
	  // Handle a struct and array indices which add their offset to the pointer.
	  if (const StructType *STy = dyn_cast<StructType>(*GTI)) {
	    Offset += GlobalTD->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
	  } else {
	    uint64_t Size = GlobalTD->getTypeAllocSize(GTI.getIndexedType());
	    Offset += OpC->getSExtValue()*Size;
	  }
	}
  
	return std::make_pair(ValSetTypePB, ImprovedVal(BasePB.second.V, BasePB.second.Offset + Offset);

      }
  
    case Instruction::Add:
    case Instruction::Sub:
      {

	std::pair<ValSetType, ImprovedVal> Op1 = getValPB(CE->getOperand(0));
	std::pair<ValSetType, ImprovedVal> Op2 = getValPB(CE->getOperand(1));

	if(Op1.first == ValSetTypeUnknown || Op2.first == ValSetTypeUnknown)
	  return std::make_pair(ValSetTypeUnknown, ShadowValue());

	if(Op1.first == ValSetTypeScalar && Op2.first == ValSetTypeScalar) {

	  if(CE->getOpcode() == Instruction::Add)
	    return constPtrAsInt(ConstantExpr::getAdd(cast<Constant>(Op1.second.V), cast<Constant>(Op2.second.V)));
	  else
	    return constPtrAsInt(ConstantExpr::getSub(cast<Constant>(Op1.second.V), cast<Constant>(Op2.second.V)));

	}

	if(CE->getOpcode() == Instruction::Add) {

	  if(Op2.first == ValSetTypePB)
	    std::swap(Op1, Op2);

	  if(Op2.first == ValSetTypePB) // Can't add 2 pointers
	    return std::make_pair(ValSetTypeUnknown, ImprovedVal());

	  if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.second.V))
	    return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, Op1.second.Offset + Op2C->getLimitedValue()));
	  else
	    return std::make_pair(ValSetTypePB, ImprovedVal(Op1.second.V, LLONG_MAX));

	}
	else {
	
	  if(Op1.first == ValSetTypePB) {
	  
	    if(Op2.first == ValSetTypePB) {
	    
	      if(Op1.second.V == Op2.second.V) {

		if(Op1.second.Offset == LLONG_MAX || Op2.second.Offset == LLONG_MAX)
		  return std::make_pair(ValSetTypeUnknown, ShadowValue());
		else
		  return std::make_pair(ValSetTypeScalar, 
					ImprovedValue(ShadowValue(ConstantInt::get(Type::getInt64Ty(CE->getContext()))), 
						      Op1.second.Offset - Op2.second.Offset));
	      
	      }
	      // Else can't subtract 2 pointers with differing bases

	    }
	    else {

	      if(Op1.second.Offset == LLONG_MAX)
		return Op1;
	      if(ConstantInt* Op2C = dyn_cast<ConstantInt>(Op2.second.V))
		return std::make_pair(ValSetTypePB, ShadowValue(Op1.second.V, Op1.second.Offset - Op2C->getLimitedValue()));
	      else
		return std::make_pair(ValSetTypePB, ShadowValue(Op1.second.V));

	    }
	  
	  }
	
	}

	// Fall through to default

      }	

    default:
      return std::make_pair(ValSetTypeUnknown, ShadowValue());

    }

  }
  else if(isa<GlobalVal>(C)) {
    
    return std::make_pair(ValSetTypePB, ShadowValue(C));

  }
  else {

    return std::make_pair(ValSetTypeScalar, ShadowValue(C));

  }

}

bool IntegrationAttempt::tryEvaluateOrdinaryInst(ShadowInstruction* SI, PointerBase& NewPB, std::pair<ValSetType, ImprovedVal>* Ops, uint32_t OpIdx) {

  if(OpIdx == SI->getNumOperands()) {

    ValSetType ThisVST;
    ShadowValue ThisV;
    if(!tryEvaluateResult(SI, Ops, ThisVST, ThisV)) {

      NewPB.setOverdef();
      return true;

    }
    else {

      PointerBase ThisPB(ThisVST);
      ThisPB.insert(ThisV);
      NewPB.merge(ThisPB);
      return true;

    }

  }

  // Else queue up the next operand:

  ShadowValue OpV = SI->getOperand(OpIdx);
  if(Value* V = OpV.getVal()) {

    Ops[OpIdx] = getValPB(V);
    return tryEvaluateOrdinaryInst(SI, NewPB, Ops, OpIdx+1);

  }
  else {

    PointerBase ArgPB;
    bool ArgPBValid = getPointerBase(OpV, ArgPB);
    if((!ArgPBValid) || ArgPB.Overdef) {
      Ops[OpIdx].first = ValSetTypeUnknown;
      Ops[OpIdx].second.V = ShadowValue();
      return tryEvaluateOrdinaryInst(SI, NewPB, Ops, OpIdx+1);
    }
    else {
      
      Ops[OpIdx].first = ArgPB.type;
      for(uint32_t i = 0; i < ArgPB.Values.size(); ++i) {
	
	Ops[OpIdx].second = ArgPB.Values[i];
	tryEvaluateOrdinaryInst(SI, NewPB, Ops, OpIdx+1);
	if(NewPB.Overdef)
	  break;
	
      }

      return true;

    }

  }

}

bool IntegrationAttempt::tryEvaluateOrdinaryInst(ShadowInstruction* SI, PointerBase& NewPB) {

  std::pair<ValSetType, ImprovedVal> Ops[SI->getNumOperands()];
  return tryEvaluateOrdinaryInst(SI, NewPB, 0);

}

bool IntegrationAttempt::getNewPB(ShadowInstruction* SI, bool finalise, PointerBase& NewPB, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA) {

  // Special case the merge instructions:
  bool tryMerge = false;
 
  switch(I->getOpcode()) {
    
  case Instruction::Load:
    return tryForwardLoadPB(SI, finalise, NewPB, CacheThresholdBB, CacheThresholdIA);
  case Instruction::PHI:
    {
      bool Valid;
      if(tryEvaluateHeaderPHI(SI, Ops, Valid, ImpType, Improved))
	return Valid;
      tryMerge = true;
      break;
    }
  case Instruction::Select:
    Constant* Cond = getConstReplacement(Ops[0].second);
    if(Cond) {
      if(cast<ConstantInt>(Cond)->isZero()) {
	Improved = Ops[2].second;
	ImpType = Ops[2].first;
      }
      else {
	Improved = Ops[1].second;
	ImpType = Ops[1].first;
      }
      return ImpType != ValSetTypeUnknown;
    }
    else {
      tryMerge = true;
    }
    break;
  case Instruction::Call:
    tryMerge = true;
    break;
  default:
    break;

  }

  if(tryMerge) {

    return tryEvaluateMerge(SI, finalise, NewPB);

  }
  else {

    return tryEvaluateOrdinaryInst(SI, NewPB);

  }

}

bool InlineAttempt::getArgBasePointer(Argument* A, PointerBase& OutPB) {

  if(!parent)
    return false;
  ShadowValue Arg = CI->getCallArgOperand(SA->invar->A->getArgNo());
  return getPointerBase(Arg, OutPB);

}

bool IntegrationAttempt::tryEvaluate(ShadowValue V, bool finalise, LoopPBAnalyser* LPBA, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA) {

  Instruction* I = SI->invar->I;

  PointerBase OldPB;
  bool OldPBValid = getPointerBase(SI, OldPB);

  // Getting no worse:
  if(finalise && LPBA && ((!OldPBValid) || OldPB.Overdef))
    return false;

  PointerBase NewPB;
  bool NewPBValid;

  if(ShadowArg* SA = V.getArg()) {

    InlineAttempt* IA = getFunctionRoot();
    NewPBValid = IA->getArgBasePointer(SA->invar->A, NewPB);

  }
  else {

    NewPBValid = getNewPB(SI, NewPB);

  }

  if(!NewPBValid)
    return false;

  release_assert(NewPB.Overdef || (NewPB.Type != ValSetTypeUnknown));

  if((!OldPBValid) || OldPB != NewPB) {

    if(ShadowInstruction* I = V.getInst()) {
      if(!inst_is<LoadInst>(I)) {
	std::string RStr;
	raw_string_ostream RSO(RStr);
	printPB(RSO, NewPB, true);
	RSO.flush();
	if(!finalise)
	  optimisticForwardStatus[I->invar->I] = RStr;
	else
	  pessimisticForwardStatus[I->invar->I] = RStr;
      }
    }

    if(ShadowInstruction* SI = V.getInst()) {
      SI->i.PB = NewPB;
    }
    else {
      ShadowArg* SA = V.getArg();
      SA->i.PB = NewPB;
    }

    if(verbose) {
      errs() << "Updated dep to ";
      printPB(errs(), NewPB);
      errs() << "\n";
    }
  
    if(LPBA)
      queueUsersUpdatePB(V, LPBA);

    return true;

  }

}

namespace llvm {

  raw_ostream& operator<<(raw_ostream& Stream, const IntegrationAttempt& P) {

    P.describe(Stream);
    return Stream;

  }

}

