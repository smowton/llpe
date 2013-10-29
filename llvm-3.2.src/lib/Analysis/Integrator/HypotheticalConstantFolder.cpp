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
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include "llvm/DataLayout.h"

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

  if(parentPA->invarInfo->optimisticEdge.first == 0xffffffff)
    return true;

  return parentPA->allNonFinalIterationsDoNotExit();

}

bool InlineAttempt::isOptimisticPeel() {
  
  return false;

}

bool PeelIteration::isOptimisticPeel() {

  return parentPA->invarInfo->optimisticEdge.first != 0xffffffff;

}

bool IntegrationAttempt::tryEvaluateMerge(ShadowInstruction* I, ImprovedValSet*& NewPB) {

  // The case for a resolved select instruction has already been handled.

  SmallVector<ShadowValue, 4> Vals;
  if(inst_is<SelectInst>(I)) {

    Vals.push_back(I->getOperand(1));
    Vals.push_back(I->getOperand(2));

  }
  else if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {

    if(CI->getType()->isVoidTy())
      return false;

    if(InlineAttempt* IA = getInlineAttempt(I)) {

      IA->getLiveReturnVals(Vals);

    }
    else {

      return false;

    }

  }
  else {

    // I is a PHI node, but not a header PHI.
    ShadowInstructionInvar* SII = I->invar;

    for(uint32_t i = 0, ilim = SII->operandIdxs.size(); i != ilim; i++) {

      SmallVector<ShadowValue, 1> predValues;
      getExitPHIOperands(I, i, predValues);
      Vals.append(predValues.begin(), predValues.end());

    }

  }

  bool ret = getMergeValue(Vals, NewPB);
  ImprovedValSetSingle* NewIVS;
  if(NewPB && (NewIVS = dyn_cast<ImprovedValSetSingle>(NewPB)) && NewIVS->isWhollyUnknown()) {

    for(SmallVector<ShadowValue, 1>::iterator it = Vals.begin(), itend = Vals.end(); it != itend; ++it)
      valueEscaped(*it, I->parent);

  }

  return ret;

}

bool IntegrationAttempt::getMergeValue(SmallVector<ShadowValue, 4>& Vals, ImprovedValSet*& NewPB) {

  bool anyInfo = false;
  bool verbose = false;
  
  // For now, only support straight copying of multis; otherwise just return overdef.

  bool anyMultis = false;
  for(SmallVector<ShadowValue, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2; ++it) {

    switch(it->t) {
    case SHADOWVAL_ARG:
    case SHADOWVAL_INST:
      anyMultis |= isa<ImprovedValSetMulti>(getIVSRef(*it));
      break;
    default:
      break;
    }

  }

  if(anyMultis) {

    if(Vals.size() > 1)
      NewPB = newOverdefIVS();
    else
      NewPB = new ImprovedValSetMulti(*cast<ImprovedValSetMulti>(getIVSRef(Vals[0])));
    return true;

  }
  else {

    ImprovedValSetSingle* NewIVS = newIVS();
    NewPB = NewIVS;
  
    for(SmallVector<ShadowValue, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2 && !NewIVS->Overdef; ++it) {
    
      addValToPB(*it, *NewIVS);

    }

    if(verbose)
      errs() << "=== END PHI MERGE\n";

    return anyInfo;

  }

}

ShadowValue PeelIteration::getLoopHeaderForwardedOperand(ShadowInstruction* SI) {

  PHINode* PN = cast_inst<PHINode>(SI);

  // Careful here: this function is used during commit when loop structure can be temporarily
  // disrupted by cloning blocks (e.g. one might branch to the header pending remapping,
  // knocking out the preheader).

  if(iterationCount == 0) {

    LPDEBUG("Pulling PHI value from preheader\n");
    // Can just use normal getOperand/replacement here.
    ShadowBBInvar* PHBBI = getBBInvar(parentPA->invarInfo->preheaderIdx);
    int predIdx = PN->getBasicBlockIndex(PHBBI->BB);
    assert(predIdx >= 0 && "Failed to find preheader block");
    return SI->getOperand(predIdx);

  }
  else {

    LPDEBUG("Pulling PHI value from previous iteration latch\n");
    ShadowBBInvar* LBBI = getBBInvar(parentPA->invarInfo->latchIdx);
    int predIdx = PN->getBasicBlockIndex(LBBI->BB);
    assert(predIdx >= 0 && "Failed to find latch block");
    // Find equivalent instruction in previous iteration:
    IntegrationAttempt* prevIter = parentPA->getIteration(iterationCount - 1);
    ShadowInstIdx& SII = SI->invar->operandIdxs[predIdx];
    if(SII.blockIdx != INVALID_BLOCK_IDX)
      return ShadowValue(prevIter->getInst(SII.blockIdx, SII.instIdx));
    else
      return SI->getOperand(predIdx);

  }

}


bool IntegrationAttempt::tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSet*& result) {

  return false;

}

bool PeelIteration::tryEvaluateHeaderPHI(ShadowInstruction* SI, bool& resultValid, ImprovedValSet*& result) {

  PHINode* PN = cast_inst<PHINode>(SI);
  bool isHeaderPHI = PN->getParent() == L->getHeader();

  if(isHeaderPHI) {

    ShadowValue predValue = getLoopHeaderForwardedOperand(SI);
    resultValid = copyImprovedVal(predValue, result);
    return true;

  }
  // Else, not a header PHI.
  return false;

}

void IntegrationAttempt::getOperandRising(ShadowInstruction* SI, uint32_t valOpIdx, ShadowBBInvar* ExitingBB, ShadowBBInvar* ExitedBB, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs, bool readFromNonTerminatedLoop) {

  if(edgeIsDead(ExitingBB, ExitedBB))
    return;

  if(ExitingBB->naturalScope != L) {
    
    // Read from child loop if appropriate:
    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(L, ExitingBB->naturalScope))) {

      if(PA->isEnabled() && (readFromNonTerminatedLoop || PA->isTerminated())) {

	for(unsigned i = 0; i < PA->Iterations.size(); ++i) {

	  PeelIteration* Iter = PA->Iterations[i];
	  Iter->getOperandRising(SI, valOpIdx, ExitingBB, ExitedBB, ops, BBs, readFromNonTerminatedLoop);

	}

	if(PA->isTerminated())
	  return;

      }

    }

  }

  // Loop unexpanded or value local or lower:

  ShadowInstIdx valOp = SI->invar->operandIdxs[valOpIdx];
  ShadowValue NewOp;
  if(valOp.instIdx != INVALID_INSTRUCTION_IDX && valOp.blockIdx != INVALID_BLOCK_IDX)
    NewOp = getInst(valOp.blockIdx, valOp.instIdx);
  else
    NewOp = SI->getOperand(valOpIdx);

  ops.push_back(NewOp);
  if(BBs) {
    ShadowBB* NewBB = getBB(*ExitingBB);
    release_assert(NewBB);
    BBs->push_back(NewBB);
  }

}

void IntegrationAttempt::getExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs, bool readFromNonTerminatedLoop) {

  ShadowInstructionInvar* SII = SI->invar;
  ShadowBBInvar* BB = SII->parent;
  
  uint32_t blockIdx = SII->operandBBs[valOpIdx];

  assert(blockIdx != INVALID_BLOCK_IDX);

  ShadowBBInvar* OpBB = getBBInvar(blockIdx);

  if(OpBB->naturalScope != L && ((!L) || L->contains(OpBB->naturalScope)))
    getOperandRising(SI, valOpIdx, OpBB, BB, ops, BBs, readFromNonTerminatedLoop);
  else {

    // Arg is local (can't be lower or this is a header phi)
    if((!edgeIsDead(OpBB, BB)) && !shouldIgnoreEdge(OpBB, BB)) {
      ops.push_back(SI->getOperand(valOpIdx));
      if(BBs) {
	ShadowBB* NewBB = getBBFalling(OpBB);
	release_assert(NewBB);
	BBs->push_back(NewBB);
      }
    }

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

  CmpInst* CmpI = cast_inst<CmpInst>(SI);

  if(Ops[0].first != ValSetTypeFD && Ops[1].first != ValSetTypeFD)
    return false;

  bool flip;
  ConstantInt* CmpInt = 0;
  ValSetType CmpIntType;
  ShadowValue& op0 = Ops[0].second.V;
  ShadowValue& op1 = Ops[1].second.V;
  ShadowInstruction* op0I = op0.getInst();
  ShadowInstruction* op1I = op1.getInst();

  if(op0I && Ops[0].first == ValSetTypeFD) {
    flip = false;
    CmpInt = dyn_cast_or_null<ConstantInt>(op1.getVal());
    CmpIntType = Ops[1].first;
  }
  else if(op1I && Ops[1].first == ValSetTypeFD) {
    flip = true;
    CmpInt = dyn_cast_or_null<ConstantInt>(op0.getVal());
    CmpIntType = Ops[0].first;
  }
  else {
    return false;
  }

  if(CmpInt) {
    
    Improved.V = getOpenCmpResult(CmpI, CmpInt, flip);
    if(!Improved.V.isInval()) {
      LPDEBUG("Comparison against file descriptor resolves to " << itcache(Improved.V) << "\n");
      ImpType = ValSetTypeScalar;
    }
    else {
      LPDEBUG("Comparison against file descriptor inconclusive\n");
      ImpType = ValSetTypeOverdef;
    }

  }
  else {

    ImpType = CmpIntType == ValSetTypeUnknown ? ValSetTypeUnknown : ValSetTypeOverdef;

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

bool IntegrationAttempt::tryFoldNonConstCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved) {

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

  Constant* Op0C = dyn_cast_or_null<Constant>(Ops[0].second.V.getVal());
  Constant* Op1C = dyn_cast_or_null<Constant>(Ops[1].second.V.getVal());
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

static bool isIDOrConst(ShadowValue& op) {

  if(isGlobalIdentifiedObject(op))
    return true;

  if(val_is<ConstantPointerNull>(op))
    return true;

  if(ConstantExpr* CE = dyn_cast_val<ConstantExpr>(op))
    return CE->getOpcode() == Instruction::IntToPtr && isa<Constant>(CE->getOperand(0));

  return false;

}

static bool heapPointerAlreadyTested(ShadowValue& V, ShadowInstruction* TestI) {

  // For now, only deal with the common case that a heap object is allocated
  // and immediately tested in the same basic block.
  // If this situation is apparent, only that test needs to be checked at runtime;
  // if it can't, all heap pointer checks need repeating.

  // I know V is a heap allocation, therefore a call instruction.
  ShadowInstruction* I = V.getInst();
  ShadowBB* BB = I->parent;

  // This test is in the allocation block?
  if(TestI->parent == BB)
    return false;

  // Look for a comparison against null that follows the allocation:
  for(uint32_t i = I->invar->idx + 1, ilim = BB->insts.size(); i != ilim; ++i) {

    ShadowInstruction* ThisI = &BB->insts[i];
    if(inst_is<ICmpInst>(ThisI)) {

      ShadowValue Op0 = ThisI->getOperand(0);
      ShadowValue Op1 = ThisI->getOperand(1);

      if((val_is<ConstantPointerNull>(Op0) && Op1.isInst() && Op1.getInst() == I) ||
	 (val_is<ConstantPointerNull>(Op1) && Op0.isInst() && Op0.getInst() == I))
	return true;
      
    }

  }

  errs() << "Heap allocation " << itcache(V) << " does not appear to be locally tested and so all null comparisons will be checked\n";
  return false;

}

// Return value as above: true for "we've handled it" and false for "try constant folding"
bool IntegrationAttempt::tryFoldPointerCmp(ShadowInstruction* SI, std::pair<ValSetType, ImprovedVal>* Ops, ValSetType& ImpType, ImprovedVal& Improved, unsigned char* needsRuntimeCheck) {

  CmpInst* CmpI = cast_inst<CmpInst>(SI);

  // Need scalars or pointers throughout:
  if((Ops[0].first != ValSetTypeScalar && Ops[0].first != ValSetTypePB) || (Ops[1].first != ValSetTypeScalar && Ops[1].first != ValSetTypePB))
    return false;

  // Check for special cases of pointer comparison that we can understand:

  ShadowValue& op0 = Ops[0].second.V;
  ShadowValue& op1 = Ops[1].second.V;

  Constant* op0C = dyn_cast_or_null<Constant>(op0.getVal());
  Constant* op1C = dyn_cast_or_null<Constant>(op1.getVal());

  bool op0Fun = (op0C && isa<Function>(op0C->stripPointerCasts()));
  bool op1Fun = (op1C && isa<Function>(op1C->stripPointerCasts()));

  bool op0UGO = isGlobalIdentifiedObject(op0);
  bool op1UGO = isGlobalIdentifiedObject(op1);

  bool comparingHeapPointer = false;
  if(op0UGO && val_is<CallInst>(op0))
    comparingHeapPointer = true;
  else if(op1UGO && val_is<CallInst>(op1))
    comparingHeapPointer = true;

  // Don't check the types here because we need to accept cases like comparing a ptrtoint'd pointer
  // against an integer null. The code for case 1 works for these; all other cases require that both
  // values resolved to pointers.

  Type* I64 = Type::getInt64Ty(CmpI->getContext());
  Constant* zero = ConstantInt::get(I64, 0);
  Constant* one = ConstantInt::get(I64, 1);
  
  // 1. Comparison between two null pointers, or a null pointer and a resolved pointer:

  Constant* op0Arg = 0, *op1Arg = 0;
  if(op0C && op0C->isNullValue())
    op0Arg = zero;
  else if(op0.getType()->isPointerTy() && (op0UGO || op0Fun))
    op0Arg = one;
  
  if(op1C && op1C->isNullValue())
    op1Arg = zero;
  else if(op1.getType()->isPointerTy() && (op1UGO || op1Fun))
    op1Arg = one;

  if(op0Arg && op1Arg && (op0Arg == zero || op1Arg == zero)) {
    
    ImpType = ValSetTypeScalar;
    Improved = ShadowValue(ConstantFoldCompareInstOperands(CmpI->getPredicate(), op0Arg, op1Arg, GlobalTD));

    if(comparingHeapPointer && needsRuntimeCheck) {

      ShadowValue& heapOp = op0Arg == zero ? op1 : op0;

      if(!heapPointerAlreadyTested(heapOp, SI))
	(*needsRuntimeCheck) = RUNTIME_CHECK_AS_EXPECTED;

    }

    return true;   

  }

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
    Improved.V = ShadowValue(ConstantFoldCompareInstOperands(getSignedPred(CmpI->getPredicate()), op0Arg, op1Arg, GlobalTD));
    return true;

  }

  // 3. Restricted comparison of pointers with a differing base: we can compare for equality only
  // as we don't know memory layout at this stage.

  if(isIDOrConst(op0) && isIDOrConst(op1) && op0 != op1) {

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

    if(!Op0Ptr) {

      // This is a constant - pointer, which some compilers e.g. DragonEgg-3.2 + gcc-4.6 can produce.
      // Mark it as pointer with unknown offset, to hopefully catch it later in the special case under ::Add
      // below.

      ImpType = ValSetTypePB;
      Improved.V = Ops[1].second.V;
      Improved.Offset = LLONG_MAX;
      return true;

    }

    if(!Op1Ptr) {

      ConstantInt* Op1I = dyn_cast_or_null<ConstantInt>(Ops[1].second.V.getVal());

      ImpType = ValSetTypePB;
      Improved.V = Ops[0].second.V;
      if(Ops[0].second.Offset == LLONG_MAX || !Op1I)
	Improved.Offset = LLONG_MAX;
      else
	Improved.Offset = Ops[0].second.Offset - Op1I->getSExtValue();

      return true;

    }
    else if(Ops[0].second.V == Ops[1].second.V) {

      // Subtracting pointers with a common base.
      if(Ops[0].second.Offset != LLONG_MAX && Ops[1].second.Offset != LLONG_MAX) {
	ImpType = ValSetTypeScalar;
	Improved = ShadowValue(ConstantInt::getSigned(BOp->getType(), Ops[0].second.Offset - Ops[1].second.Offset));
	return true;
      }

    }

  }
  else if(BOp->getOpcode() == Instruction::Add) {

    if(Op0Ptr && Op1Ptr) {

      // Check for the special case mentioned above: some compilers generate constructions like:
      // (const - ptr) + ptr, where the former operand is noted as (ptr + ?) since ImprovedVal
      // has no way to indicate the negation of a pointer at the moment.
      // Try to find that case if it has happened here.

      // Need a common base and at least one non-? offset:
      if(Ops[0].second.V != Ops[1].second.V)
	return false;

      uint32_t checkNegOp;
      if(Ops[0].second.Offset == LLONG_MAX)
	checkNegOp = 0;
      else
	checkNegOp = 1;
      
      uint32_t otherOp = checkNegOp == 0 ? 1 : 0;
      if(Ops[otherOp].second.Offset == LLONG_MAX)
	return false;

      ShadowValue checkOp = SI->getOperand(checkNegOp);

      if((!checkOp.isInst()) || checkOp.u.I->invar->I->getOpcode() != Instruction::Sub)
	return false;

      ConstantInt* SubOp0 = dyn_cast_or_null<ConstantInt>(getConstReplacement(checkOp.u.I->getOperand(0)));
      if(!SubOp0)
	return false;

      ShadowInstruction* SubOp1 = checkOp.u.I->getOperand(1).getInst();
      if(!SubOp1)
	return false;

      ShadowValue SubOp1Base;
      int64_t SubOp1Offset;
      if(!getBaseAndConstantOffset(ShadowValue(SubOp1), SubOp1Base, SubOp1Offset))
	return false;

      if(SubOp1Base != Ops[checkNegOp].second.V)
	return false;

      // OK, the special case applies: We have (p + c1) + (c2 - (p + c3))
      // (or commute the topmost + operator) = c1 + c2 - c3.

      ImpType = ValSetTypeScalar;
      int64_t NewVal = (Ops[otherOp].second.Offset + ((int64_t)SubOp0->getLimitedValue())) - SubOp1Offset;
      Improved.V = ShadowValue(ConstantInt::getSigned(BOp->getType(), NewVal));

      return true;

    }
    
    std::pair<ValSetType, ImprovedVal>& PtrV = Op0Ptr ? Ops[0] : Ops[1];
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
      else if(isa<CallInst>(SI->invar->I)) {
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

// Defined in VMCore/ConstantFold.cpp but never prototyped:
namespace llvm {
  Constant* ConstantFoldExtractValueInstruction(Constant *Agg, ArrayRef<unsigned> Idxs);
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

  Constant* Op0C = cast_or_null<Constant>(Ops[0].second.V.getVal());
  Constant* Op1C = cast_or_null<Constant>(Ops[1].second.V.getVal());

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

static Constant* tryCastTo(Constant* C, Type* Ty) {

  if(!CastInst::isCastable(C->getType(), Ty))
    return 0;

  Instruction::CastOps Op = CastInst::getCastOpcode(C, false, Ty, false);
  return ConstantExpr::getCast(Op, C, Ty);

}

void IntegrationAttempt::tryEvaluateResult(ShadowInstruction* SI, 
					   std::pair<ValSetType, ImprovedVal>* Ops, 
					   ValSetType& ImpType, ImprovedVal& Improved,
					   unsigned char* needsRuntimeCheck) {
  
  Instruction* I = SI->invar->I;

  // Try a special case for forwarding FDs: they can be passed through any cast preserving 32 bits.
  // We optimistically pass vararg cookies through all casts.
  if(inst_is<CastInst>(SI)) {

    CastInst* CI = cast_inst<CastInst>(SI);
    Type* SrcTy = CI->getSrcTy();
    Type* DestTy = CI->getDestTy();
	
    if(Ops[0].first == ValSetTypeFD) {
      if(!((SrcTy->isIntegerTy(32) || SrcTy->isIntegerTy(64) || SrcTy->isPointerTy()) &&
	   (DestTy->isIntegerTy(32) || DestTy->isIntegerTy(64) || DestTy->isPointerTy()))) {

	ImpType = ValSetTypeOverdef;
	return;

      }
    }

    if(Ops[0].first != ValSetTypeScalar) {

      // Pass FDs, pointers, vararg cookies through. This includes ptrtoint and inttoptr.
      ImpType = Ops[0].first;
      Improved = Ops[0].second;
      return;

    }

    // Otherwise pass scalars through the normal constant folder.

  }

  if(inst_is<CmpInst>(SI)) {

    if(tryFoldOpenCmp(SI, Ops, ImpType, Improved))
      return;
    if(inst_is<ICmpInst>(SI) && tryFoldPointerCmp(SI, Ops, ImpType, Improved, needsRuntimeCheck))
      return;
    if(tryFoldNonConstCmp(SI, Ops, ImpType, Improved))
      return;

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
	    ConstantInt* OpC = cast<ConstantInt>(Ops[i].second.V.getVal());
	    if (OpC->isZero()) continue;
	    // Handle a struct and array indices which add their offset to the pointer.
	    if (StructType *STy = dyn_cast<StructType>(*GTI)) {
	      Improved.Offset += GlobalTD->getStructLayout(STy)->getElementOffset(OpC->getZExtValue());
	    } else {
	      uint64_t Size = GlobalTD->getTypeAllocSize(GTI.getIndexedType());
	      Improved.Offset += OpC->getSExtValue()*Size;
	    }
	  }
	}

      }

      return;

    }
    else if(SI->getNumOperands() == 2 && Ops[0].first == ValSetTypeVarArg) {

      int64_t newVaArg = ImprovedVal::not_va_arg;

      if(Ops[1].first == ValSetTypeVarArg) {

	// This should be gep ( symbolic-stack-base, some-offset )
	// some-offset will denote the nth fp arg or nth non-fp arg
	// return value should be the nth arg /of either kind/
	
	InlineAttempt* calledIA = Ops[0].second.V.getInst()->parent->IA->getFunctionRoot();

	if(Ops[0].second.getVaArgType() == va_arg_type_baseptr) {

	  if(Ops[1].second.getVaArgType() == va_arg_type_nonfp)
	    newVaArg = calledIA->NonFPArgIdxToArgIdx(Ops[1].second.getVaArg());
	  else if(Ops[1].second.getVaArgType() == va_arg_type_fp)
	    newVaArg = calledIA->FPArgIdxToArgIdx(Ops[1].second.getVaArg());

	}

      }
      else if(Ops[1].first == ValSetTypeScalar) {

	// This should be gep ( any-arg-ptr, some-scalar ) -> any-arg-ptr + 1
	if(Ops[0].second.getVaArgType() == va_arg_type_any) {

	  newVaArg = Ops[0].second.Offset + 1;

	}

      }

      if(newVaArg != ImprovedVal::not_va_arg) {
	ImpType = ValSetTypeVarArg;
	Improved.V = Ops[0].second.V;
	Improved.Offset = newVaArg;
	return;
      }
      
    }

    ImpType = (Ops[0].first == ValSetTypeUnknown ? ValSetTypeUnknown : ValSetTypeOverdef);
    return;
	  
  }

  else if(I->getOpcode() == Instruction::Add || I->getOpcode() == Instruction::Sub || I->getOpcode() == Instruction::And || I->getOpcode() == Instruction::Or) {

    if(I->getOpcode() == Instruction::Add && Ops[0].first == ValSetTypeVarArg) {
      ImpType = ValSetTypeVarArg;
      Improved = ImprovedVal(Ops[0].second.V, Ops[0].second.Offset + 1);
      return;
    }
    if(tryFoldPtrAsIntOp(SI, Ops, ImpType, Improved))
      return;
    if(tryFoldBitwiseOp(SI, Ops, ImpType, Improved))
      return;
	    
  }

  else if(I->getOpcode() == Instruction::ExtractValue) {

    // Missing from ConstantFoldInstOperands for some reason.

    if(Ops[0].first != ValSetTypeScalar) {
      ImpType = ValSetTypeOverdef;
      return;
    }

    Constant* Agg = cast<Constant>(Ops[0].second.V.u.V);
    Constant* Ext = ConstantFoldExtractValueInstruction(Agg, cast<ExtractValueInst>(SI->invar->I)->getIndices());
    if(Ext) {
      ImpType = ValSetTypeScalar;
      Improved = ImprovedVal(Ext, 0);
      return;
    }

    ImpType = ValSetTypeOverdef;
    return;

  }

  // Try ordinary constant folding?

  SmallVector<Constant*, 4> instOperands;

  bool allOpsAvailable = true;

  for(unsigned i = 0, ilim = I->getNumOperands(); i != ilim; i++) {

    if(Ops[i].first == ValSetTypePB) {
      
      if(Constant* OpBase = dyn_cast_or_null<Constant>(Ops[i].second.V.getVal())) {

	if(OpBase->isNullValue()) {

	  instOperands.push_back(getGVOffset(OpBase, Ops[i].second.Offset, OpBase->getType()));
	  continue;

	}

      }

    }
      
    if(Ops[i].first != ValSetTypeScalar) {
      if(Ops[i].first == ValSetTypeUnknown)
	allOpsAvailable = false;
      else {
	ImpType = ValSetTypeOverdef;
	return;
      }
    }

    instOperands.push_back(cast<Constant>(Ops[i].second.V.getVal()));

  }

  if(!allOpsAvailable) {

    // Need more information
    ImpType = ValSetTypeUnknown;
    return;

  }

  Constant* newConst = 0;

  if (const CmpInst *CI = dyn_cast<CmpInst>(I)) {
   
    // Rare corner case: we get here but the compare args are not of the same type.
    // Example: comparing a constant against ptrtoint(null).
    // Coerece to the real instruction's type if possible.
    if(instOperands[0]->getType() != CI->getOperand(0)->getType()) {
      instOperands[0] = tryCastTo(instOperands[0], CI->getOperand(0)->getType());
      if(!instOperands[0]) {
	ImpType = ValSetTypeUnknown;
	return;
      }
    }

    if(instOperands[1]->getType() != CI->getOperand(1)->getType()) {
      instOperands[1] = tryCastTo(instOperands[1], CI->getOperand(1)->getType());
      if(!instOperands[1]) {
	ImpType = ValSetTypeUnknown;
	return;
      }
    }    

    newConst = ConstantFoldCompareInstOperands(CI->getPredicate(), instOperands[0], instOperands[1], GlobalTD);

  }
  else if(isa<LoadInst>(I))
    newConst = ConstantFoldLoadFromConstPtr(instOperands[0], GlobalTD);
  else
    newConst = ConstantFoldInstOperands(I->getOpcode(), I->getType(), instOperands, GlobalTD, GlobalTLI, /* preserveGEPSign = */ true);

  if(newConst) {

    // Filter out cases that have just wrapped a ConstantExpr around the operands.
    // Acceptable cases here: inttoptr(const)
    if(ConstantExpr* CE = dyn_cast<ConstantExpr>(newConst)) {

      if(CE->getOpcode() != Instruction::IntToPtr && CE->getOpcode() != Instruction::BitCast) {
	ImpType = ValSetTypeOverdef;
	return;
      }

    }

    LPDEBUG(itcache(*I) << " now constant at " << itcache(*newConst) << "\n");

    if(isa<ConstantPointerNull>(newConst)) {
      ImpType = ValSetTypePB;
      Improved = ImprovedVal(ShadowValue(newConst), 0);
    }
    else{
      ImpType = ValSetTypeScalar;
      Improved.V = ShadowValue(newConst);
    }
  }
  else {
    ImpType = ValSetTypeOverdef;
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

// All Ops are known not to have multi values.
bool IntegrationAttempt::tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSetSingle& NewPB, std::pair<ValSetType, ImprovedVal>* Ops, uint32_t OpIdx) {

  if(OpIdx == SI->getNumOperands()) {

    ValSetType ThisVST;
    ImprovedVal ThisV;
    tryEvaluateResult(SI, Ops, ThisVST, ThisV, &SI->needsRuntimeCheck);
    if(ThisVST == ValSetTypeUnknown)
      return false;
    else if(ThisVST == ValSetTypeOverdef) {
      NewPB.setOverdef();
      return true;
    }
    else {

      NewPB.mergeOne(ThisVST, ThisV);
      return true;

    }

  }

  // Else queue up the next operand:

  ShadowValue OpV = SI->getOperand(OpIdx);

  switch(OpV.t) {
  case SHADOWVAL_OTHER:
    
    Ops[OpIdx] = getValPB(OpV.u.V);
    return tryEvaluateOrdinaryInst(SI, NewPB, Ops, OpIdx+1);

  case SHADOWVAL_GV:

    Ops[OpIdx] = std::make_pair(ValSetTypePB, ImprovedVal(OpV, 0));
    return tryEvaluateOrdinaryInst(SI, NewPB, Ops, OpIdx+1);

  default:

    {

      ImprovedValSetSingle& ArgPB = *(cast<ImprovedValSetSingle>(getIVSRef(OpV)));
      if(ArgPB.isWhollyUnknown()) {

	if(!tryGetPathValue(OpV, SI->parent, Ops[OpIdx])) {

	  Ops[OpIdx].first = ArgPB.Overdef ? ValSetTypeOverdef : ValSetTypeUnknown;
	  Ops[OpIdx].second.V = ShadowValue();

	}

	return tryEvaluateOrdinaryInst(SI, NewPB, Ops, OpIdx+1);

      }
      else {
      
	Ops[OpIdx].first = ArgPB.SetType;
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

}

bool IntegrationAttempt::tryEvaluateMultiCmp(ShadowInstruction* SI, ImprovedValSet*& NewIV) {

  CmpInst* CI = cast_inst<CmpInst>(SI);
  CmpInst::Predicate Pred = CI->getPredicate();
  switch(Pred) {

  case CmpInst::ICMP_EQ:
  case CmpInst::ICMP_NE:
    break;
  default:
    NewIV = newOverdefIVS();
    return true;

  }

  CI->setPredicate(CmpInst::ICMP_EQ);
  MultiCmpResult MCR = tryEvaluateMultiEq(SI);
  CI->setPredicate(Pred);

  if(Pred == CmpInst::ICMP_NE) {
    switch(MCR) {
    case MCRTRUE:
      MCR = MCRFALSE; break;
    case MCRFALSE:
      MCR = MCRTRUE; break;
    default:
      break;
    }
  }

  switch(MCR) {

  case MCRTRUE: 
  case MCRFALSE:
    {
      ImprovedValSetSingle* NewIVS = newIVS();
      NewIV = NewIVS;
      LLVMContext& LLC = SI->invar->I->getContext();
      ShadowValue Result = ShadowValue(MCR == MCRTRUE ? ConstantInt::getTrue(LLC) : ConstantInt::getFalse(LLC));
      NewIVS->set(ImprovedVal(Result), ValSetTypeScalar);
      break;
    }
  case MCRMAYBE:
    NewIV = newOverdefIVS();
    break;
  }

  return true;

}

MultiCmpResult IntegrationAttempt::tryEvaluateMultiEq(ShadowInstruction* SI) {

  // EQ is true if true of all fields, false if false anywhere, or unknown otherwise.

  ImprovedValSetMulti* IVM;
  Constant* CmpC;
  if(!(IVM = dyn_cast<ImprovedValSetMulti>(getIVSRef(SI->getOperand(0))))) {
    IVM = cast<ImprovedValSetMulti>(getIVSRef(SI->getOperand(1)));
    CmpC = getConstReplacement(SI->getOperand(0));
  }
  else {
    CmpC = getConstReplacement(SI->getOperand(1));
  }

  if(!CmpC)
    return MCRMAYBE;

  uint64_t CmpInt = cast<ConstantInt>(CmpC)->getLimitedValue();
  uint8_t* CmpBytes = (uint8_t*)&CmpInt;
  bool allEqual = true;

  for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), endit = IVM->Map.end(); it != endit; ++it) {

    std::pair<ValSetType, ImprovedVal> Ops[2];
    Type* SubValType = Type::getIntNTy(SI->invar->I->getContext(), it.stop() - it.start());
    Constant* SubVal = constFromBytes(&(CmpBytes[it.start()]), SubValType, GlobalTD);
    Ops[0] = std::make_pair(ValSetTypeScalar, ImprovedVal(SubVal));
    MultiCmpResult MCRHere = MCRMAYBE;

    for(uint32_t i = 0; i < it.val().Values.size(); ++i) {
      
      ValSetType ThisVST;
      ImprovedVal ThisV;
      Ops[1] = std::make_pair(it.val().SetType, it.val().Values[i]);
      tryEvaluateResult(SI, Ops, ThisVST, ThisV, 0);
      if(ThisVST != ValSetTypeScalar) {
	MCRHere = MCRMAYBE;
	break;
      }
      Constant* ThisC = cast_val<Constant>(ThisV.V);
      MultiCmpResult thisResult = ThisC->isNullValue() ? MCRFALSE : MCRTRUE;

      if(i == 0)
	MCRHere = thisResult;
      else if(MCRHere != thisResult) {
	MCRHere = MCRMAYBE;
	break;
      }

    }
    
    switch(MCRHere) {
    case MCRFALSE:
      return MCRFALSE;
    case MCRTRUE:
      continue;
    case MCRMAYBE:
      allEqual = false;
    }
      
  }

  if(allEqual)
    return MCRTRUE;
  else
    return MCRMAYBE;

}

bool IntegrationAttempt::tryEvaluateMultiInst(ShadowInstruction* SI, ImprovedValSet*& NewIV) {

  // Currently supported operations on multis:
  // * Equality, inequality
  // * Shift right and left by constant amount
  // * Truncate
  // * PHI, select, and other copies (but these are implemented in the merge-instruction path)
  
  if(inst_is<CmpInst>(SI))
    return tryEvaluateMultiCmp(SI, NewIV);

  unsigned opcode = SI->invar->I->getOpcode();
  int64_t resSize = (int64_t)GlobalAA->getTypeStoreSize(SI->getType());

  switch(opcode) {
    
  case Instruction::LShr:
  case Instruction::AShr:
  case Instruction::Shl:
  case Instruction::Trunc:
    {

      int64_t ShiftInt;

      if(opcode != Instruction::Trunc) {

	ConstantInt* ShiftAmt = cast_or_null<ConstantInt>(getConstReplacement(SI->getOperand(1)));
	if(!ShiftAmt) {
	  NewIV = newOverdefIVS();
	  return true;
	}
	ShiftInt = (int64_t)ShiftAmt->getLimitedValue();
	if(ShiftInt % 8 != 0) {
	  NewIV = newOverdefIVS();
	  return true;
	}
	ShiftInt /= 8;

	if(opcode == Instruction::LShr || opcode == Instruction::AShr)
	  ShiftInt = -ShiftInt;

      }
      else {

	// Trunc (on LE systems) selects the lowest-numbered bytes.
	ShiftInt = 0;
	
      }

      ImprovedValSetMulti* InIVM = cast<ImprovedValSetMulti>(getIVSRef(SI->getOperand(0)));

      // Discounting items that will be out of range, will the new value be a simple integer?
      // How many items will remain visible post shift?
      bool NonScalarsInRange = false;
      bool uniqueValid = false;
      ImprovedValSetSingle* uniqueVal = 0;
      for(ImprovedValSetMulti::MapIt it = InIVM->Map.begin(), endit = InIVM->Map.end(); it != endit; ++it) {

	// Out of range left?
	if(((int64_t)it.stop()) + ShiftInt <= 0)
	  continue;
	
	// Out of range right?
	if(it.start() + ShiftInt >= (uint64_t)resSize)
	  continue;

	if(!(it.val().SetType == ValSetTypeScalar || it.val().Overdef || !it.val().isInitialised()))
	  NonScalarsInRange = true;

	if(!uniqueValid) {
	  uniqueVal = &(it.val());
	  uniqueValid = true;
	}
	else
	  uniqueVal = 0;

      }

      if(uniqueVal) {

	NewIV = copyIV(uniqueVal);

      }
      else if(!NonScalarsInRange) {
	
	// Flatten to single value.
	PartialVal PV(resSize);
	for(ImprovedValSetMulti::MapIt it = InIVM->Map.begin(), endit = InIVM->Map.end(); it != endit; ++it) {

	  // Out of range left?
	  if(((int64_t)it.stop()) + ShiftInt <= 0)
	    continue;
	
	  // Out of range right?
	  if(it.start() + ShiftInt >= (uint64_t)resSize)
	    continue;

	  int64_t ShiftedStart = ((int64_t)it.start()) + ShiftInt;
	  int64_t ShiftedStop = ((int64_t)it.stop()) + ShiftInt;

	  if(!addIVSToPartialVal(it.val(), std::max(-ShiftedStart, (int64_t)0), std::max(ShiftedStart, (int64_t)0), std::min(ShiftedStop, resSize) - std::max(ShiftedStart, (int64_t)0), &PV, 0)) {

	    NewIV = newOverdefIVS();
	    return true;    

	  }

	}

	ImprovedValSetSingle* NewIVS = newIVS();
	NewIV = NewIVS;
	Constant* PVConst = PVToConst(PV, 0, resSize, SI->invar->I->getContext());
	ShadowValue PVConstV(PVConst);
	addValToPB(PVConstV, *NewIVS);

      }
      else {

	// Make a new IVM, but offset and trimmed.
	ImprovedValSetMulti* NewIVM = new ImprovedValSetMulti(InIVM->AllocSize);
	NewIV = NewIVM;

	for(ImprovedValSetMulti::MapIt it = InIVM->Map.begin(), endit = InIVM->Map.end(); it != endit; ++it) {	
	  // Out of range left?
	  if(((int64_t)it.stop()) + ShiftInt <= 0)
	    continue;
	
	  // Out of range right?
	  if(it.start() + ShiftInt >= (uint64_t)resSize)
	    continue;

	  int64_t ShiftedStart = ((int64_t)it.start()) + ShiftInt;
	  int64_t ShiftedStop = ((int64_t)it.stop()) + ShiftInt;

	  NewIVM->Map.insert(it.start(), it.stop(), *it);
	  ImprovedValSetMulti::MapIt newVal = NewIVM->Map.find(it.start());

	  if(ShiftedStart < 0) {
	    if(canTruncate(newVal.val()))
	      truncateRight(newVal, -ShiftedStart);
	    else
	      newVal.val().setOverdef();
	  }
	  else if(ShiftedStop > resSize) {
	    if(canTruncate(newVal.val()))
	      truncateLeft(newVal, ShiftedStop - resSize);
	    else
	      newVal.val().setOverdef();
	  }
	 
	}

	// Iterate again because the truncate options can break composites into many entries.
	// All values are now in appropriate range.
	for(ImprovedValSetMulti::MapIt it = InIVM->Map.begin(), endit = InIVM->Map.end(); it != endit; ++it) {	

	  it.setStart(it.start() + ShiftInt);
	  it.setStop(it.stop() + ShiftInt);

	}

      }

    }
    break;

  case Instruction::And:
    {

      // Evaluate against each subcomponent. Any mask against a non-scalar except 0x00 and 0xff -> overdef.
      ImprovedValSetMulti* IVM;
      Constant* MaskC;
      if(!(IVM = dyn_cast<ImprovedValSetMulti>(getIVSRef(SI->getOperand(0))))) {
	IVM = cast<ImprovedValSetMulti>(getIVSRef(SI->getOperand(1)));
	MaskC = getConstReplacement(SI->getOperand(0));
      }
      else {
	MaskC = getConstReplacement(SI->getOperand(1));
      }

      if(!MaskC) {
	NewIV = newOverdefIVS();
	break;
      }

      uint64_t MaskInt = cast<ConstantInt>(MaskC)->getLimitedValue();
      uint8_t* Mask = (uint8_t*)&MaskInt;
      
      bool anyNonScalarVisible = false;
      bool anyNonScalarPreserved = false;

      for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), endit = IVM->Map.end(); it != endit; ++it) {

	if(it.val().SetType == ValSetTypePB || it.val().SetType == ValSetTypeFD) {
	  for(uint32_t i = it.start(), ilim = it.stop(); i != ilim; ++i) {
	    if(Mask[i])
	      anyNonScalarVisible = true;
	  }
	  bool thisPreserved = true;
	  for(uint32_t i = it.start(), ilim = it.stop(); i != ilim; ++i) {
	    if(Mask[i] != 0xff)
	      thisPreserved = false;
	  }
	  anyNonScalarPreserved |= thisPreserved;
	}

      }

      if(!anyNonScalarVisible) {

	// Now wholly scalar, so flatten and eval.

	PartialVal PV(resSize);	  	

	for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), endit = IVM->Map.end(); it != endit; ++it) {

	  if(it.val().SetType == ValSetTypePB || it.val().SetType == ValSetTypeFD) {
	    
	    Type* valType = Type::getIntNTy(SI->invar->I->getContext(), it.stop() - it.start());
	    Constant* Zero = Constant::getNullValue(valType);
	    PartialVal NewPV = PartialVal::getPartial(Zero, 0);
	    PV.combineWith(NewPV, it.start(), it.stop(), PV.partialBufBytes, GlobalTD, 0);

	  }
	  else {

	    if(!addIVSToPartialVal(it.val(), 0, it.start(), it.stop() - it.start(), &PV, 0)) {
	      NewIV = newOverdefIVS();
	      return true;
	    }

	  }

	}

	ImprovedValSetSingle* NewIVS = newIVS();
	NewIV = NewIVS;
	Constant* PVConst = PVToConst(PV, 0, resSize, SI->invar->I->getContext());

	Constant* MaskedConst = ConstantExpr::getAnd(PVConst, MaskC);
	if(ConstantExpr* MaskedCE = dyn_cast<ConstantExpr>(MaskedConst))
	  MaskedConst = ConstantFoldConstantExpression(MaskedCE);

	ShadowValue MaskedConstV(MaskedConst);
	addValToPB(MaskedConstV, *NewIVS);

      }
      else if(!anyNonScalarPreserved) {

	// FD or pointer components all clobbered. Call it overdef.
	NewIV = newOverdefIVS();

      }
      else {

	// FD or pointer components retained, but necessarily aren't the whole thing.
	// Create a new multi, with each individual part masked appropriately.

	ImprovedValSetMulti* NewIVM = new ImprovedValSetMulti(IVM->AllocSize);
	NewIV = NewIVM;
	for(ImprovedValSetMulti::MapIt it = IVM->Map.begin(), endit = IVM->Map.end(); it != endit; ++it) {

	  if(it.val().SetType == ValSetTypePB || it.val().SetType == ValSetTypeFD) {

	    bool thisPreserved = true;
	    for(uint32_t i = it.start(), ilim = it.stop(); i != ilim; ++i) {
	      if(Mask[i] != 0xff)
		thisPreserved = false;
	    }

	    if(thisPreserved)
	      NewIVM->Map.insert(it.start(), it.stop(), it.val());
	    else
	      NewIVM->Map.insert(it.start(), it.stop(), ImprovedValSetSingle(ValSetTypeUnknown, true));

	  }
	  else if(it.val().SetType == ValSetTypeScalar) {
	    
	    ImprovedValSetSingle newIVS;

	    std::pair<ValSetType, ImprovedVal> Ops[2];
	    Type* SubMaskType = Type::getIntNTy(SI->invar->I->getContext(), it.stop() - it.start());
	    Constant* SubMask = constFromBytes(&(Mask[it.start()]), SubMaskType, GlobalTD);
	    Ops[0] = std::make_pair(ValSetTypeScalar, ImprovedVal(SubMask));

	    for(uint32_t i = 0; i < it.val().Values.size(); ++i) {

	      ValSetType ThisVST;
	      ImprovedVal ThisV;
	      Ops[1] = std::make_pair(ValSetTypeScalar, it.val().Values[i]);
	      tryEvaluateResult(SI, Ops, ThisVST, ThisV, 0);
	      if(ThisVST != ValSetTypeScalar) {
		newIVS.setOverdef();
		break;
	      }
	      else {
		newIVS.mergeOne(ThisVST, ThisV);
	      }

	    }

	    NewIVM->Map.insert(it.start(), it.stop(), newIVS);

	  }
	  else {

	    NewIVM->Map.insert(it.start(), it.stop(), ImprovedValSetSingle(ValSetTypeUnknown, true));

	  }

	}

      }

    }
    break;

    // Unhandled instructions:
  default:
    NewIV = newOverdefIVS();

  }

  return true;

}

bool IntegrationAttempt::tryEvaluateOrdinaryInst(ShadowInstruction* SI, ImprovedValSet*& NewPB) {

  bool anyMultis = false;

  for(uint32_t i = 0, ilim = SI->getNumOperands(); i != ilim && !anyMultis; ++i) {
    
    ShadowValue OpV = SI->getOperand(i);
    switch(OpV.t) {
    case SHADOWVAL_INST:
    case SHADOWVAL_ARG:
      anyMultis |= isa<ImprovedValSetMulti>(getIVSRef(OpV));
      break;
    default:
      break;
    }

  }

  if(anyMultis) {
    return tryEvaluateMultiInst(SI, NewPB);
  }
  else {
    ImprovedValSetSingle* NewIVS = newIVS();
    NewPB = NewIVS;
    std::pair<ValSetType, ImprovedVal> Ops[SI->getNumOperands()];
    return tryEvaluateOrdinaryInst(SI, *NewIVS, Ops, 0);
  }

}

bool IntegrationAttempt::getNewPB(ShadowInstruction* SI, ImprovedValSet*& NewPB, bool& loadedVararg) {

  // Special case the merge instructions:
  bool tryMerge = false;
 
  switch(SI->invar->I->getOpcode()) {
    
  case Instruction::Load:
    return tryForwardLoadPB(SI, NewPB, loadedVararg);
  case Instruction::PHI:
    {
      bool Valid;
      if(tryEvaluateHeaderPHI(SI, Valid, NewPB))
	return Valid;
      tryMerge = true;
      break;
    }
  case Instruction::Select:
    {
      Constant* Cond = getConstReplacement(SI->getOperand(0));
      if(Cond) {
	if(cast<ConstantInt>(Cond)->isZero())
	  return copyImprovedVal(SI->getOperand(2), NewPB);
	else
	  return copyImprovedVal(SI->getOperand(1), NewPB);
      }
      else {
	tryMerge = true;
      }
    }
    break;
  case Instruction::Call: 
    {
      if(inlineChildren.count(SI))
	tryMerge = true;
      break;
    }
  case Instruction::Br:
  case Instruction::Switch:
    // Normally these are filtered, but the loop solver can queue them:
    return false;
  default:
    break;

  }

  if(tryMerge) {

    tryEvaluateMerge(SI, NewPB);
    if(!NewPB)
      return true;
    if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(NewPB))
      return IVS->isInitialised();
    else
      return true;

  }
  else {

    tryEvaluateOrdinaryInst(SI, NewPB);

    if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(NewPB)) {
      if(!IVS->isInitialised())
	IVS->setOverdef();
      if(IVS->isWhollyUnknown()) {

	for(uint32_t i = 0, ilim = SI->invar->operandIdxs.size(); i != ilim; ++i)
	  valueEscaped(SI->getOperand(i), SI->parent);

      }
    }

    return true;

  }

}

static bool willUseIndirectly(ImprovedValSet* IV) {

  if(ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(IV)) {

    if((IVS->SetType == ValSetTypeFD || IVS->SetType == ValSetTypePB) && IVS->Values.size() == 1)
      return true;

  }

  return false;

}

void llvm::releaseIndirectUse(ShadowValue V, ImprovedValSet* OldPB) {

  if(willUseIndirectly(OldPB)) {

    ImprovedValSetSingle* OldIVS = cast<ImprovedValSetSingle>(OldPB);
    if(ShadowInstruction* Used = OldIVS->Values[0].V.getInst()) {
	
      std::vector<ShadowValue>& Users = GlobalIHP->indirectDIEUsers[Used];

      std::vector<ShadowValue>::iterator findit = std::find(Users.begin(), Users.end(), V);
      if(findit != Users.end())
	Users.erase(findit);
      
    }

  }

}

void llvm::noteIndirectUse(ShadowValue V, ImprovedValSet* NewPB) {

  if(willUseIndirectly(NewPB)) {
	
    ImprovedValSetSingle* NewIVS = cast<ImprovedValSetSingle>(NewPB);
    if(ShadowInstruction* WillUse = NewIVS->Values[0].V.getInst()) {

      std::vector<ShadowValue>& Users = GlobalIHP->indirectDIEUsers[WillUse];
      
      if(std::find(Users.begin(), Users.end(), V) == Users.end())
	Users.push_back(V);

    }
      
  }

}

bool IntegrationAttempt::tryEvaluate(ShadowValue V, bool inLoopAnalyser, bool& loadedVararg) {

  ImprovedValSet* OldPB = getIVSRef(V);
  ImprovedValSetSingle* OldPBSingle = dyn_cast_or_null<ImprovedValSetSingle>(OldPB);
  // The latter case here implies a multi which is always defined.
  bool OldPBValid = (OldPBSingle && OldPBSingle->isInitialised()) || (OldPB && !OldPBSingle);

  if(inLoopAnalyser) {
    // Values can only get worse, and overdef is as bad as it gets:
    if(OldPBSingle && OldPBSingle->Overdef)
      return false;
  }

  ImprovedValSet* NewPB = 0;
  bool NewPBValid;

  ShadowInstruction* SI = V.getInst();
  NewPBValid = getNewPB(SI, NewPB, loadedVararg);

  // AFAIK only void calls can be rejected this way.
  if(!NewPB)
    return false;

  release_assert(NewPBValid);

  // Check if there is a path condition defining the instruction,
  // as opposed to one defining an /argument/, which is checked elsewhere.
  {

    ImprovedValSetSingle* NewIVS;
    if((NewIVS = dyn_cast<ImprovedValSetSingle>(NewPB)) && NewIVS->isWhollyUnknown()) {

      std::pair<ValSetType, ImprovedVal> PathVal;
      if(tryGetAsDefPathValue(V, SI->parent, PathVal))
	NewIVS->set(PathVal.second, PathVal.first);

    }

  }

  if((!OldPBValid) || !IVsEqualShallow(OldPB, NewPB)) {

    if(OldPBValid)
      releaseIndirectUse(V, OldPB);

    noteIndirectUse(V, NewPB);

    if(pass->verboseOverdef) {
      if(ShadowInstruction* I = V.getInst()) {
	if(!inst_is<LoadInst>(I)) {
	  std::string RStr;
	  raw_string_ostream RSO(RStr);
	  NewPB->print(RSO, true);
	  RSO.flush();
	  pass->optimisticForwardStatus[I] = RStr;
	}
      }
    }

    if(ShadowInstruction* SI = V.getInst()) {
      if(SI->i.PB)
	deleteIV(SI->i.PB);
      SI->i.PB = NewPB;
    }
    else {
      ShadowArg* SA = V.getArg();
      if(SA->i.PB)
	deleteIV(SA->i.PB);
      SA->i.PB = NewPB;
    }

    bool verbose = false;

    if(verbose) {
      errs() << "Updated dep to ";
      NewPB->print(errs(), false);
      errs() << "\n";
    }
  
    /*
    if(LPBA) {
      //errs() << "QUEUE\n";
      queueUsersUpdatePB(V, LPBA);
    }
    */

    return true;

  }
  else {

    // New result not needed.
    deleteIV(NewPB);

  }

  return false;

}

namespace llvm {

  raw_ostream& operator<<(raw_ostream& Stream, const IntegrationAttempt& P) {

    P.describe(Stream);
    return Stream;

  }

}

