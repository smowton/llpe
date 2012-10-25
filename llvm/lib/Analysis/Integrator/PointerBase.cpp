// Implementation of an SCCP-like solver to discover the base object pointers refer to.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instruction.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

bool IntegrationAttempt::getPointerBaseLocal(Value* V, PointerBase& OutPB) {

  if(isa<AllocaInst>(V) || isNoAliasCall(V)) {

    OutPB = PointerBase::get(make_vc(V, this), 0);
    return true;

  }
  else if(isa<GlobalValue>(V)) {

    OutPB = PointerBase::get(const_vc(cast<Constant>(V)), 0);    
    return true;

  }

  DenseMap<Value*, PointerBase>::iterator it = pointerBases.find(V);
  if(it != pointerBases.end()) {
    OutPB = it->second;
    return true;
  }

  return false;

}

bool IntegrationAttempt::getPointerBaseRising(Value* V, PointerBase& OutPB, const Loop* VL) {
  
  if(VL == getLoopContext())
    return getPointerBaseFalling(V, OutPB);

  PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(getLoopContext(), VL));
  if(!LPA)
    return getPointerBaseFalling(V, OutPB);

  PeelIteration* LastIt = LPA->Iterations.back();
  if(!LastIt->isOnlyExitingIteration())
    return getPointerBaseFalling(V, OutPB);

  return LastIt->getPointerBaseRising(V, OutPB, VL);

}

bool IntegrationAttempt::getPointerBaseFalling(Value* V, PointerBase& OutPB) {

  if(getPointerBaseLocal(V, OutPB))
    return true;
  if(parent)
    return parent->getPointerBaseFalling(V, OutPB);
  return false;

}

// The loop-header-PHI case is already taken care of.
// UserI is the instruction that uses V in whose context we're investigating V.
bool IntegrationAttempt::getPointerBase(Value* V, PointerBase& OutPB, Instruction* UserI) {

  const Loop* MyL = getLoopContext();
  const Loop* VL = getValueScope(V);
  const Loop* UserL = getValueScope(UserI);

  // Bear in mind here that this context's loop might be lower than either VL or UserL
  // because we're trying to work out their base in a loop-invariant context.
  // If MyL doesn't match UserL then we won't rise into loops.
  
  // Case 1: UserI is an exit PHI, V is a value within some nest of loops that it exits,
  // AND we're asking about the exit PHI's natural scope. Try to use specific information
  // if available.

  if(UserL == MyL && VL != UserL && ((!UserL) || UserL->contains(VL))) {

    return getPointerBaseRising(V, OutPB, VL);

  }
  
  // Case 2: UserI is within a loop and V is outside (e.g. is an argument).
  // In this case if we're in invariant scope outside both there's no need to descend.
  if(VL != UserL && ((!VL) || VL->contains(UserL)) && ((!VL) || VL->contains(MyL))) {

    return getPointerBaseFalling(V, OutPB);

  }

  // Case 3: Same loop.
  return getPointerBaseLocal(V, OutPB);
  
}

// If finalise is false, we're in the 'incremental upgrade' phase: PHIs and selects take on
// the newest result of their operands.
// If finalise is true, we're in the 'resolution' phase: they take on their true value.
// e.g. in phase 1, PHI(def_1, overdef_0) = def_1, in phase 2 it is overdef_1.
bool IntegrationAttempt::updateMergeBasePointer(Instruction* I, bool finalise) {

  SmallVector<Value*, 4> Vals;
  if(SelectInst* SI = dyn_cast<SelectInst>(I)) {

    Vals.push_back(SI->getTrueValue());
    Vals.push_back(SI->getFalseValue());

  }
  else {

    PHINode* PN = cast<PHINode>(I);
    for(unsigned i = 0; i < PN->getNumIncomingValues(); ++i)
      Vals.push_back(PN->getIncomingValue(i));

  }

  bool UniqueBaseSet = false;
  ValCtx UniqueBase;
  
  uint64_t MaxGen = 0;
  for(SmallVector<Value*, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2; ++it) {

    Value* V = *it;
    PointerBase VPB;
    if(getPointerBase(V, VPB, I)) {

      if(VPB.Generation > MaxGen)
	MaxGen = VPB.Generation;

    }

  }

  for(SmallVector<Value*, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2; ++it) {
    
    Value* V = *it;
    PointerBase VPB;
    if(getPointerBase(V, VPB, I)) {

      if(VPB.Generation == MaxGen || (!VPB.Overdef) || finalise) {

	if(VPB.Overdef || (UniqueBaseSet && UniqueBase != VPB.Base)) {

	  pointerBases[I] = PointerBase::getOverdef(MaxGen);
	  return true;

	}
	else {

	  UniqueBaseSet = true;
	  UniqueBase = VPB.Base;

	}

      }

    }

  }

  if(UniqueBaseSet) {

    pointerBases[I] = PointerBase::get(UniqueBase, MaxGen);
    return true;

  }

  if(!finalise) {
    // Else, have no information.
    return false;
  }
  else {
    // Missing operands treated as overdef in the finalise phase.
    pointerBases[I] = PointerBase::getOverdef(MaxGen);
    return true;
  }

}

bool InlineAttempt::getArgBasePointer(Argument* A, PointerBase& OutPB) {

  return parent->getPointerBaseFalling(CI->getArgOperand(A->getArgNo()), OutPB);

}

bool InlineAttempt::updateHeaderPHIPB(PHINode* PN, bool& Changed) {
  
  return false;

}

bool PeelIteration::updateHeaderPHIPB(PHINode* PN, bool& Changed) {
  
  Changed = false;

  PointerBase OldPB;
  bool OldPBValid = getPointerBaseFalling(PN, OldPB);

  if(L && L->getHeader() == PN->getParent()) {

    ValCtx Repl;
    if(getIterCount() == 0)
      Repl = make_vc(PN->getIncomingValueForBlock(L->getLoopPreheader()), parent);
    else {
      PeelIteration* PreviousIter = parentPA->getIteration(getIterCount() - 1);	      
      Repl = make_vc(PN->getIncomingValueForBlock(L->getLoopLatch()), PreviousIter);
    }
    PointerBase PrevPB;
    if(Repl.second->getPointerBaseFalling(Repl.first, PrevPB)) {
      if((!OldPBValid) || PrevPB.Generation > OldPB.Generation) {
	pointerBases[PN] = PrevPB;
	Changed = true;
      }
      else {
	// Nothing changed
      }
    }
    else {
      // No information
    }

    return true;

  }
  // Else, not a header PHI.
  return false;

}

bool IntegrationAttempt::updateBasePointer(Value* V, bool finalise) {

  if(Argument* A = dyn_cast<Argument>(V)) {

    PointerBase OldPB;
    bool OldPBValid = getPointerBaseFalling(V, OldPB);

    PointerBase PB;
    InlineAttempt* IA = getFunctionRoot();
    if(IA->getArgBasePointer(A, PB)) {

      if((!OldPBValid) || PB.Generation > OldPB.Generation) {

	pointerBases[A] = PB;

      }
      else {

	// Already up to date
	return false;

      }

    }
    else {

      // No information from our argument
      return false;

    }

  }
  else {

    Instruction* I = cast<Instruction>(V);

    // First a quick check: do we need to update at all?
    PointerBase OldPB;
    bool mustUpdate = false;
    if(getPointerBaseFalling(I, OldPB)) {

      for(unsigned i = 0; i < I->getNumOperands() && !mustUpdate; ++i) {

	PointerBase ArgPB;
	if(getPointerBase(I->getOperand(i), ArgPB, I)) {

	  if(ArgPB.Generation > OldPB.Generation)
	    mustUpdate = true;

	}

      }

    }

    if(!mustUpdate)
      return false;

    switch(I->getOpcode()) {

    case Instruction::GetElementPtr:
    case Instruction::BitCast:
    case Instruction::SExt:
    case Instruction::ZExt:
    case Instruction::IntToPtr:
    case Instruction::PtrToInt:

      {
	PointerBase PB;
	if(getPointerBase(I->getOperand(0), PB, I))
	  pointerBases[V] = PB;
	else
	  return false;
	break;
      }

    case Instruction::Add:
      {
	PointerBase PB1, PB2;
	bool found1 = getPointerBase(I->getOperand(0), PB1, I);
	bool found2 = getPointerBase(I->getOperand(1), PB2, I);
	if(found1 && found2) {
	  LPDEBUG("Add of 2 pointers\n");
	  pointerBases[V] = PointerBase::getOverdef(std::max(PB1.Generation, PB2.Generation));
	}
	else if((!found1) && (!found2)) {
	  return false;
	}
	else {
	  pointerBases[V] = found1 ? PB1 : PB2;
	}
	break;
      }      
    case Instruction::Sub:
      {
	PointerBase PB1, PB2;
	bool found1 = getPointerBase(I->getOperand(0), PB1, I);
	bool found2 = getPointerBase(I->getOperand(1), PB2, I);
	if(found1 && found2) {
	  LPDEBUG("Subtract of 2 pointers (makes plain int)\n");
	  return false;
	}
	else if(found1) {
	  pointerBases[V] = PB1;
	}
	else {
	  return false;
	}
	break;
      }
    case Instruction::PHI:
      {
	bool Changed;
	if(updateHeaderPHIPB(cast<PHINode>(I), Changed)) {
	  if(Changed)
	    break;
	  else
	    return false;
	}
	// Else fall through:
      }
    case Instruction::Select:
      {
	if(!updateMergeBasePointer(I, finalise))
	  return false;
	break;
      }
    default:
      // Unknown instruction -- leave it alone, if pointer-typed it will be demoted to overdef later.
      return false;
    }

  }

  queueUsersUpdatePB(V);

  return true;

}

// This is different to HCF's investigateUsers code because it investigates different scopes.
// We investigate: (1) the user's 'natural' scope (since this catches exit PHIs), and
// (2) if the user is within our scope, all scopes between ours and its 
// (since our new invariant information might be useful at many scopes).
void IntegrationAttempt::queueUsersUpdatePB(Value* V) {

  const Loop* MyL = getLoopContext();
  
  for(Value::use_iterator UI = V->use_begin(), UE = V->use_end(); UI != UE; ++UI) {

    if(Instruction* UserI = dyn_cast<Instruction>(*UI)) {

      const Loop* UserL = getValueScope(UserI);

      if((!MyL) || (UserL && MyL->contains(UserL))) {
	  
	queueUsersUpdatePBRising(UserI, UserL, V);
	
      }
      else {
	
	queueUsersUpdatePBFalling(UserI, UserL, V);

      }

    }

  }

}

void IntegrationAttempt::queueUsersUpdatePBFalling(Instruction* I, const Loop* IL, Value* V) {

  if(getLoopContext() == IL) {

    if(CallInst* CI = dyn_cast<CallInst>(I)) {

      if(InlineAttempt* IA = getInlineAttempt(CI)) {

	if(Function* F = getCalledFunction(CI)) {

	  unsigned i = 0;
	  for(Function::arg_iterator AI = F->arg_begin(), AE = F->arg_end(); AI != AE; ++AI, ++i) {
	  
	    if(V == CI->getArgOperand(i))
	      pass->queueUpdatePB(IA, AI);

	  }

	}

      }

    }
    else {
      pass->queueUpdatePB(this, I);
    }

  }
  else {
    if(parent)
      parent->queueUsersUpdatePBFalling(I, IL, V);
  }

}

void PeelAttempt::queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V) {

  for(unsigned i = 0; i < Iterations.size(); ++i)
    Iterations[i]->queueUsersUpdatePBRising(I, TargetL, V);

}

void IntegrationAttempt::queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V) {

  const Loop* MyL = getLoopContext();

  // Investigate here:
  queueUsersUpdatePBFalling(I, MyL, V);
  
  // And at inner contexts if possible.
  if(TargetL != MyL) {

    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(getLoopContext(), TargetL)))
      PA->queueUsersUpdatePBRising(I, TargetL, V);

  }

}

void IntegrationHeuristicsPass::runPointerBaseSolver(bool finalise, SmallVector<ValCtx, 64>* ChangedVCs) {

  SmallVector<ValCtx, 64>* ConsumeQ = (PBProduceQ == &PBQueue1) ? &PBQueue2 : &PBQueue1;
  
  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ValCtx, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());
    
    for(SmallVector<ValCtx, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      if(it->second->updateBasePointer(it->first, finalise) && ChangedVCs)
	ChangedVCs->push_back(*it);

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, PBProduceQ);

  }

}

void IntegrationHeuristicsPass::runPointerBaseSolver() {

  SmallVector<ValCtx, 64> ChangedVCs;

  runPointerBaseSolver(false, &ChangedVCs);

  PBProduceQ->insert(PBProduceQ->end(), ChangedVCs.begin(), ChangedVCs.end());
  
  runPointerBaseSolver(true, 0);

  ++PBGeneration;

}

uint64_t IntegrationHeuristicsPass::getPBGeneration() {

  return PBGeneration;

}

void IntegrationHeuristicsPass::queueUpdatePB(IntegrationAttempt* IA, Value* V) {

  PBProduceQ->push_back(make_vc(V, IA));
  
  IntegratorWQItem I;
  I.type = PBSolve;
  I.u.IHP = this;

  produceQueue->push_back(I);

}

void IntegrationAttempt::resolvePointerBase(Value* V, ValCtx Base) {

  pointerBases[V] = PointerBase::get(Base, pass->getPBGeneration());
  queueUsersUpdatePB(V);

}
