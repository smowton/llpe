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

static bool extractCEBase(Constant* C, PointerBase& PB) {

  if(isa<GlobalValue>(C)) {
    PB = PointerBase::get(const_vc(C));
    return true;
  }

  ConstantExpr* CE = dyn_cast<ConstantExpr>(C);
  if(!CE)
    return false;

  switch(CE->getOpcode()) {

  case Instruction::GetElementPtr:
  case Instruction::BitCast:
  case Instruction::SExt:
  case Instruction::ZExt:
  case Instruction::IntToPtr:
  case Instruction::PtrToInt:
    return extractCEBase(CE->getOperand(0), PB);
  case Instruction::Add:
  case Instruction::Sub:
    {
      PointerBase PB1, PB2;
      bool PB1Valid, PB2Valid;
      PB1Valid = extractCEBase(CE->getOperand(0), PB1);
      PB2Valid = extractCEBase(CE->getOperand(1), PB2);
      if(CE->getOpcode() == Instruction::Add) {

	if(PB1Valid == PB2Valid)
	  return false;
	PB = PB1Valid ? PB1 : PB2;
	return true;

      }
      else {

	if((!PB1Valid) || PB2Valid)
	  return false;
	PB = PB1;
	return true;

      }
      
    }

 default:
   return false;

  }

}

bool IntegrationAttempt::getPointerBaseLocal(Value* V, PointerBase& OutPB) {

  if(isa<AllocaInst>(V) || isNoAliasCall(V)) {

    OutPB = PointerBase::get(make_vc(V, this));
    return true;

  }
  else if(isa<GlobalValue>(V)) {

    OutPB = PointerBase::get(const_vc(cast<Constant>(V)));    
    return true;

  }
  else if(ConstantExpr* CE = dyn_cast<ConstantExpr>(V)) {

    return extractCEBase(CE, OutPB);

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

  if(isa<Constant>(V))
    return getPointerBaseLocal(V, OutPB);

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
bool IntegrationAttempt::getMergeBasePointer(Instruction* I, bool finalise, PointerBase& NewPB) {

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

  bool anyInfo = false;

  for(SmallVector<Value*, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2 && !NewPB.Overdef; ++it) {
    
    Value* V = *it;
    PointerBase VPB;
    if(!getPointerBase(V, VPB, I)) {
      if(finalise) {
	NewPB = PointerBase::getOverdef();
	return true;
      }
      else
	continue;      
    }

    anyInfo = true;
    NewPB.merge(VPB);

  }

  return anyInfo;

}

bool InlineAttempt::getArgBasePointer(Argument* A, PointerBase& OutPB) {

  if(!parent)
    return false;
  return parent->getPointerBaseFalling(CI->getArgOperand(A->getArgNo()), OutPB);

}

bool InlineAttempt::updateHeaderPHIPB(PHINode* PN, bool& NewPBValid, PointerBase& NewPB) {
  
  return false;

}

bool PeelIteration::updateHeaderPHIPB(PHINode* PN, bool& NewPBValid, PointerBase& NewPB) {
  
  if(L && L->getHeader() == PN->getParent()) {

    ValCtx Repl;
    if(getIterCount() == 0)
      Repl = make_vc(PN->getIncomingValueForBlock(L->getLoopPreheader()), parent);
    else {
      PeelIteration* PreviousIter = parentPA->getIteration(getIterCount() - 1);	      
      Repl = make_vc(PN->getIncomingValueForBlock(L->getLoopLatch()), PreviousIter);
    }
    NewPBValid = Repl.second->getPointerBaseFalling(Repl.first, NewPB);

    return true;

  }
  // Else, not a header PHI.
  return false;

}

void IntegrationAttempt::printPB(raw_ostream& out, PointerBase PB) {

  if(PB.Overdef)
    out << "Overdef";
  else {
    out << "{ ";
    for(SmallVector<ValCtx, 4>::iterator it = PB.Values.begin(), it2 = PB.Values.end(); it != it2; ++it) {

      if(it != PB.Values.begin())
	out << ", ";
      out << itcache(*it);

    }
    out << " }";
  }

}

bool IntegrationAttempt::updateBasePointer(Value* V, bool finalise) {

  LPDEBUG("Update pointer base " << itcache(*V) << "\n");
  PointerBase NewPB;

  PointerBase OldPB;
  bool OldPBValid = getPointerBaseFalling(V, OldPB);

  if(Argument* A = dyn_cast<Argument>(V)) {

    PointerBase PB;
    InlineAttempt* IA = getFunctionRoot();
    if(!IA->getArgBasePointer(A, NewPB)) {

      // No information from our argument
      return false;

    }

  }
  else {

    Instruction* I = cast<Instruction>(V);

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
	  NewPB = PB;
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
	  NewPB = PointerBase::getOverdef();
	}
	else if((!found1) && (!found2)) {
	  return false;
	}
	else {
	  NewPB = found1 ? PB1 : PB2;
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
	  NewPB = PB1;
	}
	else {
	  return false;
	}
	break;
      }
    case Instruction::PHI:
      {
	bool NewPBValid;
	if(updateHeaderPHIPB(cast<PHINode>(I), NewPBValid, NewPB)) {
	  if(!NewPBValid)
	    return false;
	  else
	    break;
	}
	// Else fall through:
      }
    case Instruction::Select:
      {
	if(!getMergeBasePointer(I, finalise, NewPB))
	  return false;
	else
	  break;
      }
    default:
      // Unknown instruction, draw no conclusions.
      return false;
    }

  }

  if((!OldPBValid) || OldPB != NewPB) {

    pointerBases[V] = NewPB;

    LPDEBUG("Updated dep to ");
    DEBUG(printPB(dbgs(), NewPB));
    DEBUG(dbgs() << "\n");
  
    queueUsersUpdatePB(V, !NewPB.Overdef);

    return true;

  }
  
  return false;

}

// This is different to HCF's investigateUsers code because it investigates different scopes.
// We investigate: (1) the user's 'natural' scope (since this catches exit PHIs), and
// (2) if the user is within our scope, all scopes between ours and its 
// (since our new invariant information might be useful at many scopes).
void IntegrationAttempt::queueUsersUpdatePB(Value* V, bool VDefined) {

  const Loop* MyL = getLoopContext();
  
  for(Value::use_iterator UI = V->use_begin(), UE = V->use_end(); UI != UE; ++UI) {

    if(Instruction* UserI = dyn_cast<Instruction>(*UI)) {

      const Loop* UserL = getValueScope(UserI);

      if((!MyL) || (UserL && MyL->contains(UserL))) {
	  
	queueUsersUpdatePBRising(UserI, UserL, V, VDefined);
	
      }
      else {
	
	queueUsersUpdatePBFalling(UserI, UserL, V, VDefined);

      }

    }

  }

}

void IntegrationAttempt::queueUsersUpdatePBFalling(Instruction* I, const Loop* IL, Value* V, bool VDefined) {

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
      if(VDefined)
	queueWorkBlockedOn(I);
    }

  }
  else {
    if(parent)
      parent->queueUsersUpdatePBFalling(I, IL, V, VDefined);
  }

}

void PeelAttempt::queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, bool VDefined) {

  for(unsigned i = 0; i < Iterations.size(); ++i)
    Iterations[i]->queueUsersUpdatePBRising(I, TargetL, V, VDefined);

}

void IntegrationAttempt::queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, bool VDefined) {

  const Loop* MyL = getLoopContext();

  // Investigate here:
  queueUsersUpdatePBFalling(I, MyL, V, VDefined);
  
  // And at inner contexts if possible.
  if(TargetL != MyL) {

    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(getLoopContext(), TargetL)))
      PA->queueUsersUpdatePBRising(I, TargetL, V, VDefined);

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
  I.ctx = 0;
  I.u.IHP = this;

  produceQueue->push_back(I);

}

void IntegrationAttempt::resolvePointerBase(Value* V, PointerBase& PB) {

  PointerBase ExistingPB;
  if((!getPointerBaseLocal(V, ExistingPB)) || ExistingPB != PB) {
    pointerBases[V] = PB;
    queueUsersUpdatePB(V, true);
  }

}

bool InlineAttempt::ctxContains(IntegrationAttempt* IA) {

  return this == IA;

}

bool PeelIteration::ctxContains(IntegrationAttempt* IA) {

  if(this == IA)
    return true;
  return parent->ctxContains(IA);

}

bool IntegrationAttempt::basesMayAlias(ValCtx VC1, ValCtx VC2) {

  if(VC1.first == VC2.first) {

    if((!VC1.second) || (!VC2.second))
      return true;

    if(VC1.second->ctxContains(VC2.second) || VC2.second->ctxContains(VC1.second))
      return true;

  }

  return false;

}
