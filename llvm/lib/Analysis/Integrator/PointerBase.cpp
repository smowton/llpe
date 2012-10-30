// Implementation of an SCCP-like solver to discover the base object pointers refer to.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Function.h"
#include "llvm/Constants.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instruction.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ConstantFolding.h"
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

    if(VPB.Overdef && !finalise)
      continue;
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

bool IntegrationAttempt::isScalarSet(PointerBase& PB) {

  if(PB.Overdef)
    return false;
  assert(PB.Values.size());
  if(PB.Values[0].first->getType()->isPointerTy())
    return false;
  if(PB.Values[0].second)
    return false;
  if(ConstantExpr* CE = dyn_cast<ConstantExpr>(PB.Values[0].first)) {
    PointerBase Ign;
    if(extractCEBase(CE, Ign))
      return false;
  }

  return true;

}



bool IntegrationAttempt::getScalarSet(Value* V, Instruction* UserI, SmallVector<Constant*, 4>& Result) {

  PointerBase PB;
  bool found = getPointerBase(V, PB, UserI);
  if(found) {
    
    if(!isScalarSet(PB))
      return false;

    // That *should* eliminate everything but integers, FP, and other things not related to pointers.
    for(unsigned i = 0; i < PB.Values.size(); ++i) {
      Result.push_back(cast<Constant>(PB.Values[i].first));
    }
    return true;

  }

  Constant* C = getConstReplacement(V);
  if(!C)
    return false;

  PointerBase Ign;
  if(C->getType()->isPointerTy() || extractCEBase(C, Ign))
    return false;

  Result.push_back(C);
  return true;

}

bool IntegrationAttempt::updateBinopValues(Instruction* I, PointerBase& PB, bool& isScalarBinop) {

  switch(I->getOpcode()) {
  case Instruction::Add:
  case Instruction::Sub:
  case Instruction::And:
  case Instruction::Or:
  case Instruction::Xor:
    break;
  default:
    return false;
  }

  SmallVector<Constant*, 4> Op1Vals;
  SmallVector<Constant*, 4> Op2Vals;

  if((!getScalarSet(I->getOperand(0), I, Op1Vals)) || (!getScalarSet(I->getOperand(1), I, Op2Vals)))
    return false;

  // Prevent treating these like pointer bases.
  isScalarBinop = true;

  if(Op1Vals.size() == 1 && Op2Vals.size() == 1) {

    // Pointless, until the regular constant folder and this one are merged.
    return false;

  }

  for(unsigned i = 0; i < Op1Vals.size() && !PB.Overdef; ++i) {
    for(unsigned j = 0; j < Op2Vals.size() && !PB.Overdef; ++j) {
    
      Constant* Expr = ConstantExpr::get(I->getOpcode(), Op1Vals[i], Op2Vals[j]);
      if(ConstantExpr* CE = dyn_cast<ConstantExpr>(Expr))
	Expr = ConstantFoldConstantExpression(CE, TD);

      if(Expr) {

	PB.insert(const_vc(Expr));

      }
      else {

	return false;

      }

    }
  }

  return PB.Values.size() > 0 && !PB.Overdef;
  
}

// Do load forwarding, possibly in optimistic mode: this means that
// stores that def but which have no associated PB are optimistically assumed
// to be compatible with anything, the same as the mergepoint logic above
// when finalise is false. When finalise = true this is just like normal load
// forwarding operating in PB mode.
bool IntegrationAttempt::tryForwardLoadPB(LoadInst* LI, bool finalise, PointerBase& NewPB) {

  LoadForwardAttempt Attempt(LI, this, TD);
  Attempt.PBOptimistic = !finalise;
  tryResolveLoad(Attempt, LFMPB);
  if(Attempt.PB.Values.size() == 0 && !Attempt.PB.Overdef)
    return false;

  NewPB = Attempt.PB;
  return true;

}

bool IntegrationAttempt::updateBasePointer(Value* V, bool finalise) {

  LPDEBUG("Update pointer base " << itcache(*V) << "\n");
  PointerBase NewPB;

  PointerBase OldPB;
  bool OldPBValid = getPointerBaseFalling(V, OldPB);

  // Getting no better:
  if((!finalise) && OldPBValid && (!OldPB.Overdef) && OldPB.Values.size() == 1)
    return false;

  // Getting no worse:
  if(finalise && ((!OldPBValid) || OldPB.Overdef))
    return false;

  if(LoadInst* LI = dyn_cast<LoadInst>(V)) {

    if(!tryForwardLoadPB(LI, finalise, NewPB))
      return false;

  }
  else if(Argument* A = dyn_cast<Argument>(V)) {

    PointerBase PB;
    InlineAttempt* IA = getFunctionRoot();
    if(!IA->getArgBasePointer(A, NewPB)) {

      // No information from our argument
      return false;

    }

  }
  else {

    Instruction* I = cast<Instruction>(V);

    bool handled = false;

    switch(I->getOpcode()) {

    case Instruction::GetElementPtr:
    case Instruction::BitCast:
    case Instruction::SExt:
    case Instruction::ZExt:
    case Instruction::IntToPtr:
    case Instruction::PtrToInt:

      {
	PointerBase PB;
	handled = true;
	if(getPointerBase(I->getOperand(0), PB, I))
	  NewPB = PB;
	else
	  return false;
	break;
      }

    }

    if(!handled) {

      bool isScalarBinop = false;
      if(updateBinopValues(I, NewPB, isScalarBinop))
	handled = true;
      if(isScalarBinop)
	return false;

    }
    
    if(!handled) {

      switch(I->getOpcode()) {

      case Instruction::Add:
	{
	  PointerBase PB1, PB2;
	  bool found1 = getPointerBase(I->getOperand(0), PB1, I);
	  bool found2 = getPointerBase(I->getOperand(1), PB2, I);
	  if((!found1) && (!found2)) {
	    return false;
	  }

	  if(found1 && found2) {
	    LPDEBUG("Add of 2 pointers\n");
	    NewPB = PointerBase::getOverdef();
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

  }

  if((!OldPBValid) || OldPB != NewPB) {

    pointerBases[V] = NewPB;

    LPDEBUG("Updated dep to ");
    DEBUG(printPB(dbgs(), NewPB));
    DEBUG(dbgs() << "\n");
  
    queueUsersUpdatePB(V);

    return true;

  }
  
  return false;

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
    else if(isa<StoreInst>(I)) {

      DenseMap<Instruction*, SmallVector<std::pair<IntegrationAttempt*, LoadInst*>, 4> >::iterator it = 
	InstBlockedLoads.find(I);
      if(it != InstBlockedLoads.end()) {

	for(SmallVector<std::pair<IntegrationAttempt*, LoadInst*>, 4>::iterator II = it->second.begin(),
	      IE = it->second.end(); II != IE; ++II) {

	  pass->queueUpdatePB(this, II->second);

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

struct ChangedPB {

  bool OldPBValid;
  PointerBase OldPB;

  ChangedPB(bool O, PointerBase OP) : OldPBValid(O), OldPB(OP) { }

};

void IntegrationHeuristicsPass::runPointerBaseSolver(bool finalise, DenseMap<ValCtx, ChangedPB>* ChangedVCs) {

  SmallVector<ValCtx, 64>* ConsumeQ = (PBProduceQ == &PBQueue1) ? &PBQueue2 : &PBQueue1;
  
  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ValCtx, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());
    
    for(SmallVector<ValCtx, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      PointerBase OldPB;
      bool OldPBValid = it->second->getPointerBaseFalling(it->first, OldPB);

      if(it->second->updateBasePointer(it->first, finalise) && ChangedVCs) {
	// Note the VC's pre-solver PB the first time we update it.
	ChangedVCs->insert(std::make_pair(*it, ChangedPB(OldPBValid, OldPB)));
      }

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, PBProduceQ);

  }

}

void IntegrationAttempt::queueWorkFromUpdatedPB(Value* V, PointerBase& PB) {

  if(isScalarSet(PB)) {
    if(PB.Values.size() == 1) {

      // Feed the result to the ordinary constant folder, until the two get merged.
      setReplacement(V, PB.Values[0]);
      investigateUsers(V);

    }
  }
  else {
    // Set of pointer bases. Retry any load that might benefit (i.e. those at the affected scope
    // and its children).
    investigateUsers(V);
  }

}

void IntegrationAttempt::queuePBUpdateIfUnresolved(Value *V) {

  if(!isUnresolved(V))
    return;

  PointerBase PB;
  bool PBValid = getPointerBaseFalling(V, PB);
  if(PBValid && PB.Values.size() == 1)
    return;

  pass->queueUpdatePB(this, V);

}

void IntegrationAttempt::queuePBUpdateAllUnresolvedVCsInScope(const Loop* L) {

  if(!getLoopContext()) {

    for(Function::arg_iterator AI = F.arg_begin(), AE = F.arg_end(); AI != AE; ++AI) {

      queuePBUpdateIfUnresolved(AI);

    }

  }

  for(Function::iterator BI = F.begin(), BE = F.end(); BI != BE; ++BI) {

    BasicBlock* BB = BI;
    const Loop* BBL = getBlockScopeVariant(BB);
    if((!L) || (BBL && L->contains(BBL))) {

      for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II) {
	
	queuePBUpdateIfUnresolved(II);

      }

    }

  }  

}

void IntegrationAttempt::queuePBUpdateAllUnresolvedVCs() {

  queuePBUpdateAllUnresolvedVCsInScope(getLoopContext());

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->queuePBUpdateAllUnresolvedVCs();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->queuePBUpdateAllUnresolvedVCs();

  }

}

bool IntegrationHeuristicsPass::runPointerBaseSolver() {

  DenseMap<ValCtx, ChangedPB> ChangedVCs;
  
  uint64_t totalVCs = 0, optimisticVCs = 0, pessimisticVCs = 0;
  RootIA->queuePBUpdateAllUnresolvedVCs();
  totalVCs = PBProduceQ->size();

  runPointerBaseSolver(false, &ChangedVCs);
  optimisticVCs = ChangedVCs.size();

  for(DenseMap<ValCtx, ChangedPB>::iterator it = ChangedVCs.begin(), it2 = ChangedVCs.end(); it != it2; ++it) {

    PBProduceQ->push_back(it->first);

  }

  runPointerBaseSolver(true, 0);

  for(DenseMap<ValCtx, ChangedPB>::iterator it = ChangedVCs.begin(), it2 = ChangedVCs.end(); it != it2; ++it) {

    PointerBase NewPB;
    bool NewPBValid = it->first.second->getPointerBaseFalling(it->first.first, NewPB);
    assert(NewPBValid && "Ended up in changed queue despite not defining a PB?");

    if(NewPB.Overdef)
      continue;

    if(it->second.OldPBValid && (NewPB == it->second.OldPB))
      continue;

    pessimisticVCs++;
    it->first.second->queueWorkFromUpdatedPB(it->first.first, NewPB);

  }

  errs() << "Ran optimistic solver: considered " << totalVCs << ", found " << optimisticVCs << " optimistic values, kept " << pessimisticVCs << "\n";

  return pessimisticVCs != 0;

}

void IntegrationHeuristicsPass::queueUpdatePB(IntegrationAttempt* IA, Value* V) {

  PBProduceQ->push_back(make_vc(V, IA));

}

void IntegrationAttempt::resolvePointerBase(Value* V, PointerBase& PB) {

  PointerBase ExistingPB;
  if((!getPointerBaseLocal(V, ExistingPB)) || ExistingPB != PB) {
    pointerBases[V] = PB;
    // Don't queue, just wait for the next round of optimistic solving.
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
