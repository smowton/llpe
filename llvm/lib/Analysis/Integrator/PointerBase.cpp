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

PointerBase PointerBase::get(ValCtx VC) {

  ValCtx CEGlobal;
  if(isa<Constant>(VC.first) && extractCEBase(cast<Constant>(VC.first), CEGlobal))
    return get(CEGlobal, ValSetTypePB);
  else if(isa<Constant>(VC.first) && (!VC.first->getType()->isPointerTy()))
    return get(VC, ValSetTypeScalar);
  else
    return get(VC, ValSetTypePB);
  
}

bool llvm::extractCEBase(Constant* C, ValCtx& VC) {

  if(isa<GlobalValue>(C)) {
    VC = const_vc(C);
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
    return extractCEBase(CE->getOperand(0), VC);
  case Instruction::Add:
  case Instruction::Sub:
    {
      ValCtx VC1, VC2;
      bool VC1Valid, VC2Valid;
      VC1Valid = extractCEBase(CE->getOperand(0), VC1);
      VC2Valid = extractCEBase(CE->getOperand(1), VC2);
      if(CE->getOpcode() == Instruction::Add) {

	if(VC1Valid == VC2Valid)
	  return false;
	VC = VC1Valid ? VC1 : VC2;
	return true;

      }
      else {

	if((!VC1Valid) || VC2Valid)
	  return false;
	VC = VC1;
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

    OutPB = PointerBase::get(const_vc(CE));
    return true;

  }

  DenseMap<Value*, PointerBase>::iterator it = pointerBases.find(V);
  if(it != pointerBases.end()) {
    OutPB = it->second;
    return true;
  }

  // This causes an infinite(?) loop at the moment. Not sure why.
  /*
  const Loop* MyL = getLoopContext();
  const Loop* VL = getValueScope(V);
  // Single-value results only stored at natural scope for now.
  if(MyL != VL)
    return false;

  ValCtx Repl = getReplacement(V);
  ValCtx ReplUO;
  if(Repl.second)
    ReplUO = Repl.second->getUltimateUnderlyingObject(Repl.first);
  else
    ReplUO = Repl;
  if(isa<Constant>(ReplUO.first) || isGlobalIdentifiedObject(ReplUO)) {

    OutPB = PointerBase::get(ReplUO);
    return true;

  }
  */

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
  if(getLoopContext())
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
    if(!getValSetOrReplacement(V, VPB, I)) {
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

void IntegrationAttempt::printPB(raw_ostream& out, PointerBase PB, bool brief) {

  if(PB.Overdef)
    out << "Overdef";
  else {
    out << "{ ";
    for(SmallVector<ValCtx, 4>::iterator it = PB.Values.begin(), it2 = PB.Values.end(); it != it2; ++it) {

      if(it != PB.Values.begin())
	out << ", ";
      out << itcache(*it, brief);

    }
    out << " }";
  }

}

bool IntegrationAttempt::updateUnaryValSet(Instruction* I, PointerBase &PB) {

  PointerBase ArgPB;
  if(!getPointerBase(I->getOperand(0), ArgPB, I))
    return false;
  if(ArgPB.Overdef) {
    PB = ArgPB;
    return true;
  }

  assert(ArgPB.Type != ValSetTypeUnknown);

  if(ArgPB.Type == ValSetTypeScalar) {

    switch(I->getOpcode()) {

    case Instruction::SExt:
    case Instruction::ZExt:
    case Instruction::Trunc:
      break;

    default:
      return false;

    }

    if(ArgPB.Values.size() == 1)
      return false;

    for(unsigned i = 0; i < ArgPB.Values.size() && !PB.Overdef; ++i) {

      PointerBase NewPB;

      Constant* Expr = ConstantExpr::getCast(I->getOpcode(), cast<Constant>(ArgPB.Values[i].first), I->getType());
      if(ConstantExpr* CE = dyn_cast<ConstantExpr>(Expr))
	Expr = ConstantFoldConstantExpression(CE, TD);

      if((!Expr) || isa<ConstantExpr>(Expr))
	NewPB = PointerBase::getOverdef();
      else
	NewPB = PointerBase::get(const_vc(Expr));
    
      PB.merge(NewPB);

    }

    return true;

  }
  else {

    PB = ArgPB;
    return true;

  }

}

bool IntegrationAttempt::getValSetOrReplacement(Value* V, PointerBase& PB, Instruction* UserI) {

  bool found;
  if(UserI)
    found = getPointerBase(V, PB, UserI);
  else
    found = getPointerBaseFalling(V, PB);

  if(found)
    return true;

  ValCtx Repl = getReplacement(V);
  ValCtx ReplUO;
  if(Repl.second)
    ReplUO = Repl.second->getUltimateUnderlyingObject(Repl.first);
  else
    ReplUO = Repl;
  if(isa<Constant>(ReplUO.first) || isGlobalIdentifiedObject(ReplUO)) {
    PB = PointerBase::get(ReplUO);
    return true;
  }

  return false;

}

bool IntegrationAttempt::updateBinopValSet(Instruction* I, PointerBase& PB) {

  PointerBase Op1PB;
  PointerBase Op2PB;

  bool Op1Valid = getValSetOrReplacement(I, Op1PB);
  bool Op2Valid = getValSetOrReplacement(I, Op2PB);

  if((!Op1Valid) && (!Op2Valid))
    return false;

  if(Op1Valid && Op2Valid) {

    if(Op1PB.Overdef || Op2PB.Overdef) {
      PB = PointerBase::getOverdef();
      return true;
    }

  }

  ValSetType RetType = (Op1PB.Type == ValSetTypePB || Op2PB.Type == ValSetTypePB) ? ValSetTypePB : ValSetTypeScalar;

  if(RetType == ValSetTypePB) {

    switch(I->getOpcode()) {

    case Instruction::Add:
      {
	if(Op1PB.Type == ValSetTypePB && Op2PB.Type == ValSetTypePB) {
	  LPDEBUG("Add of 2 pointers\n");
	  PB = PointerBase::getOverdef();
	}
	else {
	  PB = Op1PB.Type == ValSetTypePB ? Op1PB : Op2PB;
	}
	return true;
      }      
    case Instruction::Sub:
      {
	if(Op1PB.Type == ValSetTypePB && Op2PB.Type == ValSetTypePB) {
	  LPDEBUG("Subtract of 2 pointers (makes plain int)\n");
	  PB = PointerBase::getOverdef();
	}
	else {
	  PB = Op1PB.Type == ValSetTypePB ? Op1PB : Op2PB;
	}
	return true;
      }
    default:
      return false;

    }

  }
  else {

    if(Op1PB.Type != ValSetTypeScalar || Op2PB.Type != ValSetTypeScalar)
      return false;

    if(Op1PB.Values.size() == 1 && Op2PB.Values.size() == 1) {

      // Pointless, until the regular constant folder and this one are merged.
      return false;

    }

    for(unsigned i = 0; i < Op1PB.Values.size() && !PB.Overdef; ++i) {
      for(unsigned j = 0; j < Op2PB.Values.size() && !PB.Overdef; ++j) {
    
	Constant* Expr = ConstantExpr::get(I->getOpcode(), cast<Constant>(Op1PB.Values[i].first), cast<Constant>(Op2PB.Values[j].first));
	if(ConstantExpr* CE = dyn_cast<ConstantExpr>(Expr))
	  Expr = ConstantFoldConstantExpression(CE, TD);

	PointerBase ThisPB;

	if(Expr)
	  ThisPB = PointerBase::get(const_vc(Expr));
	else
	  ThisPB = PointerBase::getOverdef();

	PB.merge(ThisPB);

      }
    }

    return true;

  }

}

std::string IntegrationAttempt::describeLFA(LoadForwardAttempt& LFA) {
  
  std::string out;
  raw_string_ostream RSO(out);
  
  if(LFA.PB.Overdef) {
    for(unsigned i = 0; i < LFA.OverdefReasons.size(); ++i) {
      if(i != 0)
	RSO << ", ";
      RSO << LFA.OverdefReasons[i];
    }
  }  
  else if(LFA.PB.Values.size() == 0) {
    
    RSO << "No defn";
    
  }
  else {
    
    printPB(RSO, LFA.PB, true);
    
  }
    
  return out;
    
}
  
// Do load forwarding, possibly in optimistic mode: this means that
// stores that def but which have no associated PB are optimistically assumed
// to be compatible with anything, the same as the mergepoint logic above
// when finalise is false. When finalise = true this is just like normal load
// forwarding operating in PB mode.
bool IntegrationAttempt::tryForwardLoadPB(LoadInst* LI, bool finalise, PointerBase& NewPB) {

  LoadForwardAttempt Attempt(LI, this, LFMPB, TD);
  Attempt.PBOptimistic = !finalise;

  tryResolveLoad(Attempt);

  if(!finalise)
    optimisticForwardStatus[LI] = describeLFA(Attempt);
  else
    pessimisticForwardStatus[LI] = describeLFA(Attempt);
    
  if(Attempt.PB.Values.size() == 0 && !Attempt.PB.Overdef)
    return false;

  NewPB = Attempt.PB;
  return true;

}

bool IntegrationAttempt::updateBasePointer(Value* V, bool finalise) {

  // Don't duplicate the work of the pessimistic solver:
  if(getLoopContext() == getValueScope(V) && !isUnresolved(V))
    return false;

  LPDEBUG("Update pointer base " << itcache(*V) << "\n");
  PointerBase NewPB;

  PointerBase OldPB;
  bool OldPBValid = getPointerBaseFalling(V, OldPB);

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

    switch(I->getOpcode()) {

    case Instruction::GetElementPtr:
    case Instruction::BitCast:
    case Instruction::SExt:
    case Instruction::ZExt:
    case Instruction::IntToPtr:
    case Instruction::PtrToInt:

      if(!updateUnaryValSet(I, NewPB))
	return false;
      else
	break;

    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:      
      
      if(!updateBinopValSet(I, NewPB))
	return false;
      else
	break;

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
	bool mergeAnyInfo = getMergeBasePointer(I, finalise, NewPB);
	std::string RStr;
	raw_string_ostream RSO(RStr);
	printPB(RSO, NewPB);
	RSO.flush();
	if(!finalise)
	  optimisticForwardStatus[I] = RStr;
	else
	  pessimisticForwardStatus[I] = RStr;
	if(!mergeAnyInfo)
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

void IntegrationAttempt::printConsiderCount(DenseMap<ValCtx, int>& in, int n) {

  std::vector<std::pair<int, ValCtx> > results;
  for(DenseMap<ValCtx, int>::iterator it = in.begin(), it2 = in.end(); it != it2; ++it)
    results.push_back(std::make_pair(it->second, it->first));

  std::sort(results.begin(), results.end());
  
  for(int i = results.size() - 1; i >= 0 && i >= (results.size() - (n + 1)); --i)
    errs() << itcache(results[i].second) << ": " << results[i].first << "\n";

}

void IntegrationAttempt::queueWorkFromUpdatedPB(Value* V, PointerBase& PB) {

  if(PB.Type == ValSetTypeScalar) {
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

    if(blockIsDead(BI))
      continue;

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

void IntegrationAttempt::queuePBUpdateAllResolvedVCs() {

  for(DenseMap<Value*, PointerBase>::iterator it = pointerBases.begin(), it2 = pointerBases.end(); it != it2; ++it) {

    if(!it->second.Overdef)
      pass->queueUpdatePB(this, it->first);

  }

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->queuePBUpdateAllResolvedVCs();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->queuePBUpdateAllResolvedVCs();

  }

}

// Actually clear everything for now, for simplicity's sake.
void IntegrationAttempt::clearSuboptimalPBResults(DenseMap<ValCtx, PointerBase>& OldPBs) {

  //  std::vector<Value*> toErase;
  
  for(DenseMap<Value*, PointerBase>::iterator it = pointerBases.begin(), it2 = pointerBases.end(); it != it2; ++it) {

    OldPBs.insert(std::make_pair(make_vc(it->first, this), it->second));
    // toErase.push_back(it->first);

  }

  pointerBases.clear();

  //  for(unsigned i = 0; i < toErase.size(); ++i)
  //    pointerBases.erase(toErase[i]);

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->clearSuboptimalPBResults(OldPBs);

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->clearSuboptimalPBResults(OldPBs);

  }

}

void IntegrationAttempt::queueNewPBWork(DenseMap<ValCtx, PointerBase>& OldPBs, uint64_t& newVCs, uint64_t& changedVCs) {

  for(DenseMap<Value*, PointerBase>::iterator it = pointerBases.begin(), it2 = pointerBases.end(); it != it2; ++it) {

    if(it->second.Overdef)
      continue;

    DenseMap<ValCtx, PointerBase>::iterator OldPB = OldPBs.find(make_vc(it->first, this));
    bool queue = false;
    if(OldPB == OldPBs.end()) {
      newVCs++;
      queue = true;
    }
    else if(OldPB->second != it->second) {
      changedVCs++;
      queue = true;
    }

    if(queue)
      queueWorkFromUpdatedPB(it->first, it->second);

  }

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->queueNewPBWork(OldPBs, newVCs, changedVCs);

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->queueNewPBWork(OldPBs, newVCs, changedVCs);

  }

}

void IntegrationHeuristicsPass::runPointerBaseSolver(bool finalise) {

  DenseMap<ValCtx, int> considerCount;

  SmallVector<ValCtx, 64>* ConsumeQ = (PBProduceQ == &PBQueue1) ? &PBQueue2 : &PBQueue1;

  //int i = 0;
  
  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ValCtx, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());
    
    for(SmallVector<ValCtx, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      /*
      considerCount[*it]++;
      if(++i == 10000) {
	errs() << "----\n";
	it->second->printConsiderCount(considerCount, 100);
	errs() << "----\n";
	i = 0;
      }
      */

      it->second->updateBasePointer(it->first, finalise);

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, PBProduceQ);

  }

}

bool IntegrationHeuristicsPass::runPointerBaseSolver() {

  DenseMap<ValCtx, PointerBase> OldPBs;
  
  uint64_t totalVCs = 0, newVCs = 0, changedVCs = 0;

  // Step 1: discard all existing PB results that could be improved.
  RootIA->clearSuboptimalPBResults(OldPBs);

  // Step 2: consider every result in optimistic mode until stable.
  // In this mode, undefineds are ok and clobbers are ignored on the supposition that
  // they might turn into known pointers.
  // Overdefs are still bad.

  RootIA->queuePBUpdateAllUnresolvedVCs();
  totalVCs = PBProduceQ->size();

  runPointerBaseSolver(false);

  // Queue up anything of which we've asserted a non-overdef PB for reconsideration.
  RootIA->queuePBUpdateAllResolvedVCs();

  // Step 3: consider every result in pessimistic mode until stable: clobbers are back in,
  // and undefined == overdefined.

  runPointerBaseSolver(true);

  RootIA->queueNewPBWork(OldPBs, newVCs, changedVCs);

  errs() << "Ran optimistic solver: considered " << totalVCs << ", found " << newVCs << " new and " << changedVCs << " changed\n";

  return (newVCs + changedVCs) != 0;

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
