// Implementation of an SCCP-like solver to discover the base object pointers refer to.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Function.h"
#include "llvm/Constants.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instruction.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Support/Debug.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Analysis/MemoryBuiltins.h"

using namespace llvm;

static double time_diff(struct timespec& start, struct timespec& end) {

  timespec temp;
  if ((end.tv_nsec-start.tv_nsec)<0) {
    temp.tv_sec = end.tv_sec-start.tv_sec-1;
    temp.tv_nsec = 1000000000+end.tv_nsec-start.tv_nsec;
  } else {
    temp.tv_sec = end.tv_sec-start.tv_sec;
    temp.tv_nsec = end.tv_nsec-start.tv_nsec;
  }

  return (temp.tv_sec) + (((double)temp.tv_nsec) / 1000000000.0);

}

PointerBase PointerBase::get(ValCtx VC) {

  ValCtx CEGlobal;
  const PointerType* PTy = dyn_cast<PointerType>(VC.first->getType());
  bool isFunctionTy = PTy && PTy->getElementType()->isFunctionTy();

  // Treat function pointers like scalars, since they're not indexable objects.

  if(isa<Constant>(VC.first) && extractCEBase(cast<Constant>(VC.first), CEGlobal))
    return get(CEGlobal, ValSetTypePB);
  else if(isa<Constant>(VC.first) && (isFunctionTy || !PTy))
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

bool IntegrationAttempt::hasResolvedPB(Value* V) {

  // A little different to isUnresolved: that would call GEP of X where X has a known replacement resolved. We explicitly eval that GEP.
  // This method will become the one true method once the two folders merge.

  if(isa<AllocaInst>(V) || isNoAliasCall(V))
    return true;

  if(getReplacement(V) != getDefaultVC(V))
    return true;

  return false;

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

  bool verbose = false;
  
  SmallVector<std::pair<ValCtx, Instruction*>, 4> Vals;
  if(SelectInst* SI = dyn_cast<SelectInst>(I)) {

    Vals.push_back(std::make_pair(make_vc(SI->getTrueValue(), this), SI));
    Vals.push_back(std::make_pair(make_vc(SI->getFalseValue(), this), SI));

  }
  else if(CallInst* CI = dyn_cast<CallInst>(I)) {

    if(CI->getType()->isVoidTy())
      return false;

    if(InlineAttempt* IA = getInlineAttempt(CI)) {

      Function* F = getCalledFunction(CI);
      for(Function::iterator it = F->begin(), it2 = F->end(); it != it2; ++it) {

	if(ReturnInst* RI = dyn_cast<ReturnInst>(it->getTerminator())) {

	  if(IA->blockIsDead(RI->getParent()))
	    continue;
	  
	  Vals.push_back(std::make_pair(make_vc(RI->getOperand(0), IA), RI));

	}

      }

    }
    else {
      return false;
    }

  }
  else {

    PHINode* PN = cast<PHINode>(I);
    for(unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
      if(edgeIsDead(PN->getIncomingBlock(i), PN->getParent()))
	continue;
      Vals.push_back(std::make_pair(make_vc(PN->getIncomingValue(i), this), PN));
    }

  }

  bool anyInfo = false;

  if(verbose) {

    errs() << "=== START PHI MERGE for " << itcache(*I) << " (finalise = " << finalise << ")\n";

    IntegrationAttempt* PrintCtx = this;
    while(PrintCtx) {
      errs() << PrintCtx->getShortHeader() << ", ";
      PrintCtx = PrintCtx->parent;
    }
    errs() << "\n";

  }

  for(SmallVector<std::pair<ValCtx, Instruction*>, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2 && !NewPB.Overdef; ++it) {
    
    Value* V = it->first.first;
    IntegrationAttempt* VCtx = it->first.second;
    Instruction* VUser = it->second;
    PointerBase VPB;
    if(!VCtx->getValSetOrReplacement(V, VPB, VUser)) {
      if(verbose)
	errs() << "Predecessor " << itcache(make_vc(V, VCtx)) << " undefined\n";
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

  switch(PB.Type) {
  case ValSetTypeScalar:
    out << "S "; break;
  case ValSetTypePB:
    out << "PB "; break;
  case ValSetTypeUnknown:
    out << "U "; break;
  }

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

  if(!getValSetOrReplacement(I->getOperand(0), ArgPB, I))
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

  bool found;
  if(UserI)
    found = getPointerBase(V, PB, UserI);
  else
    found = getPointerBaseFalling(V, PB);

  if(found)
    return true;

  return false;

}

bool IntegrationAttempt::updateBinopValSet(Instruction* I, PointerBase& PB) {

  PointerBase Op1PB;
  PointerBase Op2PB;

  bool Op1Valid = getValSetOrReplacement(I->getOperand(0), Op1PB);
  bool Op2Valid = getValSetOrReplacement(I->getOperand(1), Op2PB);

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

    /*
    if(Op1PB.Values.size() == 1 && Op2PB.Values.size() == 1) {

      // Pointless, until the regular constant folder and this one are merged.
      return false;

    }
    */
    
    // Need this to establish value recurrences, e.g. a loop with store-to-load (or phi-to-phi) feeds which circulates a known value or value set.

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

void IntegrationAttempt::addMemWriterEffect(Instruction* I, LoadInst* LI, IntegrationAttempt* Ctx) {

  memWriterEffects[I].insert(std::make_pair(LI, Ctx));

}

bool IntegrationAttempt::updateBasePointer(Value* V, bool finalise, LoopPBAnalyser* LPBA) {

  // Quick escape for values we can't handle:

  bool verbose = false;

  if(Instruction* I = dyn_cast<Instruction>(V)) {
    
    switch(I->getOpcode()) {

    case Instruction::GetElementPtr:
    case Instruction::BitCast:
    case Instruction::SExt:
    case Instruction::ZExt:
    case Instruction::IntToPtr:
    case Instruction::PtrToInt:
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:      
    case Instruction::PHI:
    case Instruction::Select:
    case Instruction::Load:
    case Instruction::Call:
      break;
    default:
      // Unknown instruction, draw no conclusions.
      return false;
      
    }

  }

  // Don't duplicate the work of the pessimistic solver:
  if(getLoopContext() == getValueScope(V) && hasResolvedPB(V))
    return false;

  if(verbose)
    errs() << "Update pointer base " << itcache(*V) << "\n";
  PointerBase NewPB;

  PointerBase OldPB;
  bool OldPBValid = getPointerBaseFalling(V, OldPB);

  // Getting no worse:
  if(finalise && LPBA && ((!OldPBValid) || OldPB.Overdef))
    return false;

  if(LoadInst* LI = dyn_cast<LoadInst>(V)) {

    bool ret = tryForwardLoadPB(LI, finalise, NewPB);
    if(!ret)
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
    case Instruction::Call:
      {
	bool mergeAnyInfo = getMergeBasePointer(I, finalise, NewPB);
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

  assert(NewPB.Overdef || (NewPB.Type != ValSetTypeUnknown));

  if((!OldPBValid) || OldPB != NewPB) {

    if(Instruction* I = dyn_cast<Instruction>(V)) {
      if(!isa<LoadInst>(V)) {
	std::string RStr;
	raw_string_ostream RSO(RStr);
	printPB(RSO, NewPB, true);
	RSO.flush();
	if(!finalise)
	  optimisticForwardStatus[I] = RStr;
	else
	  pessimisticForwardStatus[I] = RStr;
      }
    }

    pointerBases[V] = NewPB;

    if(verbose) {
      errs() << "Updated dep to ";
      printPB(errs(), NewPB);
      errs() << "\n";
    }
  
    if(LPBA)
      queueUsersUpdatePB(V, LPBA);

    return true;

  }
  
  return false;

}

void InlineAttempt::queueUpdateCall(LoopPBAnalyser* LPBA) {

  if(parent)
    queueUpdatePB(parent, CI, LPBA);

}

// This is different to HCF's investigateUsers code because it investigates different scopes.
// We investigate: (1) the user's 'natural' scope (since this catches exit PHIs), and
// (2) if the user is within our scope, all scopes between ours and its 
// (since our new invariant information might be useful at many scopes).
void IntegrationAttempt::queueUsersUpdatePB(Value* V, LoopPBAnalyser* LPBA) {

  for(Value::use_iterator UI = V->use_begin(), UE = V->use_end(); UI != UE; ++UI) {

    if(Instruction* UserI = dyn_cast<Instruction>(*UI)) {

      queueUserUpdatePB(V, UserI, LPBA);

    }

  }

}

void IntegrationAttempt::queueUserUpdatePB(Value* V, Instruction* UserI, LoopPBAnalyser* LPBA) {

  const Loop* MyL = getLoopContext();
  
  if(isa<ReturnInst>(UserI)) {
	
    getFunctionRoot()->queueUpdateCall(LPBA);
	
  }

  const Loop* UserL = getValueScope(UserI);

  if((!MyL) || (UserL && MyL->contains(UserL))) {
	  
    queueUsersUpdatePBRising(UserI, UserL, V, LPBA);
	
  }
  else {
	
    queueUsersUpdatePBFalling(UserI, UserL, V, LPBA);

  }
  
}

void IntegrationAttempt::queueUpdatePB(IntegrationAttempt* Ctx, Value* V, LoopPBAnalyser* LPBA) {
  
  LPBA->queueIfConsidered(make_vc(V, Ctx));

}

void IntegrationAttempt::queueUsersUpdatePBFalling(Instruction* I, const Loop* IL, Value* V, LoopPBAnalyser* LPBA) {

  if(getLoopContext() == IL) {

    if(blockIsDead(I->getParent()))
      return;

    if((!isa<CallInst>(I)) && getValueScope(I) == getLoopContext() && hasResolvedPB(I)) {

      // No point investigating instructions whose concrete values are already known.
      return;

    }

    if(CallInst* CI = dyn_cast<CallInst>(I)) {

      if(InlineAttempt* IA = getInlineAttempt(CI)) {

	if(Function* F = getCalledFunction(CI)) {

	  unsigned i = 0;
	  for(Function::arg_iterator AI = F->arg_begin(), AE = F->arg_end(); AI != AE; ++AI, ++i) {
	  
	    if(V == CI->getArgOperand(i)) {
	      queueUpdatePB(IA, AI, LPBA);
	    }

	  }

	}

      }

    }
    else if(isa<StoreInst>(I)) {

      DenseMap<Instruction*, DenseSet<std::pair<LoadInst*, IntegrationAttempt*> > >::iterator it = 
	memWriterEffects.find(I);
      if(it != memWriterEffects.end()) {

	for(DenseSet<std::pair<LoadInst*, IntegrationAttempt*> >::iterator SI = it->second.begin(), SE = it->second.end(); SI != SE; ++SI) {

	  queueUpdatePB(SI->second, SI->first, LPBA);

	}

      }

    }
    else {
      queueUpdatePB(this, I, LPBA);
    }

  }
  else {
    if(parent)
      parent->queueUsersUpdatePBFalling(I, IL, V, LPBA);
  }

}

void PeelAttempt::queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, LoopPBAnalyser* LPBA) {

  for(unsigned i = 0; i < Iterations.size(); ++i)
    Iterations[i]->queueUsersUpdatePBRising(I, TargetL, V, LPBA);

}

void IntegrationAttempt::queueUsersUpdatePBRising(Instruction* I, const Loop* TargetL, Value* V, LoopPBAnalyser* LPBA) {

  const Loop* MyL = getLoopContext();
  const Loop* NextL = TargetL == MyL ? TargetL : immediateChildLoop(MyL, TargetL);
  bool investigateHere = true;

  if(TargetL != MyL) {

    if(PeelAttempt* PA = getPeelAttempt(NextL)) {
      if(PA->Iterations.back()->iterStatus == IterationStatusFinal)
	investigateHere = false;
      PA->queueUsersUpdatePBRising(I, TargetL, V, LPBA);
    }

  }

  if(investigateHere)
    queueUsersUpdatePBFalling(I, MyL, V, LPBA);

}

bool IntegrationAttempt::shouldCheckPB(Value* V) {

  bool verbose = false;

  if(verbose)
    errs() << "shouldCheckPB " << itcache(make_vc(V, this)) << "\n";

  if(contextIsDead) {
    if(verbose)
      errs() << "Ctx dead\n";
    return false;
  }

  if(hasResolvedPB(V)) {
    if(verbose)
      errs() << "Resolved already: repl " << itcache(getReplacement(V)) << " vs default " << itcache(getDefaultVC(V)) << "\n";
    return false;
  }

  if(Instruction* I = dyn_cast<Instruction>(V)) {
    if(blockIsDead(I->getParent())) {
      if(verbose)
	errs() << "Block dead\n";
      return false;
    }
  }

  const Loop* MyL = getLoopContext();
  const Loop* VL = getValueScope(V);
				     
  if(MyL != VL) {

    // Check if there's a terminated loop above us which would cause this query
    // to malfunction (we'd jump into the last iteration without transiting
    // an exit edge; to fix?)

    // Extend this to all values: if there's a terminated loop we can just identify its value
    // per iteration as usual.

    if(MyL && !MyL->contains(VL)) {
      if(verbose)
	errs() << "Not within context loop\n";
      return false;
    }

    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(MyL, VL))) {

      if(PA->Iterations.back()->iterStatus == IterationStatusFinal) {
	if(verbose)
	  errs() << "Under a terminated loop\n";
	return false;
      }

    }

  }

  PointerBase PB;
  bool PBValid = getPointerBaseFalling(V, PB);
  if(PBValid && PB.Values.size() == 1) {
    if(verbose)
      errs() << "Has optimal PB\n";
    return false;
  }

  if(verbose)
    errs() << "Will check\n";
  return true;

}

void IntegrationAttempt::queuePBUpdateIfUnresolved(Value *V, LoopPBAnalyser* LPBA) {

  if(shouldCheckPB(V)) {
    
    LPBA->addVC(make_vc(V, this));
    //errs() << "Queue " << itcache(make_vc(V, this)) << "\n";
    pointerBases.erase(V);

  }
  else {

    LPDEBUG("Shouldn't check " << itcache(make_vc(V, this)) << "\n");

  }

}

void IntegrationAttempt::queuePBUpdateAllUnresolvedVCsInScope(const Loop* L, LoopPBAnalyser* LPBA) {

  if((!getLoopContext()) && !L) {

    for(Function::arg_iterator AI = F.arg_begin(), AE = F.arg_end(); AI != AE; ++AI) {

      queuePBUpdateIfUnresolved(AI, LPBA);

    }

  }

  for(Function::iterator BI = F.begin(), BE = F.end(); BI != BE; ++BI) {

    if(blockIsDead(BI))
      continue;

    BasicBlock* BB = BI;
    const Loop* BBL = LI[&F]->getLoopFor(BB);
    if((!L) || (BBL && L->contains(BBL))) {

      for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II) {
	
	queuePBUpdateIfUnresolved(II, LPBA);

      }

    }

  }  

}

void IntegrationAttempt::queueUpdatePBWholeLoop(const Loop* L, LoopPBAnalyser* LPBA) {

  //errs() << "QUEUE WHOLE LOOP " << (L ? L->getHeader()->getName() : F.getName()) << "\n";

  //bool verbose = false;

  queuePBUpdateAllUnresolvedVCsInScope(L, LPBA);

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if((!L) || L->contains(it->first->getParent()))
      it->second->queueUpdatePBWholeLoop(0, LPBA);

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    if(L->contains(it->first) && it->second->Iterations.back()->iterStatus == IterationStatusFinal) {
      for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
	it->second->Iterations[i]->queueUpdatePBWholeLoop(it->first, LPBA);
    }

  }

}

// Currently unused:
/*
static bool isBetterThanOrEqual(PointerBase& NewPB, PointerBase& OldPB) {

  if(OldPB.Overdef)
    return true;

  if(NewPB.Overdef)
    return false;

  return NewPB.Values.size() <= OldPB.Values.size();

}
*/

void LoopPBAnalyser::runPointerBaseSolver(bool finalise, std::vector<ValCtx>* modifiedVCs) {

  DenseMap<ValCtx, int> considerCount;

  SmallVector<ValCtx, 64>* ConsumeQ = (PBProduceQ == &PBQueue1) ? &PBQueue2 : &PBQueue1;

  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ValCtx, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());

    for(SmallVector<ValCtx, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      assert(inLoopVCs.count(*it));

      struct timespec start;
      clock_gettime(CLOCK_REALTIME, &start);

      if(it->second->updateBasePointer(it->first, finalise, this)) {
	if(modifiedVCs) {
	  modifiedVCs->push_back(*it);
	}
      }

      struct timespec end;
      clock_gettime(CLOCK_REALTIME, &end);

      if(time_diff(start, end) > 0.1) {

	errs() << "Consider " << (*ConsumeQ)[0].second->itcache(*it) << " took " << time_diff(start, end) << "\n";

      }

      //++(considerCount[*it]);

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, PBProduceQ);

  }

  /*
  std::vector<std::pair<int, ValCtx> > sortCounts;

  for(DenseMap<ValCtx, int>::iterator it = considerCount.begin(), it2 = considerCount.end(); it != it2; ++it) {

    sortCounts.push_back(std::make_pair(it->second, it->first));

  }

  std::sort(sortCounts.begin(), sortCounts.end());

  for(std::vector<std::pair<int, ValCtx> >::iterator it = sortCounts.begin(), it2 = sortCounts.end(); it != it2; ++it) {

    errs() << it->first << ": " << sortCounts[0].second.second->itcache(it->second) << "\n";

  }
  */

}

void LoopPBAnalyser::run() {

  struct timespec start;
  clock_gettime(CLOCK_REALTIME, &start);

  std::vector<ValCtx> updatedVCs;
  runPointerBaseSolver(false, &updatedVCs);

  struct timespec optend;
  clock_gettime(CLOCK_REALTIME, &optend);

  std::sort(updatedVCs.begin(), updatedVCs.end());
  std::vector<ValCtx>::iterator startit, endit;
  endit = std::unique(updatedVCs.begin(), updatedVCs.end());

  struct timespec sortend;
  clock_gettime(CLOCK_REALTIME, &sortend);

  for(startit = updatedVCs.begin(); startit != endit; ++startit) {
	
    queueUpdatePB(make_vc(startit->first, startit->second));

  }

  struct timespec requeueend;
  clock_gettime(CLOCK_REALTIME, &requeueend);

  runPointerBaseSolver(true, 0);

  struct timespec pesend;
  clock_gettime(CLOCK_REALTIME, &pesend);

  for(startit = updatedVCs.begin(); startit != endit; ++startit) {

    startit->second->tryPromoteSingleValuedPB(startit->first);
    
  }

  struct timespec end;
  clock_gettime(CLOCK_REALTIME, &end);

  errs() << "Analysis phases: opt " << time_diff(start, optend) << ", sort " << time_diff(optend, sortend) << ", requeue " << time_diff(sortend, requeueend) << ", pes " << time_diff(requeueend, pesend) << ", promote " << time_diff(pesend, end) << "\n";

}

void IntegrationAttempt::tryPromoteSingleValuedPB(Value* V) {

  PointerBase NewPB;
  if(!getPointerBaseLocal(V, NewPB))
    return;

  if(NewPB.Overdef)
    return;
  
  if(NewPB.Type == ValSetTypeScalar) {

    if(NewPB.Values.size() == 1) {
      
      if(getValueScope(V) == getLoopContext()) {
	// Feed the result to the ordinary constant folder, until the two get merged.
	setReplacement(V, NewPB.Values[0]);
	pointerBases.erase(V);
      }

    }

  }

}

void IntegrationAttempt::analyseLoopPBs(const Loop* L) {

  // L is an immediate child of this context.

  LoopPBAnalyser LPBA;

  // Step 1: queue VCs falling within this loop.

  struct timespec queuestart;
  clock_gettime(CLOCK_REALTIME, &queuestart);
  
  queueUpdatePBWholeLoop(L, &LPBA);

  struct timespec queueend;
  clock_gettime(CLOCK_REALTIME, &queueend);

  errs() << "Consider entire loop " << L->getHeader()->getName() << " in " << F.getName() << " (queue time: " << time_diff(queuestart, queueend) << ")\n";

  // Step 2: consider every result in optimistic mode until stable.
  // In this mode, undefineds are ok and clobbers are ignored on the supposition that
  // they might turn into known pointers.
  // Overdefs are still bad.
  // Step 3: consider every result in pessimistic mode until stable: clobbers are back in,
  // and undefined == overdefined.

  LPBA.run();

  errs() << "Loop consideration complete\n";

}

void IntegrationAttempt::resolvePointerBase(Value* V, PointerBase& PB) {

  PointerBase ExistingPB;
  if((!getPointerBaseLocal(V, ExistingPB)) || ExistingPB != PB) {
    pointerBases[V] = PB;
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
