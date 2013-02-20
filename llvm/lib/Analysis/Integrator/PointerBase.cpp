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

PointerBase PointerBase::get(ShadowValue SV) {

  Constant* CEGlobal
  const PointerType* PTy = dyn_cast<PointerType>(SV.getType());
  bool isFunctionTy = PTy && PTy->getElementType()->isFunctionTy();

  // Treat function pointers like scalars, since they're not indexable objects.

  if(val_is<Constant>(SV) && extractCEBase(val_cast<Constant>(SV), CEGlobal))
    return get(ShadowValue(CEGlobal), ValSetTypePB);
  else if(val_is<Constant>(SV) && (isFunctionTy || !PTy))
    return get(SV, ValSetTypeScalar);
  else
    return get(SV, ValSetTypePB);
  
}

bool llvm::extractCEBase(Constant* C, Constant*& Base) {

  if(isa<GlobalValue>(C)) {
    Base = C;
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
    return extractCEBase(CE->getOperand(0), Base);
  case Instruction::Add:
  case Instruction::Sub:
    {
      Constant *Base1, *Base2;
      bool C1Valid, C2Valid;
      C1Valid = extractCEBase(CE->getOperand(0), C1);
      C2Valid = extractCEBase(CE->getOperand(1), C2);
      if(CE->getOpcode() == Instruction::Add) {

	if(C1Valid == C2Valid)
	  return false;
	Base = C1Valid ? C1 : C2;
	return true;

      }
      else {

	if((!C1Valid) || C2Valid)
	  return false;
	C = C1;
	return true;

      }
      
    }

 default:
   return false;

  }

}

bool IntegrationAttempt::hasResolvedPB(ShadowValue V) {

  // A little different to isUnresolved: that would call GEP of X where X has a known replacement resolved. We explicitly eval that GEP.
  // This method will become the one true method once the two folders merge.

  if(ShadowInstruction* SI = V.getInst()) {

    if(inst_is<AllocaInst>(SI) || isNoAliasCall(SI->invar->I))
      return true;  
    
    if(!SI->i.replaceWith.isInval())
      return true;

  }
  else if(ShadowArg* SA = V.getArg()) {

    if(!SA->i.replaceWith.isInval())
      return true;
    
  }

  return false;

}

bool llvm::getPointerBase(ShadowValue V, PointerBase& OutPB) {

  if(ShadowInstruction* SI = V.getInst()) {

    if(inst_is<AllocaInst>(SI) || isNoAliasCall(SI->invar->I)) {

      OutPB = PointerBase::get(V);
      return true;
      
    }
    else {

      OutPB = SI->i.PB;
      return OutPB.isInitialised();

    }

  }
  else if(ShadowArg* SA = V.getArg()) {

    OutPB = SA->i.PB;
    return OutPB.isInitialised();

  }
  else {
    
    Value* Val = V.getVal();
    if(isa<GlobalValue>(Val)) {
      
      OutPB = PointerBase::get(V);    
      return true;

    }
    else if(isa<ConstantExpr>(Val)) {

      OutPB = PointerBase::get(V);
      return true;

    }

  }

}

// If finalise is false, we're in the 'incremental upgrade' phase: PHIs and selects take on
// the newest result of their operands.
// If finalise is true, we're in the 'resolution' phase: they take on their true value.
// e.g. in phase 1, PHI(def, undef) = def, in phase 2 it is overdef.
bool IntegrationAttempt::getMergeBasePointer(ShadowInstruction* I, bool finalise, PointerBase& NewPB) {

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
    if(!VCtx->getValSetOrReplacement(*it, VPB)) {
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

bool InlineAttempt::getArgBasePointer(Argument* A, PointerBase& OutPB) {

  if(!parent)
    return false;
  ShadowValue Arg = CI->getCallArgOperand(SA->invar->A->getArgNo());
  return getPointerBase(Arg, OutPB);

}

bool InlineAttempt::updateHeaderPHIPB(ShadowInstruction* PN, bool& NewPBValid, PointerBase& NewPB) {
  
  return false;

}

bool PeelIteration::updateHeaderPHIPB(ShadowInstruction* I, bool& NewPBValid, PointerBase& NewPB) {

  PHINode* PN = cast_inst<PHINode>(I);
  
  if(L && L->getHeader() == PN->getParent()) {

    ShadowValue predValue = getLoopHeaderForwardedOperand(I);

    NewPBValid = getPointerBase(predValue, NewPB);

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
    for(SmallVector<ShadowValue, 4>::iterator it = PB.Values.begin(), it2 = PB.Values.end(); it != it2; ++it) {

      if(it != PB.Values.begin())
	out << ", ";
      out << itcache(*it, brief);

    }
    out << " }";
  }

}

bool IntegrationAttempt::updateUnaryValSet(ShadowInstruction* I, PointerBase &PB) {

  PointerBase ArgPB;

  if(!getValSetOrReplacement(I->getOperand(0), ArgPB))
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

      Constant* Expr = ConstantExpr::getCast(I->invar->I->getOpcode(), cast_val<Constant>(ArgPB.Values[i]), I->getType());
      if(ConstantExpr* CE = dyn_cast<ConstantExpr>(Expr))
	Expr = ConstantFoldConstantExpression(CE, TD);

      if((!Expr) || isa<ConstantExpr>(Expr))
	NewPB = PointerBase::getOverdef();
      else
	NewPB = PointerBase::get(ShadowValue(Expr));
    
      PB.merge(NewPB);

    }

    return true;

  }
  else {

    PB = ArgPB;
    return true;

  }

}

bool IntegrationAttempt::getValSetOrReplacement(ShadowValue V, PointerBase& PB) {

  if(getPointerBase(V, PB))
    return true;
  else if(V.baseObject)
    PB = PointerBase::get(V.baseObject);
  else if(V.replaceWith)
    PB = PointerBase::get(V.replaceWith);

  return PB.isInitialised();

}

bool IntegrationAttempt::updateBinopValSet(ShadowInstruction* I, PointerBase& PB) {

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

    // Need this to establish value recurrences, e.g. a loop with store-to-load (or phi-to-phi) feeds which circulates a known value or value set.

    for(unsigned i = 0; i < Op1PB.Values.size() && !PB.Overdef; ++i) {
      for(unsigned j = 0; j < Op2PB.Values.size() && !PB.Overdef; ++j) {
    
	Constant* Expr = ConstantExpr::get(I->getOpcode(), cast_val<Constant>(Op1PB.Values[i]), cast_val<Constant>(Op2PB.Values[j]));
	if(ConstantExpr* CE = dyn_cast<ConstantExpr>(Expr))
	  Expr = ConstantFoldConstantExpression(CE, TD);

	PointerBase ThisPB;

	if(Expr)
	  ThisPB = PointerBase::get(ShadowValue(Expr));
	else
	  ThisPB = PointerBase::getOverdef();

	PB.merge(ThisPB);

      }
    }

    return true;

  }

}

bool IntegrationAttempt::updateBasePointer(ShadowValue V, bool finalise, LoopPBAnalyser* LPBA, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA) {

  // Quick escape for values we can't handle:

  bool verbose = false;

  if(ShadowInstruction* I = V.getInst()) {
    
    switch(I->invar->I->getOpcode()) {

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
  if(hasResolvedPB(V))
    return false;

  if(verbose)
    errs() << "Update pointer base " << itcache(V) << "\n";
  PointerBase NewPB;

  PointerBase OldPB;
  bool OldPBValid = getPointerBase(V, OldPB);

  // Getting no worse:
  if(finalise && LPBA && ((!OldPBValid) || OldPB.Overdef))
    return false;

  if(val_is<LoadInst>(V)) {

    bool ret = tryForwardLoadPB(V.getInst(), finalise, NewPB, CacheThresholdBB, CacheThresholdIA);
    if(!ret)
      return false;

  }
  else if(ShadowArgument* SA = V.getArg()) {

    InlineAttempt* IA = getFunctionRoot();
    if(!IA->getArgBasePointer(SA->invar->A, NewPB)) {

      // No information from our argument
      return false;

    }

  }
  else {

    ShadowInstruction* I = V.getInst();

    switch(I->invar->I->getOpcode()) {

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
	if(updateHeaderPHIPB(I, NewPBValid, NewPB)) {
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
  
  return false;

}

void InlineAttempt::queueUpdateCall(LoopPBAnalyser* LPBA) {

  if(parent)
    queueUpdatePB(ShadowValue(CI), LPBA);

}

// We investigate: (1) the user's 'natural' scope (since this catches exit PHIs), and
// (2) if the user is within our scope, all scopes between ours and its 
// (since our new invariant information might be useful at many scopes).
void IntegrationAttempt::queueUsersUpdatePB(ShadowValue V, LoopPBAnalyser* LPBA) {

  ImmutableArray<ShadowInstIdx>* Users;
  if(ShadowInstruction* SI = V.getInst()) {
    Users = &(SI->invar->userIdxs);
  }
  else {
    ShadowArgument* SA = V.getArg();
    Users = &(SI->invar->userIdxs);
  }

  for(uint32_t i = 0; i < Users->size(); ++i) {

    ShadowInstIdx& SII = (*Users)[i];
    if(SII.blockIdx != INVALID_BLOCK_IDX && SII.instIdx != INVALID_INST_IDX) {

      ShadowInstructionInvar* UserI = getInstInvar(SII.blockIdx, SII.instIdx);
      queueUserUpdatePB(UserI, LPBA);

    }

  }

}

 void IntegrationAttempt::queueUserUpdatePB(ShadowInstructionInvar* UserI, LoopPBAnalyser* LPBA) {

  const Loop* MyL = L;
  
  if(inst_is<ReturnInst>(UserI)) {
	
    getFunctionRoot()->queueUpdateCall(LPBA);
	
  }

  const Loop* UserL = UserI->scope;

  if((!L) || (UserL && L->contains(UserL))) {
	  
    queueUsersUpdatePBRising(UserI, LPBA);
	
  }
  else {
	
    queueUsersUpdatePBFalling(UserI, LPBA);

  }
  
}

void IntegrationAttempt::queueUpdatePB(ShadowValue V, LoopPBAnalyser* LPBA) {
  
  LPBA->queueIfConsidered(V);

}

void IntegrationAttempt::queueUsersUpdatePBFalling(ShadowInstructionInvar* I, LoopPBAnalyser* LPBA) {

  if(I->scope == L) {

    ShadowInst* SI = getInst(I);
    if(!SI)
      return;

    if((!inst_is<CallInst>(SI)) && hasResolvedPB(SI)) {

      // No point investigating instructions whose concrete values are already known.
      return;

    }

    if(CallInst* CI = dyn_cast_inst<CallInst>(SI)) {

      if(InlineAttempt* IA = getInlineAttempt(CI)) {

	unsigned i = 0;
	Function* F = IA->getFunction();
	for(uint32_t i = 0; i < F->arg_size(); ++i) {
	  
	  if(I->I == CI->getArgOperand(i))
	    queueUpdatePB(IA->argShadows[i], LPBA);

	}

      }

    }
    else if(inst_is<StoreInst>(SI)) {

      for(SmallVector<ShadowInstruction*, 1>::iterator it = SI->i.PBIndirectUsers.begin(), it2 = SI->i.PBIndirectUsers.end(); it != it2; ++it) {

	queueUpdatePB(*it, LPBA);

      }

    }
    else {

      queueUpdatePB(SI, LPBA);

    }

  }
  else {
    if(parent)
      parent->queueUsersUpdatePBFalling(I, LPBA);
  }

}

void PeelAttempt::queueUsersUpdatePBRising(ShadowInstructionInvar* I, LoopPBAnalyser* LPBA) {

  for(unsigned i = 0; i < Iterations.size(); ++i)
    Iterations[i]->queueUsersUpdatePBRising(I, LPBA);

}

void IntegrationAttempt::queueUsersUpdatePBRising(ShadowInstructionInvar* I, LoopPBAnalyser* LPBA) {

  const Loop* MyL = L;
  const Loop* NextL = I->scope == MyL ? I->scope : immediateChildLoop(MyL, I->scope);
  bool investigateHere = true;

  if(TargetLI->scope != MyL) {

    if(PeelAttempt* PA = getPeelAttempt(NextL)) {
      if(PA->Iterations.back()->iterStatus == IterationStatusFinal)
	investigateHere = false;
      PA->queueUsersUpdatePBRising(I, LPBA);
    }

  }

  if(investigateHere)
    queueUsersUpdatePBFalling(I, LPBA);

}

bool IntegrationAttempt::shouldCheckPB(ShadowValue V) {

  bool verbose = false;

  if(verbose)
    errs() << "shouldCheckPB " << itcache(V) << "\n";

  if(contextIsDead) {
    if(verbose)
      errs() << "Ctx dead\n";
    return false;
  }

  if(hasResolvedPB(V)) {
    if(verbose)
      errs() << "Resolved already: repl " << itcache(getReplacement(V)) << "\n";
    return false;
  }

  const Loop* MyL = getLoopContext();
  const Loop* VL = V.getScope();
				     
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
  bool PBValid = getPointerBase(V, PB);
  if(PBValid && PB.Values.size() == 1) {
    if(verbose)
      errs() << "Has optimal PB\n";
    return false;
  }

  if(verbose)
    errs() << "Will check\n";
  return true;

}

void IntegrationAttempt::queuePBUpdateIfUnresolved(ShadowValue V, LoopPBAnalyser* LPBA) {

  if(shouldCheckPB(V)) {
    
    LPBA->addVal(V);
    //errs() << "Queue " << itcache(make_vc(V, this)) << "\n";
    if(ShadowInstruction* SI = V.getInst()) {
      SI->i.PB = PointerBase();
    }
    else {
      ShadowArg* SA = V.getArg();
      SA->i.PB = PointerBase();
    }

  }
  else {

    LPDEBUG("Shouldn't check " << itcache(V) << "\n");

  }

}

void InlineAttempt::queueCheckAllArgs(LoopPBAnalyser* LPBA) {

  for(uint32_t i = 0; i < F.arg_size(); ++i)
    queuePBUpdateIfUnresolved(ShadowValue(argShadows[i]));

}

void IntegrationAttempt::queuePBUpdateAllUnresolvedVCsInScope(const Loop* CheckL, LoopPBAnalyser* LPBA) {

  if((!L) && !CheckL) {

    queueCheckAllArgs();

  }

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    const Loop* BBL = BB->invar->naturalScope;

    if((!CheckL) || (BBL && CheckL->contains(BBL))) {

      for(uint32_t j = 0; j < BB->insts.size(); ++j)
	queuePBUpdateIfUnresolved(ShadowValue(BB->insts[j]), LPBA);

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

void LoopPBAnalyser::runPointerBaseSolver(bool finalise, std::vector<ShadowValue>* modifiedVals) {

  //DenseMap<ShadowValue, int> considerCount;

  SmallVector<ShadowValue, 64>* ConsumeQ = (PBProduceQ == &PBQueue1) ? &PBQueue2 : &PBQueue1;

  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ShadowValue, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());

    for(SmallVector<ShadowValue, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      assert(inLoopVCs.count(*it));

      if(it->second->updateBasePointer(*it, finalise, this, CacheThresholdBB, CacheThresholdIA)) {
	if(modifiedVCs) {
	  modifiedVCs->push_back(*it);
	}
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

  std::vector<ShadowValue> updatedVals;
  runPointerBaseSolver(false, &updatedVals);

  std::sort(updatedVals.begin(), updatedVals.end());
  std::vector<ShadowValue>::iterator startit, endit;
  endit = std::unique(updatedVals.begin(), updatedVals.end());

  for(startit = updatedVals.begin(); startit != endit; ++startit) {
	
    queueUpdatePB(*startit);

  }

  runPointerBaseSolver(true, 0);

  for(startit = updatedVals.begin(); startit != endit; ++startit) {

    startit->second->tryPromoteSingleValuedPB(*startit);
    
  }

}

void IntegrationAttempt::tryPromoteSingleValuedPB(ShadowValue V) {

  PointerBase NewPB;
  if(!getPointerBase(V, NewPB))
    return;

  if(NewPB.Overdef)
    return;
  
  if(NewPB.Type == ValSetTypeScalar) {

    if(NewPB.Values.size() == 1) {
      
      if(V.getScope() == L) {
	// Feed the result to the ordinary constant folder, until the two get merged.
	if(ShadowInstruction* SI = V.getInst()) {
	  SI->i.replaceWith = NewPB.Values[0];
	  SI->i.PB = PointerBase();
	}
	else {
	  ShadowArg* SA = V.getArg();
	  SA->i.replaceWith = NewPB.Values[0];
	  SA->i.PB = PointerBase();
	}
      }

    }

  }

}

void IntegrationAttempt::analyseLoopPBs(const Loop* L, BasicBlock* CacheThresholdBB, IntegrationAttempt* CacheThresholdIA) {

  // L is an immediate child of this context.

  LoopPBAnalyser LPBA(CacheThresholdBB, CacheThresholdIA);

  // Step 1: queue VCs falling within this loop.

  queueUpdatePBWholeLoop(L, &LPBA);

  // Step 2: consider every result in optimistic mode until stable.
  // In this mode, undefineds are ok and clobbers are ignored on the supposition that
  // they might turn into known pointers.
  // Overdefs are still bad.
  // Step 3: consider every result in pessimistic mode until stable: clobbers are back in,
  // and undefined == overdefined.

  LPBA.run();

}

bool InlineAttempt::ctxContains(IntegrationAttempt* IA) {

  return this == IA;

}

bool PeelIteration::ctxContains(IntegrationAttempt* IA) {

  if(this == IA)
    return true;
  return parent->ctxContains(IA);

}

bool llvm::basesAlias(ShadowValue V1, ShadowValue V2) {

  if(VC1.first == VC2.first) {

    if((!VC1.second) || (!VC2.second))
      return true;

    if(VC1.second->ctxContains(VC2.second) || VC2.second->ctxContains(VC1.second))
      return true;

  }

  return false;

}
