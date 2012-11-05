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

  for(SmallVector<std::pair<ValCtx, Instruction*>, 4>::iterator it = Vals.begin(), it2 = Vals.end(); it != it2 && !NewPB.Overdef; ++it) {
    
    Value* V = it->first.first;
    IntegrationAttempt* VCtx = it->first.second;
    Instruction* VUser = it->second;
    PointerBase VPB;
    if(!VCtx->getValSetOrReplacement(V, VPB, VUser)) {
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
  
void IntegrationAttempt::addMemWriterEffect(Instruction* I, LoadInst* LI, IntegrationAttempt* Ctx) {

  memWriterEffects[I].insert(std::make_pair(LI, Ctx));

}

void IntegrationAttempt::removeMemWriterEffect(Instruction* I, LoadInst* LI, IntegrationAttempt* Ctx) {

  memWriterEffects[I].erase(std::make_pair(LI, Ctx));

}

void IntegrationAttempt::zapDefOrClobberCache(LoadInst* LI) {
  
  failedLFACache.erase(LI);

  DenseMap<LoadInst*, std::vector<ValCtx> >::iterator CacheIt = defOrClobberCache.find(LI);
  if(CacheIt == defOrClobberCache.end())
    return;

  std::vector<ValCtx>& CEntry = CacheIt->second;

  for(std::vector<ValCtx>::iterator it = CEntry.begin(), it2 = CEntry.end(); it != it2; ++it) {

    // Unregister our dependency on various instructions:
    if(!it->second)
      continue;

    if(StoreInst* SI = dyn_cast<StoreInst>(it->first)) {

      it->second->removeMemWriterEffect(SI, LI, this);

    }

  }

  defOrClobberCache.erase(LI);

}

void IntegrationAttempt::addCallBlockedPBLoad(CallInst* CI, LoadInst* LI, IntegrationAttempt* IA) {

  callBlockedPBLoads[CI].push_back(std::make_pair(LI, IA));

}

void IntegrationAttempt::addCFGDependentPBLoad(LoadInst* LI, IntegrationAttempt* IA) {

  CFGDependentPBLoads.insert(std::make_pair(LI, IA));

}

void IntegrationAttempt::dismissCallBlockedPBLoads(CallInst* CI) {

  DenseMap<CallInst*, std::vector<std::pair<LoadInst*, IntegrationAttempt*> > >::iterator it = 
    callBlockedPBLoads.find(CI);
  
  if(it == callBlockedPBLoads.end())
    return;

  std::vector<std::pair<LoadInst*, IntegrationAttempt*> >& Loads = it->second;

  for(std::vector<std::pair<LoadInst*, IntegrationAttempt*> >::iterator it = Loads.begin(), it2 = Loads.end(); it != it2; ++it) {

    it->second->zapDefOrClobberCache(it->first);

  }

  callBlockedPBLoads.erase(CI);

}

void IntegrationAttempt::localCFGChanged() {

  for(DenseSet<std::pair<LoadInst*, IntegrationAttempt*> >::iterator it = CFGDependentPBLoads.begin(), it2 = CFGDependentPBLoads.end(); it != it2; ++it) {

    it->second->zapDefOrClobberCache(it->first);

  }

  CFGDependentPBLoads.clear();

}

// Do load forwarding, possibly in optimistic mode: this means that
// stores that def but which have no associated PB are optimistically assumed
// to be compatible with anything, the same as the mergepoint logic above
// when finalise is false. When finalise = true this is just like normal load
// forwarding operating in PB mode.
bool IntegrationAttempt::tryForwardLoadPB(LoadInst* LI, bool finalise, PointerBase& NewPB) {

  LoadForwardAttempt Attempt(LI, this, LFMPB, TD);
  // In pessimistic mode, PB exploration stops early when it becomes hopeless.
  Attempt.PBOptimistic = !finalise;
  Attempt.CompletelyExplored = !finalise;
  Attempt.ReachedTop = false;

  pass->PBLFAs++;

  bool verbose = false;

  if(verbose) {

    errs() << "=== START LFA for " << itcache(*LI) << "\n";

    IntegrationAttempt* PrintCtx = this;
    while(PrintCtx) {
      errs() << PrintCtx->getShortHeader() << ", ";
      PrintCtx = PrintCtx->parent;
    }
    errs() << "\n";

  }

  DenseMap<LoadInst*, std::vector<ValCtx> >::iterator cacheIt = defOrClobberCache.find(LI);
  DenseMap<LoadInst*, std::string>::iterator failCacheIt = failedLFACache.find(LI);

  if(failCacheIt != failedLFACache.end()) {
    
    if(verbose)
      errs() << "CACHED FAIL\n";
    Attempt.reachedTop(failCacheIt->second);

    /*
    LoadForwardAttempt CheckAttempt(LI, this, LFMPB, TD);
    CheckAttempt.PBOptimistic = !finalise;
    CheckAttempt.CompletelyExplored = !finalise;
    CheckAttempt.ReachedTop = false;
    tryResolveLoad(CheckAttempt);

    assert(Attempt.PB == CheckAttempt.PB);
    */

  }
  else if(cacheIt == defOrClobberCache.end()) {

    if(verbose)
      errs() << "NO CACHE\n";

    assert((!finalise) && "Instruction considered for the first time in pessimistic phase?");

    tryResolveLoad(Attempt);

    if(Attempt.CompletelyExplored) {

      if(Attempt.ReachedTop) {
	
	if(verbose)
	  errs() << "Caching failure\n";
	failedLFACache[LI] = Attempt.ReachedTopStr;

      }
      else {

	std::vector<ValCtx>& CEntry = defOrClobberCache[LI];

	CEntry.insert(CEntry.end(), Attempt.DefOrClobberInstructions.begin(), Attempt.DefOrClobberInstructions.end());
	CEntry.insert(CEntry.end(), Attempt.IgnoredClobbers.begin(), Attempt.IgnoredClobbers.end());

	for(std::vector<ValCtx>::iterator it = CEntry.begin(), it2 = CEntry.end(); it != it2; ++it) {

	  // Register our dependency on various instructions:
	  if(!it->second)
	    continue;

	  if(StoreInst* SI = dyn_cast<StoreInst>(it->first)) {

	    it->second->addMemWriterEffect(SI, LI, this);

	  }
	  else if(CallInst* CI = dyn_cast<CallInst>(it->first)) {

	    if(!isa<MemIntrinsic>(CI)) {
	      Function* CF = getCalledFunction(CI);
	      if((!CF) || (!functionIsBlacklisted(CF)))
		it->second->addCallBlockedPBLoad(CI, LI, this);

	    }

	  }

	}

	for(SmallVector<IntegrationAttempt*, 8>::iterator it = Attempt.TraversedCtxs.begin(), it2 = Attempt.TraversedCtxs.end(); it != it2; ++it) {

	  (*it)->addCFGDependentPBLoad(LI, this);

	}

      }

    }
    else {
      
      if(verbose)
	errs() << "Not caching (incomplete exploration)\n";

      // Otherwise we were unable to explore to our natural limits (def instructions and blockers like
      // unexpanded calls, which will zap the dependency cache when they expand).
      // That might be due to failure to build a symexpr (indicating the load pointer is vague)
      // or running a query in pessimistic mode.
      // Do not cache the dependency set.

    }

  }
  else {

    if(verbose)
      errs() << "USING CACHE\n";

    pass->PBLFAsCached++;

    // Mimic load forwarding:
    Value* LPtr = LI->getOperand(0);
    uint64_t LSize = AA->getTypeStoreSize(LI->getType());
    SmallVector<NonLocalDepResult, 4> NLResults;

    LPDEBUG("LFA cache hit: " << itcache(*LI) << " references " << cacheIt->second.size() << " instructions\n");

    for(unsigned i = 0; i < cacheIt->second.size(); ++i) {

      ValCtx DefOrClobberVC = cacheIt->second[i];

      if(isa<Constant>(DefOrClobberVC.first)) {

	// Cached global initialiser
	PointerBase NewPB = PointerBase::get(DefOrClobberVC);
	Attempt.addPBDefn(NewPB);
	continue;
	
      }

      Instruction* Inst = cast<Instruction>(DefOrClobberVC.first);
      IntegrationAttempt* ICtx = DefOrClobberVC.second;

      MemDepResult NewMDR;

      if(isa<AllocaInst>(Inst) || (isa<CallInst>(Inst) && extractMallocCall(Inst))) {

	ValCtx LIUO = getUltimateUnderlyingObject(LI->getOperand(0));
	if(LIUO == make_vc(Inst, ICtx)) {
	  NewMDR = MemDepResult::getDef(Inst, ICtx);
	}
	else {
	  continue;
	}
	
      }
      else {

	if(AA->getModRefInfo(Inst, LI->getOperand(0), LSize, ICtx, this, /* usePBKnowledge = */ finalise) == AliasAnalysis::NoModRef)
	  continue;
      
	if(StoreInst* SI = dyn_cast<StoreInst>(Inst)) {

	  uint64_t SSize = AA->getTypeStoreSize(SI->getOperand(0)->getType());
	  switch(AA->aliasHypothetical(make_vc(SI->getPointerOperand(), ICtx), SSize, make_vc(LPtr, this), LSize, /* usePBKnowledge = */ finalise)) {
	  case AliasAnalysis::NoAlias:
	    continue;
	  case AliasAnalysis::MayAlias:
	    NewMDR = MemDepResult::getClobber(SI, ICtx);
	    break;
	  case AliasAnalysis::MustAlias:
	    NewMDR = MemDepResult::getDef(SI, ICtx);
	    break;
	  }

	}
	else {

	  NewMDR = MemDepResult::getClobber(Inst, ICtx);
	
	}

      }

      NLResults.push_back(NonLocalDepResult(0, NewMDR, 0)); // addPBResults doesn't reference either the BB or Address params

    }

    addPBResults(Attempt, NLResults, false);

    /*
    LoadForwardAttempt CheckAttempt(LI, this, LFMPB, TD);
    CheckAttempt.PBOptimistic = !finalise;
    CheckAttempt.CompletelyExplored = !finalise;
    CheckAttempt.ReachedTop = false;
    tryResolveLoad(CheckAttempt);
    
    assert(Attempt.PB == CheckAttempt.PB);
    */

  }

  if(verbose)
    errs() << "=== END LFA\n";

  if(!finalise)
    optimisticForwardStatus[LI] = describeLFA(Attempt);
  else
    pessimisticForwardStatus[LI] = describeLFA(Attempt);
    
  if(Attempt.PB.Values.size() == 0 && !Attempt.PB.Overdef)
    return false;

  NewPB = Attempt.PB;
  return true;

}

void IntegrationAttempt::addStartOfScopePB(LoadForwardAttempt& LFA) {

  // Hacked out of tryResolveClobber to provide simple initializer-aggregate support
  // until I get around to marrying the optimistic solver with full PartialLFA.

  if(LFA.canBuildSymExpr()) {

    ValCtx PointerVC = LFA.getBaseVC();
    if(GlobalVariable* GV = dyn_cast<GlobalVariable>(PointerVC.first)) {
	    
      if(GV->hasDefinitiveInitializer()) {
	
	Constant* GVC = GV->getInitializer();
	const Type* targetType = LFA.getOriginalInst()->getType();
	uint64_t GVCSize = (TD->getTypeSizeInBits(GVC->getType()) + 7) / 8;
	uint64_t ReadOffset = (uint64_t)LFA.getSymExprOffset();
	uint64_t LoadSize = (TD->getTypeSizeInBits(targetType) + 7) / 8;
	uint64_t FirstNotDef = std::min(GVCSize - ReadOffset, LoadSize);
	if(FirstNotDef == LoadSize) {

	  ValCtx FieldVC = extractAggregateMemberAt(GVC, ReadOffset, targetType, LoadSize, TD);
	  if(FieldVC != VCNull) {

	    assert(isa<Constant>(FieldVC.first));
	    LFA.DefOrClobberInstructions.push_back(FieldVC);
	    PointerBase NewPB = PointerBase::get(FieldVC);
	    LFA.addPBDefn(NewPB);
	    return;

	  }

	}

      }

    }

  }

  LFA.reachedTop("Reached main");

}

bool IntegrationAttempt::updateBasePointer(Value* V, bool finalise) {

  // Quick escape for values we can't handle:

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

    LPDEBUG("Updated dep to ");
    DEBUG(printPB(dbgs(), NewPB));
    DEBUG(dbgs() << "\n");
  
    queueUsersUpdatePB(V);

    return true;

  }
  
  return false;

}

void InlineAttempt::queueUpdateCall() {

  if(parent)
    pass->queueUpdatePB(parent, CI);

}

// This is different to HCF's investigateUsers code because it investigates different scopes.
// We investigate: (1) the user's 'natural' scope (since this catches exit PHIs), and
// (2) if the user is within our scope, all scopes between ours and its 
// (since our new invariant information might be useful at many scopes).
void IntegrationAttempt::queueUsersUpdatePB(Value* V) {

  const Loop* MyL = getLoopContext();
  
  for(Value::use_iterator UI = V->use_begin(), UE = V->use_end(); UI != UE; ++UI) {

    if(Instruction* UserI = dyn_cast<Instruction>(*UI)) {

      if(isa<ReturnInst>(UserI)) {
	
	getFunctionRoot()->queueUpdateCall();
	
      }

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

    if(blockIsDead(I->getParent()))
      return;

    if(getValueScope(I) == getLoopContext() && !isUnresolved(I)) {

      // No point investigating instructions whose concrete values are already known.
      return;

    }

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

      DenseMap<Instruction*, DenseSet<std::pair<LoadInst*, IntegrationAttempt*> > >::iterator it = 
	memWriterEffects.find(I);
      if(it != memWriterEffects.end()) {

	for(DenseSet<std::pair<LoadInst*, IntegrationAttempt*> >::iterator SI = it->second.begin(), SE = it->second.end(); SI != SE; ++SI)
	  pass->queueUpdatePB(SI->second, SI->first);

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
  bool investigateHere = true;

  if(TargetL != MyL) {

    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(getLoopContext(), TargetL))) {
      if(PA->Iterations.back()->iterStatus == IterationStatusFinal)
	investigateHere = false;
      PA->queueUsersUpdatePBRising(I, TargetL, V);
    }

  }

  if(investigateHere)
    queueUsersUpdatePBFalling(I, MyL, V);

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

      if(getValueScope(V) == getLoopContext()) {
	// Feed the result to the ordinary constant folder, until the two get merged.
	setReplacement(V, PB.Values[0]);
	investigateUsers(V);
      }

    }
  }
  else {
    // Set of pointer bases. Retry any load that might benefit (i.e. those at the affected scope
    // and its children).
    if(Instruction* I = dyn_cast<Instruction>(V)) {
      if(shouldQueueOnInst(I, this))
	queueWorkBlockedOn(I);
    }
  }

}

void IntegrationAttempt::queuePBUpdateIfUnresolved(Value *V) {

  if(!isUnresolved(V))
    return;

  const Loop* MyL = getLoopContext();
  const Loop* VL = getValueScope(V);
				     
  if(MyL != VL) {

    // Check if there's a terminated loop above us which would cause this query
    // to malfunction (we'd jump into the last iteration without transiting
    // an exit edge; to fix?)

    // Extend this to all values: if there's a terminated loop we can just identify its value
    // per iteration as usual.

    if(MyL && !MyL->contains(VL))
      return;

    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(MyL, VL))) {

      if(PA->Iterations.back()->iterStatus == IterationStatusFinal)
	return;

    }

  }

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

void IntegrationAttempt::clearSuboptimalPBResults(DenseMap<ValCtx, PointerBase>& OldPBs) {

  std::vector<Value*> toErase;
  
  for(DenseMap<Value*, PointerBase>::iterator it = pointerBases.begin(), it2 = pointerBases.end(); it != it2; ++it) {

    OldPBs.insert(std::make_pair(make_vc(it->first, this), it->second));

    if(it->second.Overdef || it->second.Values.size() > 1)
      toErase.push_back(it->first);

  }

  for(unsigned i = 0; i < toErase.size(); ++i)
    pointerBases.erase(toErase[i]);

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->clearSuboptimalPBResults(OldPBs);

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->clearSuboptimalPBResults(OldPBs);

  }

}

static bool isBetterThanOrEqual(PointerBase& NewPB, PointerBase& OldPB) {

  if(OldPB.Overdef)
    return true;

  if(NewPB.Overdef)
    return false;

  return NewPB.Values.size() <= OldPB.Values.size();

}

void IntegrationAttempt::queueNewPBWork(DenseMap<ValCtx, PointerBase>& OldPBs, uint64_t& newVCs, uint64_t& changedVCs) {

  for(DenseMap<Value*, PointerBase>::iterator it = pointerBases.begin(), it2 = pointerBases.end(); it != it2; ++it) {

    DenseMap<ValCtx, PointerBase>::iterator OldPB = OldPBs.find(make_vc(it->first, this));

    if(OldPB != OldPBs.end()) {
      assert(isBetterThanOrEqual(it->second, OldPB->second));
    }

    if(it->second.Overdef)
      continue;

    bool queue = false;
    if(OldPB == OldPBs.end()) {
      newVCs++;
      queue = true;
    }
    else if(OldPB->second != it->second) {
      /*
      errs() << "Changed " << itcache(OldPB->first) << " to ";
      printPB(errs(), it->second);
      errs() << "\n";
      */
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

void IntegrationHeuristicsPass::runPointerBaseSolver(bool finalise, std::vector<ValCtx>* modifiedVCs) {

  DenseMap<ValCtx, int> considerCount;

  SmallVector<ValCtx, 64>* ConsumeQ = (PBProduceQ == &PBQueue1) ? &PBQueue2 : &PBQueue1;

  int i = 0;
  
  while(PBQueue1.size() || PBQueue2.size()) {

    std::sort(ConsumeQ->begin(), ConsumeQ->end());
    SmallVector<ValCtx, 64>::iterator endit = std::unique(ConsumeQ->begin(), ConsumeQ->end());
    
    for(SmallVector<ValCtx, 64>::iterator it = ConsumeQ->begin(); it != endit; ++it) {

      
      //considerCount[*it]++;
      if(++i == 10000) {
	errs() << ".";
	//	errs() << "----\n";
	//	it->second->printConsiderCount(considerCount, 100);
	//	errs() << "----\n";
	i = 0;
      }

      if(it->second->updateBasePointer(it->first, finalise)) {
	if(modifiedVCs) {
	  modifiedVCs->push_back(*it);
	}
      }

    }

    ConsumeQ->clear();
    std::swap(ConsumeQ, PBProduceQ);

  }

}

bool IntegrationHeuristicsPass::runPointerBaseSolver() {

  DenseMap<ValCtx, PointerBase> OldPBs;
  
  uint64_t totalVCs = 0, newVCs = 0, changedVCs = 0;

  PBLFAs = 0;
  PBLFAsCached = 0;

  errs() << "Start optimistic solver";

  // Step 1: discard all existing PB results that could be improved.
  RootIA->clearSuboptimalPBResults(OldPBs);

  // Step 2: consider every result in optimistic mode until stable.
  // In this mode, undefineds are ok and clobbers are ignored on the supposition that
  // they might turn into known pointers.
  // Overdefs are still bad.

  RootIA->queuePBUpdateAllUnresolvedVCs();
  totalVCs = PBProduceQ->size();

  std::vector<ValCtx> updatedVCs;

  runPointerBaseSolver(false, &updatedVCs);

  // Queue up anything of which we've asserted a non-overdef PB for reconsideration.
  //RootIA->queuePBUpdateAllResolvedVCs();

  std::sort(updatedVCs.begin(), updatedVCs.end());
  std::vector<ValCtx>::iterator it, endit;
  endit = std::unique(updatedVCs.begin(), updatedVCs.end());
  for(it = updatedVCs.begin(); it != endit; ++it) {

    queueUpdatePB(it->second, it->first);

  }

  // Step 3: consider every result in pessimistic mode until stable: clobbers are back in,
  // and undefined == overdefined.

  runPointerBaseSolver(true, 0);

  RootIA->queueNewPBWork(OldPBs, newVCs, changedVCs);

  errs() << "\nRan optimistic solver: considered " << totalVCs << ", found " << newVCs << " new and " << changedVCs << " changed (LFAs cached " << PBLFAsCached << "/" << PBLFAs << ")\n";

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
