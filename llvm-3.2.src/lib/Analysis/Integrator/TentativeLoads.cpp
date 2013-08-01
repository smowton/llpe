// A mini-analysis that spots tentative loads and memcpy instructions.
// These are loads whose incoming dataflow (a) crosses a /yield point/, a point where we must assume
// that another thread got a chance to run and messed with our state, (b) is not dominated
// by other loads or stores that will check the incoming state / overwrite it with known state,
// and (c) is not known to be thread-local regardless.

// The main phase has already taken care of part (c) for us by setting ShadowInstruction::u.load.isThreadLocal
// when the load was known to be from a thread-private object. We will set the same flag wherever
// it's clear that checking this load would be redundant.

// The order in which loads are visited is unimportant.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Function.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"

using namespace llvm;

class TentativeLoadWalker : public BackwardIAWalker {

public:

  struct Ctx {

    bool* goodBytes;
    void* ignoreUntil;

    Ctx(uint64_t size) : ignoreUntil(0) {

      goodBytes = new bool[size];
      memset(goodBytes, 0, sizeof(bool) * size);

    }

    Ctx(Ctx* other, uint64_t size) : ignoreUntil(other->ignoreUntil) {

      goodBytes = new bool[size];
      memcpy(goodBytes, other->goodBytes, sizeof(bool) * size);

    }

    ~Ctx() {
      
      delete[] goodBytes;

    }

    void fill(uint64_t from, uint64_t limit) {

      for(uint64_t i = from; i != limit; ++i)
	goodBytes[i] = true;
      
    }

  };

protected:

  virtual bool shouldEnterCall(ShadowInstruction*, void*) { return true; }

  // The blocked-by-unexpanded case is taken care of in walkInstruction.
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*) { return false; }

  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void* Context);
  virtual WalkInstructionResult mayAscendFromContext(IntegrationAttempt*, void* Ctx);

  WalkInstructionResult markGoodBytes(ShadowValue GoodPtr, uint64_t Len, void* vctx, uint64_t Offset = 0);
  WalkInstructionResult walkCopyInst(ShadowValue CopyFrom, ShadowValue CopyTo, ShadowValue LenSV, void*);

  virtual void enterCall(InlineAttempt* IA, void* Ctx);
  virtual void leaveCall(InlineAttempt* IA, void* Ctx);
  virtual void enterLoop(PeelAttempt*, void* Ctx);
  virtual void leaveLoop(PeelAttempt*, void* Ctx);

  WalkInstructionResult walkPathCondition(PathConditionTypes Ty, PathCondition& Cond, ShadowBB* BB, void* vctx);
  WalkInstructionResult walkPathConditions(PathConditionTypes Ty, std::vector<PathCondition>& Conds, ShadowBB* BB, uint32_t stackDepth, void* vctx);
  virtual WalkInstructionResult walkFromBlock(ShadowBB* BB, void* vctx);

  virtual void* copyContext(void* x) {

    return new Ctx((Ctx*)x, readSize);

  }

  virtual void freeContext(void* x) {

    delete ((Ctx*)x);

  }

  ImprovedVal readPtr;
  uint64_t readSize;

public:

  TentativeLoadWalker(ShadowInstruction& Start, ImprovedVal Ptr, uint64_t Size, void* initialCtx) : 
    BackwardIAWalker(Start.invar->idx, Start.parent, /* skipFirst = */ true, 
		     initialCtx, 0, /* doIgnoreEdges = */ true),
    readPtr(Ptr), 
    readSize(Size),
    shouldCheckLoad(TLS_NOCHECK) {}

  ThreadLocalState shouldCheckLoad;

};

void TentativeLoadWalker::enterCall(InlineAttempt* IA, void* vctx) {

  Ctx* ctx = (Ctx*)vctx;
  if((!ctx->ignoreUntil) && !IA->isEnabled())
    ctx->ignoreUntil = IA;

}

void TentativeLoadWalker::leaveCall(InlineAttempt* IA, void* vctx) {

  Ctx* ctx = (Ctx*)vctx;
  if(ctx->ignoreUntil == IA)
    ctx->ignoreUntil = 0;
  
}

void TentativeLoadWalker::enterLoop(PeelAttempt* LPA, void* vctx) {

  Ctx* ctx = (Ctx*)vctx;
  if((!ctx->ignoreUntil) && !LPA->isEnabled())
    ctx->ignoreUntil = LPA;
  
  
}

void TentativeLoadWalker::leaveLoop(PeelAttempt* LPA, void* vctx) {

  Ctx* ctx = (Ctx*)vctx;
  if(ctx->ignoreUntil == LPA)
    ctx->ignoreUntil = 0;

}

// Prevent walking up from the allocation context, since the edges followed must route around the allocation.
WalkInstructionResult TentativeLoadWalker::mayAscendFromContext(IntegrationAttempt* IA, void* Ctx) {

  ShadowInstruction* readInst = readPtr.V.getInst();
  if(readInst && readInst->parent->IA == IA)
    return WIRStopThisPath;

  return WIRContinue;

}

WalkInstructionResult TentativeLoadWalker::markGoodBytes(ShadowValue GoodPtr, uint64_t Len, void* vctx, uint64_t Offset) {

  // ignoreUntil indicates we're within a disabled context. The loads and stores here will
  // be committed unmodified, in particular without checks that their results are as expected,
  // and so they do not make any subsequent check redundant.
  // Stores in disabled contexts can't count either, because of the situation:
  // disabled {
  //   call void thread_yield();
  //   %0 = load %x;
  //   store %0, %y;
  // }
  // %1 = load %y
  
  // Here the load %y must be checked, because the load %x cannot be checked.   

  Ctx* ctx = (Ctx*)vctx;

  if(ctx->ignoreUntil)
    return WIRContinue;

  std::pair<ValSetType, ImprovedVal> PtrTarget;
  if(!tryGetUniqueIV(GoodPtr, PtrTarget))
    return WIRContinue;

  if(PtrTarget.first != ValSetTypePB)
    return WIRContinue;

  uint64_t FirstDef, FirstNotDef, Ignored;
  if(!GetDefinedRange(readPtr.V, readPtr.Offset, readSize, 
		      PtrTarget.second.V, PtrTarget.second.Offset + Offset, Len,
		      FirstDef, FirstNotDef, Ignored))
    return WIRContinue;

  bool allGood = true;

  for(uint64_t i = 0, ilim = readSize; i != ilim && (allGood || i < FirstNotDef); ++i) {

    if(i >= FirstDef && i < FirstNotDef)
      ctx->goodBytes[i] = true;
    else if(!ctx->goodBytes[i])
      allGood = false;

  }

  return allGood ? WIRStopThisPath : WIRContinue;

}

WalkInstructionResult TentativeLoadWalker::walkPathCondition(PathConditionTypes Ty, PathCondition& Cond, ShadowBB* BB, void* vctx) {

  ShadowValue CondSV = BB->IA->getFunctionRoot()->getPathConditionSV(Cond);
  uint64_t Len = 0;
  switch(Ty) {
  case PathConditionTypeIntmem:
    Len = GlobalAA->getTypeStoreSize(Cond.val->getType());
    break;
  case PathConditionTypeString:
    Len = cast<ConstantDataArray>(Cond.val)->getNumElements();
    break;
  case PathConditionTypeInt:
    release_assert(0 && "Bad path condition type");
    llvm_unreachable();
  }

  return markGoodBytes(CondSV, Len, vctx, Cond.offset);

}

WalkInstructionResult TentativeLoadWalker::walkPathConditions(PathConditionTypes Ty, std::vector<PathCondition>& Conds, ShadowBB* BB, uint32_t stackDepth, void* vctx) {

  for(std::vector<PathCondition>::iterator it = Conds.begin(), itend = Conds.end(); it != itend; ++it) {

    if(stackDepth != it->fromStackIdx || BB->invar->BB != it->fromBB)
      continue;

    WalkInstructionResult WIR = walkPathCondition(Ty, *it, BB, vctx);
    if(WIR != WIRContinue)
      return WIR;

  }

  return WIRContinue;

}

WalkInstructionResult TentativeLoadWalker::walkFromBlock(ShadowBB* BB, void* vctx) {

  InlineAttempt* IA = BB->IA->getFunctionRoot();
  if(IA->targetCallInfo) {

    WalkInstructionResult WIR = 
      walkPathConditions(PathConditionTypeIntmem, BB->IA->pass->rootIntmemPathConditions, 
			 BB, IA->targetCallInfo->targetStackDepth, vctx);

    if(WIR != WIRContinue)
      return WIR;

    return walkPathConditions(PathConditionTypeString, BB->IA->pass->rootStringPathConditions, 
			      BB, IA->targetCallInfo->targetStackDepth, vctx);

  }
  else {

    return WIRContinue;

  }

}

WalkInstructionResult TentativeLoadWalker::walkCopyInst(ShadowValue CopyFrom, ShadowValue CopyTo, ShadowValue LenSV, void* vctx) {

  ConstantInt* LenC = cast_or_null<ConstantInt>(getConstReplacement(LenSV));
  if(!LenC)
    return WIRContinue;
  uint64_t Len = LenC->getLimitedValue(); 

  WalkInstructionResult WIR = markGoodBytes(CopyTo, Len, vctx);
  if(WIR == WIRStopThisPath)
    return WIR;

  return markGoodBytes(CopyFrom, Len, vctx);

}

WalkInstructionResult TentativeLoadWalker::walkInstruction(ShadowInstruction* SI, void* vctx) {

  // Reached allocation site, which defines all bytes? (and if realloc, checks the copy):
  if(SI == readPtr.V.getInst())
    return WIRStopThisPath;

  if(LoadInst* LI = dyn_cast_inst<LoadInst>(SI)) {

    if(LI->isVolatile()) {
      shouldCheckLoad = TLS_MUSTCHECK;
      return WIRStopWholeWalk;
    }
      
    return markGoodBytes(LI->getOperand(0), GlobalAA->getTypeStoreSize(LI->getType()), vctx);

  }
  else if(StoreInst* StoreI = dyn_cast_inst<StoreInst>(SI)) {
    
    if(StoreI->isVolatile()) {
      shouldCheckLoad = TLS_MUSTCHECK;
      return WIRStopWholeWalk;
    }

    return markGoodBytes(SI->getOperand(1), GlobalAA->getTypeStoreSize(StoreI->getValueOperand()->getType()), vctx);

  }
  else if(inst_is<CallInst>(SI)) {

    if(inst_is<MemSetInst>(SI)) {

      ConstantInt* LengthCI = cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(2)));
      if(!LengthCI)
	return WIRContinue;
      uint64_t MemSize = LengthCI->getLimitedValue();

      return markGoodBytes(SI->getCallArgOperand(0), MemSize, vctx);

    }
    else if(inst_is<MemTransferInst>(SI)) {

      return walkCopyInst(SI->getCallArgOperand(0), SI->getCallArgOperand(1), SI->getCallArgOperand(2), vctx);

    }
    else {

      // Don't check realloc here -- the is-allocation-site check at the top takes care of it.
      
      Function* F = getCalledFunction(SI);
      if(ReadFile* RF = SI->parent->IA->tryGetReadFile(cast_inst<CallInst>(SI))) {

	return markGoodBytes(SI->getCallArgOperand(1), RF->readSize, vctx);

      }
      else if((!F) || GlobalIHP->yieldFunctions.count(F)) {

	shouldCheckLoad = TLS_MUSTCHECK;
	return WIRStopWholeWalk;

      }      

    }

  }

  return WIRContinue;

}

ThreadLocalState IntegrationAttempt::shouldCheckRead(ShadowInstruction& Start, ImprovedVal& Ptr, uint64_t Size, void* initCtx) {
  
  TentativeLoadWalker W(Start, Ptr, Size, initCtx);
  W.walk();
  return W.shouldCheckLoad;
    
}

static void fillCtx(TentativeLoadWalker::Ctx* initCtx, SmallVector<IVSRange, 4>& vals, int64_t Offset, uint64_t Len) {

  // Gap at left?
  initCtx->fill(0, vals[0].first.first - Offset);

  if(vals.size() > 1) {
    // Gaps between members?
    for(uint32_t i = 0, ilim = vals.size() - 1; i != ilim; ++i)
      initCtx->fill(vals[i].first.second - Offset, vals[i + 1].first.first - Offset);
  }

  // Gap at right?
  initCtx->fill(vals.back().first.second - Offset, Len);
  
  // Members already unknown at copy time?
  for(uint32_t i = 0, ilim = vals.size(); i != ilim; ++i) {

    if(vals[i].second.isWhollyUnknown())
      initCtx->fill(vals[i].first.first - Offset, vals[i].first.second - Offset);
    
  }

}

ThreadLocalState IntegrationAttempt::shouldCheckCopy(ShadowInstruction& SI, ShadowValue& PtrOp, ShadowValue& LenSV) {

  ConstantInt* LenC = cast_or_null<ConstantInt>(getConstReplacement(LenSV));
  std::pair<ValSetType, ImprovedVal> Ptr;

  if((!LenC) || (!tryGetUniqueIV(PtrOp, Ptr)) || Ptr.first != ValSetTypePB)
    return TLS_NEVERCHECK;

  uint64_t Len = LenC->getLimitedValue();
  if(Len == 0)
    return TLS_NEVERCHECK;

  // memcpyValues is unpopulated if the copy didn't "work" during specialisation,
  // so there is nothing to check.
  if((!SI.memcpyValues) || (!SI.memcpyValues->size()))
    return TLS_NEVERCHECK;

  // Create an initial context that marks as "don't care" bytes that are wholly unknown at the copy.
  TentativeLoadWalker::Ctx* initCtx = new TentativeLoadWalker::Ctx(Len);
  fillCtx(initCtx, *SI.memcpyValues, Ptr.second.Offset, Len);
  
  return shouldCheckRead(SI, Ptr.second, Len, initCtx);
    
}

ThreadLocalState IntegrationAttempt::shouldCheckLoadFrom(ShadowInstruction& SI, ImprovedVal& Ptr, uint64_t LoadSize) {

  if(Ptr.V.isNullOrConst())
    return TLS_NEVERCHECK;

  TentativeLoadWalker::Ctx* initCtx = new TentativeLoadWalker::Ctx(LoadSize);
  ImprovedValSetMulti* IV = dyn_cast<ImprovedValSetMulti>(SI.i.PB);

  if(IV) {

    SmallVector<IVSRange, 4> vals;
    for(ImprovedValSetMulti::MapIt it = IV->Map.begin(), itend = IV->Map.end(); it != itend; ++it)
      vals.push_back(std::make_pair(std::make_pair(it.start(), it.stop()), it.val()));

    fillCtx(initCtx, vals, 0, LoadSize);

  }

  return shouldCheckRead(SI, Ptr, LoadSize, initCtx);
  
}

ThreadLocalState IntegrationAttempt::shouldCheckLoad(ShadowInstruction& SI) {

  if(inst_is<LoadInst>(&SI)) {

    // Load doesn't extract any useful information?
    ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(SI.i.PB);
    if(IVS && IVS->isWhollyUnknown())
      return TLS_NEVERCHECK;

    ShadowValue PtrOp = SI.getOperand(0);
    std::pair<ValSetType, ImprovedVal> Single;
    ImprovedValSet* IV;

    uint64_t LoadSize = GlobalAA->getTypeStoreSize(SI.getType());

    getIVOrSingleVal(PtrOp, IV, Single);
    if(IV) {

      ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(IV);

      if(IVS->isWhollyUnknown() || IVS->SetType != ValSetTypePB)
	return TLS_NEVERCHECK;

      ThreadLocalState result = TLS_NEVERCHECK;

      for(uint32_t i = 0, ilim = IVS->Values.size(); i != ilim && result != TLS_MUSTCHECK; ++i)
	result = std::min(shouldCheckLoadFrom(SI, IVS->Values[i], LoadSize), result);

      return result;

    }
    else {

      if(Single.first != ValSetTypePB)
	return TLS_NEVERCHECK;
      return shouldCheckLoadFrom(SI, Single.second, LoadSize);

    }

  }
  else if(inst_is<MemTransferInst>(&SI)) {

    ShadowValue PtrOp = SI.getCallArgOperand(0);
    ShadowValue Len = SI.getCallArgOperand(2);

    return shouldCheckCopy(SI, PtrOp, Len);

  }
  else {

    // Realloc instruction
    ShadowValue PtrOp = SI.getCallArgOperand(0);
    std::pair<ValSetType, ImprovedVal> Ptr;
    if((!tryGetUniqueIV(PtrOp, Ptr)) || Ptr.first != ValSetTypePB)
      return TLS_NEVERCHECK;
    
    if((!SI.memcpyValues) || (!SI.memcpyValues->size()))
      return TLS_NEVERCHECK;
    
    uint64_t Len = Ptr.second.V.getAllocSize();

    TentativeLoadWalker::Ctx* initCtx = new TentativeLoadWalker::Ctx(Len);
    fillCtx(initCtx, *SI.memcpyValues, 0, Len);
    
    return shouldCheckRead(SI, Ptr.second, Len, initCtx);    

  }

}

bool ShadowInstruction::isCopyInst() {

  if(inst_is<MemTransferInst>(this))
    return true;

  if(inst_is<CallInst>(this)) {

    Function* F = getCalledFunction(this);
    if(F && F->getName() == "realloc")
      return true;

  }

  return false;

}

void IntegrationAttempt::findTentativeLoads() {

  // Don't repeat search due to sharing:
  if(tentativeLoadsRun)
    return;

  for(uint32_t i = 0, ilim = nBBs; i != ilim; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    if(BB->invar->naturalScope != L) {

      DenseMap<const Loop*, PeelAttempt*>::iterator findit = peelChildren.find(BB->invar->naturalScope);
      if(findit != peelChildren.end() && findit->second->isTerminated()) {
	while(i != ilim && findit->first->contains(getBBInvar(BBsOffset + i)->naturalScope))
	  ++i;
	--i;
	continue;
      }

    }

    for(uint32_t j = 0, jlim = BB->invar->insts.size(); j != jlim; ++j) {

      ShadowInstruction& SI = BB->insts[j];
      
      if(!(inst_is<LoadInst>(&SI) || SI.isCopyInst()))
	continue;

      // Known always good (as opposed to TLS_NOCHECK, resulting from a previous tentative loads run?)
      if(SI.isThreadLocal == TLS_NEVERCHECK)
	continue;

      SI.isThreadLocal = shouldCheckLoad(SI);

    }
    
  }

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    if(!it->second->isEnabled())
      continue;

    it->second->findTentativeLoads();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    if((!it->second->isTerminated()) || (!it->second->isEnabled()))
      continue;

    for(uint32_t i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->findTentativeLoads();

  }

}

void IntegrationAttempt::resetTentativeLoads() {

  tentativeLoadsRun = false;

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    if(!it->second->isEnabled())
      continue;
    
    it->second->resetTentativeLoads();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {
    
    if((!it->second->isTerminated()) || (!it->second->isEnabled()))
      continue;
    
    for(uint32_t i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->resetTentativeLoads();
    
  }

}

void IntegrationAttempt::rerunTentativeLoads() {

  resetTentativeLoads();
  findTentativeLoads();

}

// Our main interface to other passes:

bool llvm::requiresRuntimeCheck(ShadowValue V) {

  if(!V.isInst())
    return false;
  return V.u.I->parent->IA->requiresRuntimeCheck2(V);

}

bool PeelAttempt::containsYieldCalls() {

  for(uint32_t i = 0, ilim = Iterations.size(); i != ilim; ++i)
    if(Iterations[i]->containsYieldCalls())
      return true;

  return false;

}

bool IntegrationAttempt::containsYieldCalls() {

  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i);
    ShadowBB* BB = getBB(*BBI);

    if(BBI->naturalScope != L) {

      const Loop* subL = immediateChildLoop(L, BBI->naturalScope);
      if(peelChildren.count(subL)) {

	while(i != ilim && subL->contains(getBBInvar(i)->naturalScope))
	  ++i;
	--i;
	continue;

      }

    }

    for(uint32_t j = 0, jlim = BBI->insts.size(); j != jlim; ++j) {

      ShadowInstructionInvar& SII = BBI->insts[j];
      ShadowInstruction* SI = BB ? &BB->insts[j] : 0;

      if(isa<CallInst>(SII.I)) {

	Function* Called = SI ? getCalledFunction(SI) : cast<CallInst>(SII.I)->getCalledFunction();
	if((!Called) || pass->yieldFunctions.count(Called))
	  return true;

      }

    }

  }

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    if(it->second->containsYieldCalls())
      return true;

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    if(it->second->containsYieldCalls())
      return true;

  }

  return false;

}

bool IntegrationAttempt::requiresRuntimeCheck2(ShadowValue V) {

  if(val_is<LoadInst>(V) || val_is<MemTransferInst>(V)) {
    
    if(V.u.I->isThreadLocal == TLS_MUSTCHECK)
      return true;
    
  }
  else if (val_is<CallInst>(V)) {
      
    InlineAttempt* IA = getInlineAttempt(V.u.I);
    if(IA && (!IA->isEnabled()) && IA->containsYieldCalls())
      return true;

  }
  else if(val_is<PHINode>(V)) {

    ShadowBB* BB = V.u.I->parent;
    for(uint32_t i = 0, ilim = BB->invar->predIdxs.size(); i != ilim; ++i) {

      ShadowBBInvar* predBBI = getBBInvar(BB->invar->predIdxs[i]);
      if(predBBI->naturalScope != L && ((!L) || L->contains(predBBI->naturalScope))) {

	PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(L, predBBI->naturalScope));
	if(LPA && (!LPA->isEnabled()) && LPA->containsYieldCalls())
	  return true;

      }

    }

  }

  return false;

}
