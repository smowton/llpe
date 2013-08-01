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

    Ctx(uint64_t size) {

      goodBytes = new bool[size];
      memset(goodBytes, 0, sizeof(bool) * size);

    }

    Ctx(Ctx* other, uint64_t size) {

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

  WalkInstructionResult markGoodBytes(ShadowValue GoodPtr, uint64_t Len, void* vctx);
  WalkInstructionResult walkCopyInst(ShadowValue CopyFrom, ShadowValue CopyTo, ShadowValue LenSV, void*);
  

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
    shouldCheckLoad(false) {}

  bool shouldCheckLoad;

};

// Prevent walking up from the allocation context, since the edges followed must route around the allocation.
WalkInstructionResult TentativeLoadWalker::mayAscendFromContext(IntegrationAttempt* IA, void* Ctx) {

  ShadowInstruction* readInst = readPtr.V.getInst();
  if(readInst && readInst->parent->IA == IA)
    return WIRStopThisPath;

  return WIRContinue;

}

WalkInstructionResult TentativeLoadWalker::markGoodBytes(ShadowValue GoodPtr, uint64_t Len, void* vctx) {

  std::pair<ValSetType, ImprovedVal> PtrTarget;
  if(!tryGetUniqueIV(GoodPtr, PtrTarget))
    return WIRContinue;

  if(PtrTarget.first != ValSetTypePB)
    return WIRContinue;

  uint64_t FirstDef, FirstNotDef, Ignored;
  if(!GetDefinedRange(readPtr.V, readPtr.Offset, readSize, 
		      PtrTarget.second.V, PtrTarget.second.Offset, Len,
		      FirstDef, FirstNotDef, Ignored))
    return WIRContinue;

  bool allGood = true;

  Ctx* ctx = (Ctx*)vctx;

  for(uint64_t i = 0, ilim = readSize; i != ilim && (allGood || i < FirstNotDef); ++i) {

    if(i >= FirstDef && i < FirstNotDef)
      ctx->goodBytes[i] = true;
    else if(!ctx->goodBytes[i])
      allGood = false;

  }

  return allGood ? WIRStopThisPath : WIRContinue;

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
      shouldCheckLoad = true;
      return WIRStopWholeWalk;
    }
      
    return markGoodBytes(LI->getOperand(0), GlobalAA->getTypeStoreSize(LI->getType()), vctx);

  }
  else if(StoreInst* StoreI = dyn_cast_inst<StoreInst>(SI)) {
    
    if(StoreI->isVolatile()) {
      shouldCheckLoad = true;
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

	shouldCheckLoad = true;
	return WIRStopWholeWalk;

      }      

    }

  }

  return WIRContinue;

}

bool IntegrationAttempt::shouldCheckRead(ShadowInstruction& Start, ImprovedVal& Ptr, uint64_t Size, void* initCtx) {
  
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

bool IntegrationAttempt::shouldCheckCopy(ShadowInstruction& SI, ShadowValue& PtrOp, ShadowValue& LenSV) {

  ConstantInt* LenC = cast_or_null<ConstantInt>(getConstReplacement(LenSV));
  std::pair<ValSetType, ImprovedVal> Ptr;

  if((!LenC) || (!tryGetUniqueIV(PtrOp, Ptr)) || Ptr.first != ValSetTypePB)
    return false;

  uint64_t Len = LenC->getLimitedValue();
  if(Len == 0)
    return false;

  // memcpyValues is unpopulated if the copy didn't "work" during specialisation,
  // so there is nothing to check.
  if((!SI.memcpyValues) || (!SI.memcpyValues->size()))
    return false;

  // Create an initial context that marks as "don't care" bytes that are wholly unknown at the copy.
  TentativeLoadWalker::Ctx* initCtx = new TentativeLoadWalker::Ctx(Len);
  fillCtx(initCtx, *SI.memcpyValues, Ptr.second.Offset, Len);
  
  return shouldCheckRead(SI, Ptr.second, Len, initCtx);
    
}

bool IntegrationAttempt::shouldCheckLoadFrom(ShadowInstruction& SI, ImprovedVal& Ptr, uint64_t LoadSize) {

  if(Ptr.V.isNullOrConst())
    return false;

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

bool IntegrationAttempt::shouldCheckLoad(ShadowInstruction& SI) {

  if(inst_is<LoadInst>(&SI)) {

    // Load doesn't extract any useful information?
    ImprovedValSetSingle* IVS = dyn_cast<ImprovedValSetSingle>(SI.i.PB);
    if(IVS && IVS->isWhollyUnknown())
      return false;

    ShadowValue PtrOp = SI.getOperand(0);
    std::pair<ValSetType, ImprovedVal> Single;
    ImprovedValSet* IV;

    uint64_t LoadSize = GlobalAA->getTypeStoreSize(SI.getType());

    getIVOrSingleVal(PtrOp, IV, Single);
    if(IV) {

      ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(IV);

      if(IVS->isWhollyUnknown() || IVS->SetType != ValSetTypePB)
	return false;

      for(uint32_t i = 0, ilim = IVS->Values.size(); i != ilim; ++i)
	if(shouldCheckLoadFrom(SI, IVS->Values[i], LoadSize))
	  return true;

      return false;

    }
    else {

      if(Single.first != ValSetTypePB)
	return false;
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
      return false;
    
    if((!SI.memcpyValues) || (!SI.memcpyValues->size()))
      return false;
    
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

      // Already known good?
      if(SI.isThreadLocal)
	continue;

      SI.isThreadLocal = !shouldCheckLoad(SI);

    }
    
  }

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(),
	itend = inlineChildren.end(); it != itend; ++it) {

    it->second->findTentativeLoads();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    if(!it->second->isTerminated())
      continue;

    for(uint32_t i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->findTentativeLoads();

  }

}
