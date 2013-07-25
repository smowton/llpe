// Dead store elimination using essentially the same technique as Transforms/Scalar/DSE.cpp,
// only taking into account that we've been computing a probable flow through the program.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/DataLayout.h"

#include <vector>

using namespace llvm;

bool IntegrationAttempt::tryKillStore(ShadowInstruction* SI) {

  uint64_t Size = (GlobalTD->getTypeSizeInBits(SI->invar->I->getOperand(0)->getType()) + 7) / 8;
  return tryKillWriterTo(SI, SI->getOperand(1), Size);
  
}

bool IntegrationAttempt::tryKillMemset(ShadowInstruction* MI) {

  ConstantInt *SizeCst = dyn_cast_or_null<ConstantInt>(getConstReplacement(MI->getCallArgOperand(2)));
  uint64_t MemSize;
  if(SizeCst)
    MemSize = SizeCst->getZExtValue();
  else
    MemSize = AliasAnalysis::UnknownSize;
  return tryKillWriterTo(MI, MI->getCallArgOperand(0), MemSize);

}

bool IntegrationAttempt::tryKillRead(ShadowInstruction* CI, ReadFile& RF) {

  return tryKillWriterTo(CI, CI->getCallArgOperand(1), RF.readSize);

}

bool IntegrationAttempt::tryKillMTI(ShadowInstruction* MTI) {

  ConstantInt* SizeC = dyn_cast_or_null<ConstantInt>(getConstReplacement(MTI->getCallArgOperand(2)));
  uint64_t MISize;
  if(SizeC)
    MISize = SizeC->getZExtValue();
  else
    MISize = AliasAnalysis::UnknownSize;  

  return tryKillWriterTo(MTI, MTI->getCallArgOperand(0), MISize);

}

bool IntegrationAttempt::tryKillAlloc(ShadowInstruction* Alloc) {

  // The 'unknown size' thing is a bit of a hack -- it just prevents TKWT from ever
  // concluding that enough bytes have been clobbered that the allocation is pointless.
  // Rather the only way it will die is if we make it all the way to end-of-life.
  return tryKillWriterTo(Alloc, ShadowValue(Alloc), AliasAnalysis::UnknownSize); 

}

//// Implement a forward walker to determine if a store is redundant on all paths.

class WriterUsedWalker : public ForwardIAWalker {

  ShadowValue StorePtr;
  ShadowValue StoreBase;
  int64_t StoreOffset;
  uint64_t StoreSize;

public:

  bool writeUsed;

  WriterUsedWalker(ShadowInstruction* StartInst, void* StartCtx, ShadowValue SP, ShadowValue SB, int64_t SO, uint64_t SS) : ForwardIAWalker(StartInst->invar->idx, StartInst->parent, true, StartCtx, false), StorePtr(SP), StoreBase(SB), StoreOffset(SO), StoreSize(SS), writeUsed(false) { }

  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void* Context);
  virtual bool shouldEnterCall(ShadowInstruction*, void*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);
  virtual void freeContext(void*);
  virtual void* copyContext(void*);
  virtual void enterCall(InlineAttempt*, void*);
  virtual void leaveCall(InlineAttempt*, void*);
  virtual void enterLoop(PeelAttempt*, void*);
  virtual void leaveLoop(PeelAttempt*, void*);
  virtual void hitIgnoredEdge() { writeUsed = true; }
  virtual bool shouldContinue() { return !writeUsed; }

};

struct WriterUsedWalkerCtx {

  WriterUsedWalkerCtx(uint64_t Size) {
    if(Size != AliasAnalysis::UnknownSize)
      bytesWritten = new std::vector<bool>(Size, false);
    else
      bytesWritten = 0;
    commitDisabledDuring.IA = 0;
  }

  WriterUsedWalkerCtx(const WriterUsedWalkerCtx& other) {
    commitDisabledDuring.IA = other.commitDisabledDuring.IA;
    if(other.bytesWritten)
      bytesWritten = new std::vector<bool>(*(other.bytesWritten));
    else
      bytesWritten = 0;
  }

  ~WriterUsedWalkerCtx() {
    if(bytesWritten)
      delete bytesWritten;
  }

  std::vector<bool>* bytesWritten;
  union {
    InlineAttempt* IA;
    PeelAttempt* LPA;
  } commitDisabledDuring;

};

// Context objects for these writers are bool vectors sized to match the writer's byte count.
// Each field indicates whether that byte has been written on this path.

void WriterUsedWalker::freeContext(void* V) {

  if(V) {
    WriterUsedWalkerCtx* Ctx = (WriterUsedWalkerCtx*)V;
    delete Ctx;
  }

}

void* WriterUsedWalker::copyContext(void* V) {

  if(V) {
    WriterUsedWalkerCtx* Ctx = (WriterUsedWalkerCtx*)V;
    WriterUsedWalkerCtx* NewCtx = new WriterUsedWalkerCtx(*Ctx);
    return NewCtx;
  }
  else {
    return 0;
  }

}

WalkInstructionResult IntegrationAttempt::noteBytesWrittenBy(ShadowInstruction* I, ShadowValue StorePtr, ShadowValue StoreBase, int64_t StoreOffset, uint64_t Size, std::vector<bool>* writtenBytes, bool commitDisabledHere) {

  if(isLifetimeEnd(StoreBase, I)) {

    return WIRStopThisPath;

  }
  else if(inst_is<MemIntrinsic>(I)) {

    ConstantInt* SizeC = cast_or_null<ConstantInt>(getConstReplacement(I->getCallArgOperand(2)));
    uint64_t MISize;
    if(SizeC)
      MISize = SizeC->getZExtValue();
    else
      MISize = AliasAnalysis::UnknownSize;

    if(inst_is<MemTransferInst>(I)) {

      if(!(I->i.dieStatus & INSTSTATUS_UNUSED_WRITER)) {

	ShadowValue Pointer = I->getCallArgOperand(1);
	SVAAResult R = aliasSVs(Pointer, MISize, StorePtr, Size, true);

	if(R != SVNoAlias) {

	  // If it's not dead it must be regarded as a big unresolved load.

	  LPDEBUG("Can't kill store to " << itcache(StorePtr) << " because of unresolved MTI " << itcache(*I) << "\n");
	  return WIRStopWholeWalk;

	}

      }
	  
    }
    // If the size is unknown we must assume zero.
    if(MISize != AliasAnalysis::UnknownSize) {

      if(DSEHandleWrite(I->getCallArgOperand(0), MISize, StorePtr, Size, StoreBase, StoreOffset, writtenBytes))
	return WIRStopThisPath;
      else
	return WIRContinue;

    }

  }
  else if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {

    DenseMap<CallInst*, ReadFile>::iterator RI = resolvedReadCalls.find(CI);
    if(RI != resolvedReadCalls.end()) {

      if(DSEHandleWrite(I->getCallArgOperand(1), RI->second.readSize, StorePtr, Size, StoreBase, StoreOffset, writtenBytes))
	return WIRStopThisPath;
      else
	return WIRContinue;

    }

  }
  else if(inst_is<LoadInst>(I)) {

    ShadowValue Pointer = I->getOperand(0);
    uint64_t LoadSize = GlobalAA->getTypeStoreSize(I->getType());

    if(mayBeReplaced(I) && !commitDisabledHere) {

      // mayBeReplaced implies a single value.
      ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(I->i.PB);
      if(IVS->SetType == ValSetTypePB || IVS->SetType == ValSetTypeFD) {

	ShadowValue Base = IVS->Values[0].V;
	if((!Base.getCtx()) || Base.objectAvailableFrom(I->parent->IA))
	  return WIRContinue;

      }
      else {

	return WIRContinue;

      }

    }
    
    // Otherwise the load will happen for real at runtime: check if it may alias:

    SVAAResult R = aliasSVs(Pointer, LoadSize, StorePtr, Size, true);
    if(R != SVNoAlias) {

      LPDEBUG("Can't kill store to " << itcache(StorePtr) << " because of unresolved load " << itcache(Pointer) << "\n");
      return WIRStopWholeWalk;
	  
    }

  }
  else if(inst_is<StoreInst>(I)) {

    ShadowValue Pointer = I->getOperand(1);
    uint64_t StoreSize = GlobalAA->getTypeStoreSize(I->invar->I->getOperand(0)->getType());

    if(DSEHandleWrite(Pointer, StoreSize, StorePtr, Size, StoreBase, StoreOffset, writtenBytes))
      return WIRStopThisPath;
    else
      return WIRContinue;

  }

  return WIRContinue;

}

WalkInstructionResult WriterUsedWalker::walkInstruction(ShadowInstruction* I, void* Vctx) {

  WriterUsedWalkerCtx* Ctx = (WriterUsedWalkerCtx*)Vctx;
  // Ctx->commitDisabledDuring.LPA aliases Ctx->commitDisabledDuring.IA so this really means
  // is commit disabled here.
  WalkInstructionResult Res = I->parent->IA->noteBytesWrittenBy(I, StorePtr, StoreBase, StoreOffset, StoreSize, Ctx->bytesWritten, !!Ctx->commitDisabledDuring.LPA);

  if(Res == WIRStopWholeWalk)
    writeUsed = true;

  return Res;

}

bool IntegrationAttempt::callUsesPtr(ShadowInstruction* CI, ShadowValue StorePtr, uint64_t Size) {

  AliasAnalysis::ModRefResult MR = GlobalAA->getCSModRefInfo(ShadowValue(CI), StorePtr, Size, StorePtr.getTBAATag());
  return !!(MR & AliasAnalysis::Ref);

}

bool WriterUsedWalker::shouldEnterCall(ShadowInstruction* CI, void*) {

  return CI->parent->IA->callUsesPtr(CI, StorePtr, StoreSize);

}

bool WriterUsedWalker::blockedByUnexpandedCall(ShadowInstruction*, void*) {

  writeUsed = true;
  return true;

}

static uint32_t DSEProgressN = 0;
const uint32_t DSEProgressLimit = 1000;

static void DSEProgress() {

  DSEProgressN++;
  if(DSEProgressN == DSEProgressLimit) {

    errs() << ".";
    DSEProgressN = 0;

  }

}

// Note here commitDisabledDuring.LPA and IA are unioned,
// so test for zero against one tests both.
void WriterUsedWalker::enterLoop(PeelAttempt* L, void* Vctx) {

  WriterUsedWalkerCtx* ctx = (WriterUsedWalkerCtx*)Vctx;
  if((!ctx->commitDisabledDuring.LPA) && !L->isEnabled())
    ctx->commitDisabledDuring.LPA = L;

}

void WriterUsedWalker::leaveLoop(PeelAttempt* L, void* Vctx) {

  WriterUsedWalkerCtx* ctx = (WriterUsedWalkerCtx*)Vctx;
  if(ctx->commitDisabledDuring.LPA == L)
    ctx->commitDisabledDuring.LPA = 0;

}

void WriterUsedWalker::enterCall(InlineAttempt* Call, void* Vctx) {

  WriterUsedWalkerCtx* ctx = (WriterUsedWalkerCtx*)Vctx;
  if((!ctx->commitDisabledDuring.IA) && !Call->isEnabled())
    ctx->commitDisabledDuring.IA = Call;

}

void WriterUsedWalker::leaveCall(InlineAttempt* Call, void* Vctx) {

  WriterUsedWalkerCtx* ctx = (WriterUsedWalkerCtx*)Vctx;
  if(ctx->commitDisabledDuring.IA == Call)
    ctx->commitDisabledDuring.IA = 0;

}

bool IntegrationAttempt::tryKillWriterTo(ShadowInstruction* Writer, ShadowValue StorePtr, uint64_t Size) {

  DSEProgress();

  WriterUsedWalkerCtx* Ctx = new WriterUsedWalkerCtx(Size);
  void* initialCtx = Ctx;

  int64_t StoreOffset = 0;
  ShadowValue StoreBase;
  if(!getBaseAndConstantOffset(StorePtr, StoreBase, StoreOffset))
    return false;

  WriterUsedWalker Walk(Writer, initialCtx, StorePtr, StoreBase, StoreOffset, Size);
  // This will deallocate initialCtx.
  Walk.walk();

  if(!Walk.writeUsed) {
    
    Writer->i.dieStatus |= INSTSTATUS_UNUSED_WRITER;

  }

  return !Walk.writeUsed;

}

bool IntegrationAttempt::DSEHandleWrite(ShadowValue Writer, uint64_t WriteSize, ShadowValue StorePtr, uint64_t Size, ShadowValue StoreBase, int64_t StoreOffset, std::vector<bool>* deadBytes) {

  if(!deadBytes)
    return false;

  SVAAResult R = aliasSVs(Writer, WriteSize, StorePtr, Size, true);

  int64_t WriteOffset = 0;
  ShadowValue WriteBase;
  if(!getBaseAndConstantOffset(Writer, WriteBase, WriteOffset))
    return false;
  
  uint64_t Offset, FirstDef, FirstNotDef;

  if(R == SVMayAlias || R == SVPartialAlias) {

    if(!GetDefinedRange(StoreBase, StoreOffset, Size,
			WriteBase, WriteOffset, WriteSize,
			Offset, FirstDef, FirstNotDef)) {
	    
      FirstDef = 0; 
      FirstNotDef = 0;

    }
	  
  }
  else if(R == SVMustAlias) {

    FirstDef = 0;
    FirstNotDef = std::min(WriteSize, Size);

  }
  else {
	  
    FirstDef = 0; 
    FirstNotDef = 0;

  }

  if(FirstDef != FirstNotDef) {

    bool Finished = true;

    for(uint64_t i = 0; i < Size && Finished; ++i) {

      if(i >= FirstDef && i < FirstNotDef)
	(*deadBytes)[i] = true;
      else if(!((*deadBytes)[i]))
	Finished = false;

    }

    if(Finished) {
      LPDEBUG("Write " << itcache(Writer) << " wrote bytes (" << FirstDef << "-" << FirstNotDef << "] (finished, killed)\n");
      return true;
    }
    else {
      LPDEBUG("Write " << itcache(Writer) << " wrote bytes (" << FirstDef << "-" << FirstNotDef << "] (not finished yet)\n");
    }

  }

  return false;

}

InlineAttempt* PeelIteration::getFunctionRoot() {

  return parent->getFunctionRoot();

}

InlineAttempt* InlineAttempt::getFunctionRoot() {

  return this;

}

bool IntegrationAttempt::isLifetimeEnd(ShadowValue Alloc, ShadowInstruction* I) {

  if(val_is<AllocaInst>(Alloc)) {

    // Are we about to return from the function that defines the alloca's lifetime?
    if(TerminatorInst* TI = dyn_cast_inst<TerminatorInst>(I)) {
      return (TI->getNumSuccessors() == 0) && (Alloc.getCtx()->getFunctionRoot() == this);
    }

  }
  else if(I->allocIdx != -1) { 

    // allocIdx being set for a non-alloca means this is malloc or realloc.

    const CallInst* Free = isFreeCall(I->invar->I, GlobalTLI, true);
    if(Free) {

      ShadowValue FreeBase;
      ShadowValue FirstArg = I->getCallArgOperand(0);
      if(getBaseObject(FirstArg, FreeBase))
	return FreeBase == Alloc;

    }

  }

  return false;

}

void IntegrationAttempt::tryKillAllMTIs() {

  if(!isEnabled())
    return;

  // Must kill MTIs in reverse topological order. Our ShadowBBs are already in forwards toporder.

  for(uint32_t i = nBBs; i > 0; --i) {

    ShadowBB* BB = BBs[i-1];
    if(!BB)
      continue;

    if(BB->invar->naturalScope != L) {

      const Loop* enterLoop = immediateChildLoop(L, BB->invar->naturalScope);

      if(PeelAttempt* LPA = getPeelAttempt(enterLoop)) {

	// Process loop iterations in reverse order:
	for(int j = LPA->Iterations.size() - 1; j >= 0; --j) {

	  LPA->Iterations[j]->tryKillAllMTIs();

	}

	// Skip loop blocks:
	while(i > 0 && ((!BBs[i-1]) || enterLoop->contains(BBs[i-1]->invar->naturalScope)))
	  --i;
	++i;
	continue;

      }
      // Else enter the block as usual.

    }

    for(uint32_t j = BB->insts.size(); j > 0; --j) {

      ShadowInstruction* I = &(BB->insts[j-1]);
      
      if(inst_is<MemTransferInst>(I)) {

	tryKillMTI(I);

      }
      else if(inst_is<CallInst>(I)) {

	if(InlineAttempt* IA = getInlineAttempt(I))
	  IA->tryKillAllMTIs();

      }
      
    }

  }

}

void IntegrationAttempt::tryKillAllStores() {

  if(!isEnabled())
    return;

  for(uint32_t i = 0; i < nBBs; ++i) {
    
    ShadowBB* BB = BBs[i];

    if(!BB)
      continue;
    if(BB->invar->outerScope != L)
      continue;
    
    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);

      if(inst_is<StoreInst>(I)) {
	
	tryKillStore(I);
	
      }
      else if(inst_is<MemSetInst>(I)) {
	
	tryKillMemset(I);
	
      }
      else if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {
	
	DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
	if(it != resolvedReadCalls.end()) {
	  
	  tryKillRead(I, it->second);
	  
	}

      }

    }

  }

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->tryKillAllStores();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->tryKillAllStores();

  }

}

void IntegrationAttempt::tryKillAllAllocs() {

  if(!isEnabled())
    return;

  for(uint32_t i = 0; i < nBBs; ++i) {
    
    ShadowBB* BB = BBs[i];

    if(!BB)
      continue;
    if(BB->invar->outerScope != L)
      continue;
    
    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);

      if(inst_is<AllocaInst>(I)) {
      
	tryKillAlloc(I);

      }

    }

  }

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->tryKillAllAllocs();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->tryKillAllAllocs();

  }

}



