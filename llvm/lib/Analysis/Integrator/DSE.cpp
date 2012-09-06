// Dead store elimination using essentially the same technique as Transforms/Scalar/DSE.cpp,
// only taking into account that we've been computing a probable flow through the program.

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/Debug.h"
#include <llvm/Support/raw_ostream.h>

#include <vector>

using namespace llvm;

bool IntegrationAttempt::tryKillStore(StoreInst* SI) {

  uint64_t Size = (TD->getTypeSizeInBits(SI->getValueOperand()->getType()) + 7) / 8;
  return tryKillWriterTo(SI, SI->getPointerOperand(), Size);
  
}

bool IntegrationAttempt::tryKillMemset(MemIntrinsic* MI) {

  ConstantInt *SizeCst = dyn_cast_or_null<ConstantInt>(getConstReplacement(MI->getLength()));
  uint64_t MemSize;
  if(SizeCst)
    MemSize = SizeCst->getZExtValue();
  else
    MemSize = AliasAnalysis::UnknownSize;
  return tryKillWriterTo(MI, MI->getDest(), MemSize);

}

bool IntegrationAttempt::tryKillMTI(MemTransferInst* MTI) {

  ConstantInt* SizeC = dyn_cast_or_null<ConstantInt>(getConstReplacement(MTI->getLength()));
  uint64_t MISize;
  if(SizeC)
    MISize = SizeC->getZExtValue();
  else
    MISize = AliasAnalysis::UnknownSize;  

  return tryKillWriterTo(MTI, MTI->getDest(), MISize);

}

bool IntegrationAttempt::tryKillAlloc(Instruction* Alloc) {

  // The 'unknown size' thing is a bit of a hack -- it just prevents TKWT from ever
  // concluding that enough bytes have been clobbered that the allocation is pointless.
  // Rather the only way it will die is if we make it all the way to end-of-life.
  return tryKillWriterTo(Alloc, Alloc, AliasAnalysis::UnknownSize); 

}

void IntegrationAttempt::addTraversingInst(ValCtx VC) {

  deadValuesTraversingThisContext.insert(VC);
  
}

bool IntegrationAttempt::tryKillWriterTo(Instruction* Writer, Value* WritePtr, uint64_t Size) {

  bool* deadBytes;

  LPDEBUG("Trying to kill instruction " << *Writer << "\n");

  if(Size != AliasAnalysis::UnknownSize) {
    deadBytes = (bool*)alloca(Size * sizeof(bool));
    for(uint64_t i = 0; i < Size; ++i)
      deadBytes[i] = false;
  }
  else {
    deadBytes = 0;
  }

  ValCtx StorePtr = make_vc(WritePtr, this);

  int64_t StoreOffset;
  ValCtx StoreBase = GetBaseWithConstantOffset(WritePtr, this, StoreOffset);

  ValCtx NextStart = make_vc(Writer, this);

  bool skipFirst = true;
  bool Killed = false;

  SmallVector<IntegrationAttempt*, 4> WalkCtxs;
  WalkCtxs.push_back(this);

  while(NextStart.second->tryKillStoreFrom(NextStart, StorePtr, StoreBase, StoreOffset, deadBytes, Size, skipFirst, Killed)) {
    LPDEBUG("Continuing from " << NextStart << "\n");
    WalkCtxs.push_back(NextStart.second);
    skipFirst = false;
  }

  if(Killed) {
    deadValues.insert(Writer);
    for(SmallVector<IntegrationAttempt*, 4>::iterator it = WalkCtxs.begin(), it2 = WalkCtxs.end(); it != it2; ++it) {

      (*it)->addTraversingInst(make_vc(Writer, this));

    }
  }

  return Killed;

}

bool IntegrationAttempt::DSEHandleWrite(ValCtx Writer, uint64_t WriteSize, ValCtx StorePtr, uint64_t Size, ValCtx StoreBase, int64_t StoreOffset, bool* deadBytes) {

  if(!deadBytes)
    return false;

  AliasAnalysis::AliasResult R = AA->aliasHypothetical(Writer, WriteSize, StorePtr, Size);

  int64_t WriteOffset;
  ValCtx WriteBase = GetBaseWithConstantOffset(Writer.first, Writer.second, WriteOffset);

  uint64_t Offset, FirstDef, FirstNotDef;

  if(R == AliasAnalysis::MayAlias) {

    if(!GetDefinedRange(StoreBase, StoreOffset, Size * 8,
			WriteBase, WriteOffset, WriteSize * 8,
			Offset, FirstDef, FirstNotDef)) {
	    
      FirstDef = 0; 
      FirstNotDef = 0;

    }
	  
  }
  else if(R == AliasAnalysis::MustAlias) {

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
	deadBytes[i] = true;
      else if(!deadBytes[i])
	Finished = false;

    }

    if(Finished) {
      LPDEBUG("Write " << Writer << " wrote bytes (" << FirstDef << "-" << FirstNotDef << "] (finished, killed)\n");
      return true;
    }
    else {
      LPDEBUG("Write " << Writer << " wrote bytes (" << FirstDef << "-" << FirstNotDef << "] (not finished yet)\n");
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

bool IntegrationAttempt::isLifetimeEnd(ValCtx Alloc, Instruction* I) {

  if(isa<AllocaInst>(Alloc.first)) {

    // Are we about to return from the function that defines the alloca's lifetime?
    if(TerminatorInst* TI = dyn_cast<TerminatorInst>(I)) {
      return (TI->getNumSuccessors() == 0) && (Alloc.second->getFunctionRoot() == this);
    }

  }
  else if(isMalloc(Alloc.first)) {

    const CallInst* Free = isFreeCall(I);
    if(Free) {

      ValCtx Pointer = getReplacement(Free->getArgOperand(0));
      return Pointer == Alloc;

    }

  }

  return false;

}

bool IntegrationAttempt::tryKillStoreFrom(ValCtx& Start, ValCtx StorePtr, ValCtx StoreBase, int64_t StoreOffset, bool* deadBytes, uint64_t Size, bool skipFirst, bool& Killed) {

  Instruction* StartI = cast<Instruction>(Start.first);
  BasicBlock* BB = StartI->getParent();
  BasicBlock::iterator BI(StartI);

  while(1) {

    if(!skipFirst) {

      if(isLifetimeEnd(StoreBase, BI)) {

	LPDEBUG("Killed write to " << *(StorePtr.first) << " due to reaching end of lifetime for " << StoreBase << "\n");
	Killed = true;
	return false;

      }
      else if(MemIntrinsic* MI = dyn_cast<MemIntrinsic>(BI)) {

	ConstantInt* SizeC = dyn_cast_or_null<ConstantInt>(getConstReplacement(MI->getLength()));
	uint64_t MISize;
	if(SizeC)
	  MISize = SizeC->getZExtValue();
	else
	  MISize = AliasAnalysis::UnknownSize;

	if(MemTransferInst* MTI = dyn_cast<MemTransferInst>(MI)) {

	  if(!deadValues.count(MTI)) {

	    Value* Pointer = MTI->getSource();
	    AliasAnalysis::AliasResult R = AA->aliasHypothetical(make_vc(Pointer, this), MISize, StorePtr, Size);

	    if(R != AliasAnalysis::NoAlias) {

	      // If it's not dead it must be regarded as a big unresolved load.

	      LPDEBUG("Can't kill store to " << StorePtr << " because of unresolved MTI " << *MI << "\n");
	      return false;

	    }

	  }
	  
	}
     
	// If the size is unknown we must assume zero.
	if(MISize != AliasAnalysis::UnknownSize) {

	  if(DSEHandleWrite(make_vc(MI->getDest(), this), MISize, StorePtr, Size, StoreBase, StoreOffset, deadBytes)) {
	    Killed = true;
	    return false;
	  }

	}

      }
      else if(CallInst* CI = dyn_cast<CallInst>(BI)) {

	AliasAnalysis::ModRefResult MR = AA->getModRefInfo(CI, StorePtr.first, Size, this, StorePtr.second);

	if(MR != AliasAnalysis::NoModRef) {

	  if(InlineAttempt* IA = getInlineAttempt(CI)) {

	    Start = make_vc(IA->getEntryBlock()->begin(), IA);
	    return true;

	  }
	  else {

	    if(MR & AliasAnalysis::Ref) {

	      LPDEBUG("Unexpanded call " << *CI << " blocks DSE\n");
	      return false;

	    }
	    // Otherwise it doesn't read from the pointer, keep looking for a defn.

	  }

	}

      }
      else if(LoadInst* LI = dyn_cast<LoadInst>(BI)) {

	ValCtx Res = getReplacement(LI);
	if(Res == getDefaultVC(LI) || !Res.second->isAvailable()) {
	  
	  AliasAnalysis::AliasResult R = AA->aliasHypothetical(make_vc(Pointer, this), LoadSize, StorePtr, Size);
	  if(R != AliasAnalysis::NoAlias) {

	    Value* Pointer = LI->getPointerOperand();
	    uint64_t LoadSize = AA->getTypeStoreSize(LI->getType());

	    LPDEBUG("Can't kill store to " << StorePtr << " because of unresolved load " << *Pointer << "\n");
	    return false;

	  }

	}

      }
      else if(StoreInst* SI = dyn_cast<StoreInst>(BI)) {

	Value* Pointer = SI->getPointerOperand();
	uint64_t StoreSize = AA->getTypeStoreSize(SI->getValueOperand()->getType());

	if(DSEHandleWrite(make_vc(Pointer, this), StoreSize, StorePtr, Size, StoreBase, StoreOffset, deadBytes)) {

	  Killed = true;
	  return false;

	}

      }

    }

    skipFirst = false;

    ++BI;
    if(BI == BB->end()) {

      Start = getSuccessorVC(BB);

      if(Start == VCNull)
	return false;
      else if(Start.second != this)
	return true;
      else {

	StartI = cast<Instruction>(Start.first);
	BB = StartI->getParent();
	BI = BasicBlock::iterator(StartI);

      }

    }

  }
  
}

bool IntegrationAttempt::CollectMTIsFrom(ValCtx& Start, std::vector<ValCtx>& MTIs) {

  Instruction* StartI = cast<Instruction>(Start.first);
  BasicBlock* BB = StartI->getParent();
  BasicBlock::iterator BI(StartI);

  while(1) {

    if(MemTransferInst* MTI = dyn_cast<MemTransferInst>(BI)) {

      MTIs.push_back(make_vc(MTI, this));

    }
    else if(CallInst* CI = dyn_cast<CallInst>(BI)) {

      if(InlineAttempt* IA = getInlineAttempt(CI)) {
	
	Start = make_vc(IA->getEntryBlock()->begin(), IA);
	return true;
	    
      }

    }


    ++BI;
    if(BI == BB->end()) {
      
      Start = getSuccessorVC(BB);
      
      if(Start == VCNull)
	return false;
      else if(Start.second != this)
	return true;
      else {
	
	StartI = cast<Instruction>(Start.first);
	BB = StartI->getParent();
	BI = BasicBlock::iterator(StartI);

      }

    }

  }

}

void IntegrationAttempt::tryKillAllMTIs() {

  // Must kill MTIs backwards, from program end to start.
  
  std::vector<ValCtx> MTIs;
  ValCtx Start = make_vc(F.getEntryBlock().begin(), this);

  while(Start.second->CollectMTIsFrom(Start, MTIs)) {  }

  for(std::vector<ValCtx>::reverse_iterator it = MTIs.rbegin(), it2 = MTIs.rend(); it != it2; ++it) {
    it->second->tryKillMTI(cast<MemTransferInst>(it->first));
  }

}

bool IntegrationAttempt::tryKillAllStoresFrom(ValCtx& Start) {

  Instruction* StartI = cast<Instruction>(Start.first);
  BasicBlock* BB = StartI->getParent();
  BasicBlock::iterator BI(StartI);

  while(1) {

    if(StoreInst* SI = dyn_cast<StoreInst>(BI)) {

      tryKillStore(SI);

    }
    else if(MemSetInst* MI = dyn_cast<MemSetInst>(BI)) {

      tryKillMemset(MI);

    }
    else if(CallInst* CI = dyn_cast<CallInst>(BI)) {

      if(InlineAttempt* IA = getInlineAttempt(CI)) {

	Start = make_vc(IA->getEntryBlock()->begin(), IA);
	return true;
	    
      }

    }

    ++BI;
    if(BI == BB->end()) {
      
      Start = getSuccessorVC(BB);
      
      if(Start == VCNull)
	return false;
      else if(Start.second != this)
	return true;
      else {

	StartI = cast<Instruction>(Start.first);
	BB = StartI->getParent();
	BI = BasicBlock::iterator(StartI);

      }

    }

  }

}

void IntegrationAttempt::tryKillAllStores() {

  ValCtx Start = make_vc(F.getEntryBlock().begin(), this);

  while(Start.second->tryKillAllStoresFrom(Start)) { }

}

bool IntegrationAttempt::tryKillAllAllocsFrom(ValCtx& Start) {

  Instruction* StartI = cast<Instruction>(Start.first);
  BasicBlock* BB = StartI->getParent();
  BasicBlock::iterator BI(StartI);

  while(1) {

    if(isa<AllocaInst>(BI) || isMalloc(BI)) {
      
      tryKillAlloc(cast<Instruction>(BI));

    }
    else if(CallInst* CI = dyn_cast<CallInst>(BI)) {

      if(InlineAttempt* IA = getInlineAttempt(CI)) {

	Start = make_vc(IA->getEntryBlock()->begin(), IA);
	return true;
	    
      }

    }

    ++BI;
    if(BI == BB->end()) {
      
      Start = getSuccessorVC(BB);
      
      if(Start == VCNull)
	return false;
      else if(Start.second != this)
	return true;
      else {
	
	StartI = cast<Instruction>(Start.first);
	BB = StartI->getParent();
	BI = BasicBlock::iterator(StartI);

      }

    }

  }

}

void IntegrationAttempt::tryKillAllAllocs() {

  ValCtx Start = make_vc(F.getEntryBlock().begin(), this);

  while(Start.second->tryKillAllAllocsFrom(Start)) { }

}
