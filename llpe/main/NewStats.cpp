//===- NewStats.cpp -------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Function.h"

using namespace llvm;

void InlineAttempt::preCommitStats(bool enabledHere) {

  ++GlobalIHP->stats.dynamicFunctions;
  IntegrationAttempt::preCommitStats(enabledHere);

}

static bool isHeapPointer(ShadowValue V) {

  ShadowValue Base;
  return (getBaseObject(V, Base) && Base.isPtrIdx() && Base.getFrameNo() == -1);

}

void IntegrationAttempt::preCommitStats(bool enabledHere) {

  if(isCommitted())
    return;

  ++GlobalIHP->stats.dynamicContexts;
  if(!enabledHere)
    ++GlobalIHP->stats.disabledContexts;

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(!BBs[i])
      continue;

    ++GlobalIHP->stats.dynamicBlocks;
    GlobalIHP->stats.dynamicInsts += BBs[i]->insts.size();
    
    if(!enabledHere)
      continue;

    GlobalIHP->stats.condChecks += GlobalIHP->countPathConditionsAtBlockStart(BBs[i]->invar, this);

    bool hasUniqueSucc = false;
    for(uint32_t j = 0, jlim = BBs[i]->invar->succIdxs.size(); j != jlim; ++j) {

      if(BBs[i]->succsAlive[j]) {
	
	if(hasUniqueSucc) {
	
	  hasUniqueSucc = false;
	  break;

	}
	else {

	  hasUniqueSucc = true;

	}

      }

    }
    
    for(uint32_t j = 0, jlim = BBs[i]->insts.size(); j != jlim; ++j) {

      ShadowInstruction& SI = BBs[i]->insts[j];

      if(j + 1 == jlim) {
	
	BranchInst* BI;
	if(hasUniqueSucc && ((!(BI = dyn_cast_inst<BranchInst>(&SI))) || BI->isConditional()))
	  ++GlobalIHP->stats.resolvedBranches;

      }
      else {

	ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(SI.i.PB);
	if(IVS && IVS->Values.size() == 1) {

	  if(IVS->SetType == ValSetTypeScalar)
	    ++GlobalIHP->stats.constantInstructions;
	  else if(IVS->SetType == ValSetTypePB)
	    ++GlobalIHP->stats.pointerInstructions;

	}
	else if(IVS && !IVS->isWhollyUnknown()) {

	  ++GlobalIHP->stats.setInstructions;

	}
	else {

	  ++GlobalIHP->stats.unknownInstructions;

	}

	if(SI.dieStatus)
	  ++GlobalIHP->stats.deadInstructions;

	if(SI.readsMemoryDirectly()) {
	  if(SI.isThreadLocal == TLS_MUSTCHECK)
	    ++GlobalIHP->stats.threadChecks;
	}

	if(SI.needsRuntimeCheck == RUNTIME_CHECK_READ_MEMCMP || SI.needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD)
	  ++GlobalIHP->stats.fileChecks;

	if(SI.needsRuntimeCheck == RUNTIME_CHECK_AS_EXPECTED) {

	  if(inst_is<ICmpInst>(&SI) && (isHeapPointer(SI.getOperand(0)) || isHeapPointer(SI.getOperand(1))))
	    ++GlobalIHP->stats.mallocChecks;
	  else
	    ++GlobalIHP->stats.condChecks;

	}

      }

    }

  }

  for(IAIterator it = child_calls_begin(this), itend = child_calls_end(this); it != itend; ++it) {
    
    it->second->preCommitStats(enabledHere && it->second->isEnabled());

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    bool enabled = enabledHere && it->second->isTerminated() && it->second->isEnabled();

    for(uint32_t i = 0, ilim = it->second->Iterations.size(); i != ilim; ++i)
      it->second->Iterations[i]->preCommitStats(enabled);

  }

}

void LLPEAnalysisPass::postCommitStats() {

  for(SmallVector<Function*, 4>::iterator it = commitFunctions.begin(),
	itend = commitFunctions.end(); it != itend; ++it) {
  
    Function* F = *it;
    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

      BasicBlock* BB = FI;
      ++GlobalIHP->stats.residualBlocks;
      GlobalIHP->stats.residualInstructions += BB->size();

    }
    
  }

}
