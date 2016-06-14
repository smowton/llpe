//===- NewStats.cpp -------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

// This file contains code to quantify the benefits achieved by specialisation.

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Function.h"

using namespace llvm;

// Count stats for this function context.
void InlineAttempt::preCommitStats(bool enabledHere) {

  // Count function contexts:
  ++GlobalIHP->stats.dynamicFunctions;
  IntegrationAttempt::preCommitStats(enabledHere);

}

static bool isHeapPointer(ShadowValue V) {

  ShadowValue Base;
  return (getBaseObject(V, Base) && Base.isPtrIdx() && Base.getFrameNo() == -1);

}

// Count stats for this function or loop context.
void IntegrationAttempt::preCommitStats(bool enabledHere) {

  if(isCommitted())
    return;

  // Count contexts:
  ++GlobalIHP->stats.dynamicContexts;
  if(!enabledHere)
    ++GlobalIHP->stats.disabledContexts;

  for(uint32_t i = 0; i < nBBs; ++i) {

    if(!BBs[i])
      continue;

    // Count live blocks
    ++GlobalIHP->stats.dynamicBlocks;
    // Count total instructions in live blocks.
    GlobalIHP->stats.dynamicInsts += BBs[i]->insts.size();
    
    if(!enabledHere)
      continue;

    // Count synthesised checks:
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

	// Count branches straightened by specialisation.
	BranchInst* BI;
	if(hasUniqueSucc && ((!(BI = dyn_cast_inst<BranchInst>(&SI))) || BI->isConditional()))
	  ++GlobalIHP->stats.resolvedBranches;

      }
      else {

	ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(SI.i.PB);
	if(IVS && IVS->Values.size() == 1) {

	  // Count instructions successfully resolved to a constant or known symbolic pointer.
	  if(IVS->SetType == ValSetTypeScalar)
	    ++GlobalIHP->stats.constantInstructions;
	  else if(IVS->SetType == ValSetTypePB)
	    ++GlobalIHP->stats.pointerInstructions;

	}
	else if(IVS && !IVS->isWhollyUnknown()) {

	  // Count instructions with some concrete information but nontheless residualised.
	  // These are assigned a set of possible values during specialisation.
	  ++GlobalIHP->stats.setInstructions;

	}
	else {

	  // Count instructions about which we have no information during specialisation.
	  ++GlobalIHP->stats.unknownInstructions;

	}

	// Count instructions proved un-needed during specialisation, e.g. stores
	// whose corresponding loads have been resolved.
	if(SI.dieStatus)
	  ++GlobalIHP->stats.deadInstructions;

	// Count memory-reading instructions whose results must be checked against interference
	// by concurrent threads.
	if(SI.readsMemoryDirectly()) {
	  if(SI.isThreadLocal == TLS_MUSTCHECK)
	    ++GlobalIHP->stats.threadChecks;
	}

	// Count instructions that need I/O-related checks, either bytewise (memcmp) or using the file-watcher daemon.
	if(SI.needsRuntimeCheck == RUNTIME_CHECK_READ_MEMCMP || SI.needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD)
	  ++GlobalIHP->stats.fileChecks;

	if(SI.needsRuntimeCheck == RUNTIME_CHECK_AS_EXPECTED) {

	  // Count malloc-not-null and user-specified runtime checks.
	  if(inst_is<ICmpInst>(&SI) && (isHeapPointer(SI.getOperand(0)) || isHeapPointer(SI.getOperand(1))))
	    ++GlobalIHP->stats.mallocChecks;
	  else
	    ++GlobalIHP->stats.condChecks;

	}

      }

    }

  }

  // Accumulate stats for our child calls:
  for(IAIterator it = child_calls_begin(this), itend = child_calls_end(this); it != itend; ++it) {
    
    it->second->preCommitStats(enabledHere && it->second->isEnabled());

  }

  // Accumulate stats for our child loops:
  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    bool enabled = enabledHere && it->second->isTerminated() && it->second->isEnabled();

    // If the loop wasn't known-terminated we would have analysed and committed a general
    // iteration, which is part of this context not a child.
    for(uint32_t i = 0, ilim = it->second->Iterations.size(); i != ilim; ++i)
      it->second->Iterations[i]->preCommitStats(enabled);

  }

}

// Count how many instructions we ended up actually emitting, including
// those that realise checks and so on.
void LLPEAnalysisPass::postCommitStats() {

  for(SmallVector<Function*, 4>::iterator it = commitFunctions.begin(),
	itend = commitFunctions.end(); it != itend; ++it) {
  
    Function* F = *it;
    for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

      BasicBlock* BB = &*FI;
      ++GlobalIHP->stats.residualBlocks;
      GlobalIHP->stats.residualInstructions += BB->size();

    }
    
  }

}
