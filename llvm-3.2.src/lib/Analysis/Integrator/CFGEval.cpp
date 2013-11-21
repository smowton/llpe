
#define DEBUG_TYPE "hypotheticalconstantfolder"

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/BasicBlock.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h" // For isIdentifiedObject
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
// For elaboration of Calculate et al in Dominators.h:
#include "llvm/Analysis/DominatorInternals.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Assembly/Writer.h"

using namespace llvm;

// Implement instruction/block analysis concerning control flow, i.e. determining a block's
// status and relatedly analysing terminator instructions.

void IntegrationAttempt::setBlockStatus(ShadowBBInvar* BBI, ShadowBBStatus s) {

  ShadowBB* BB = getOrCreateBB(BBI);
  BB->status = s;
    
}

bool InlineAttempt::entryBlockIsCertain() {

  if(Callers.empty())
    return true;
  release_assert(!isShared());
  return blockCertainlyExecutes(Callers[0]->parent);

}

bool PeelIteration::entryBlockIsCertain() {

  if(iterationCount == 0)
    return blockCertainlyExecutes(parent->getBB(parentPA->invarInfo->preheaderIdx));

  // Otherwise it's certain if we're certain to iterate and at least the previous header was certain.
  PeelIteration* prevIter = parentPA->Iterations[iterationCount - 1];
  return blockCertainlyExecutes(prevIter->getBB(parentPA->invarInfo->latchIdx)) && prevIter->allExitEdgesDead();

}

bool InlineAttempt::entryBlockAssumed() {

  if(Callers.empty())
    return true;

  release_assert(!isShared());

  if(blockAssumedToExecute(Callers[0]->parent))
    return true;
  if(pass->shouldAlwaysExplore(&F))
    return true;

  return false;

}

bool PeelIteration::entryBlockAssumed() {

  // Having been entered at all currently signifies at least the assumption that we will run.
  return true;

}

bool IntegrationAttempt::createEntryBlock() {

  if(BBs[0])
    return false;

  ShadowBBStatus newStatus = BBSTATUS_UNKNOWN;

  if(entryBlockIsCertain())
    newStatus = BBSTATUS_CERTAIN;
  else if(entryBlockAssumed())
    newStatus = BBSTATUS_ASSUMED;

  setBlockStatus(getBBInvar(BBsOffset), newStatus);

  return true;

}

// Returns changed.
static bool setEdgeAlive(TerminatorInst* TI, ShadowBB* BB, BasicBlock* Target) {

  const unsigned NumSucc = TI->getNumSuccessors();
  bool changed = false;

  for (unsigned I = 0; I != NumSucc; ++I) {

    BasicBlock* thisTarget = TI->getSuccessor(I);

    if(thisTarget == Target) {

      // Mark this edge alive
      if(!BB->succsAlive[I])
	changed = true;
      BB->succsAlive[I] = true;

    }

  }

  return changed;

}

// Return true on change.
bool IntegrationAttempt::tryEvaluateTerminatorInst(ShadowInstruction* SI) {

  if (!(inst_is<BranchInst>(SI) || inst_is<SwitchInst>(SI))) {
    
    return false;

  }

  if(BranchInst* BI = dyn_cast_inst<BranchInst>(SI)) {
    if(BI->isUnconditional()) {
      bool changed = !SI->parent->succsAlive[0];
      SI->parent->succsAlive[0] = true;
      return changed;
    }
  }

  // Both switches and conditional branches use operand 0 for the condition.
  ShadowValue Condition = SI->getOperand(0);
      
  bool changed = false;
  
  ConstantInt* ConstCondition = dyn_cast_or_null<ConstantInt>(getConstReplacement(Condition));
  if(!ConstCondition) {

    if(Condition.t == SHADOWVAL_INST || Condition.t == SHADOWVAL_ARG) {

      // Switch statements can operate on a ptrtoint operand, of which only ptrtoint(null) is useful:
      if(ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(Condition))) {
	
	if(IVS->onlyContainsNulls()) {
	  
	  ConstCondition = cast<ConstantInt>(Constant::getNullValue(SI->invar->I->getOperand(0)->getType()));
	  
	}

      }

    }

  }

  if(!ConstCondition) {
    
    std::pair<ValSetType, ImprovedVal> PathVal;

    if(tryGetPathValue(Condition, SI->parent, PathVal))
      ConstCondition = dyn_cast_val<ConstantInt>(PathVal.second.V);

  }

  TerminatorInst* TI = cast_inst<TerminatorInst>(SI);
  const unsigned NumSucc = TI->getNumSuccessors();

  if(ConstCondition) {

    BasicBlock* takenTarget = 0;

    if(BranchInst* BI = dyn_cast_inst<BranchInst>(SI)) {
      // This ought to be a boolean.
      if(ConstCondition->isZero())
	takenTarget = BI->getSuccessor(1);
      else
	takenTarget = BI->getSuccessor(0);
    }
    else {
      SwitchInst* SwI = cast_inst<SwitchInst>(SI);
      SwitchInst::CaseIt targetidx = SwI->findCaseValue(ConstCondition);
      takenTarget = targetidx.getCaseSuccessor();
    }
    if(takenTarget) {
      // We know where the instruction is going -- remove this block as a predecessor for its other targets.
      LPDEBUG("Branch or switch instruction given known target: " << takenTarget->getName() << "\n");

      return setEdgeAlive(TI, SI->parent, takenTarget);

    }
    
    // Else fall through to set all alive.

  }

  SwitchInst* Switch;
  ImprovedValSetSingle* IVS;

  if((Switch = dyn_cast_inst<SwitchInst>(SI)) && 
     (IVS = dyn_cast<ImprovedValSetSingle>(getIVSRef(Condition))) && 
     IVS->SetType == ValSetTypeScalar && 
     !IVS->Values.empty()) {

    // A set of values feeding a switch. Set each corresponding edge alive.

    bool changed = false;

    for (unsigned i = 0, ilim = IVS->Values.size(); i != ilim; ++i) {

      SwitchInst::CaseIt targetit = Switch->findCaseValue(cast<ConstantInt>(IVS->Values[i].V.getVal()));
      BasicBlock* target = targetit.getCaseSuccessor();
      changed |= setEdgeAlive(TI, SI->parent, target);

    }

    return changed;

  }

  // Condition unknown -- set all successors alive.
  for (unsigned I = 0; I != NumSucc; ++I) {
    
    // Mark outgoing edge alive
    if(!SI->parent->succsAlive[I])
      changed = true;
    SI->parent->succsAlive[I] = true;
    
  }

  return changed;

}

IntegrationAttempt* IntegrationAttempt::getIAForScope(const Loop* Scope) {

  if((!L) || L->contains(Scope))
    return this;

  return getIAForScopeFalling(Scope);

}

IntegrationAttempt* PeelIteration::getIAForScopeFalling(const Loop* Scope) {

  if(L == Scope)
    return this;
  return parent->getIAForScopeFalling(Scope);

}

IntegrationAttempt* InlineAttempt::getIAForScopeFalling(const Loop* Scope) {

  release_assert((!Scope) && "Scope not found (getIAForScopeFalling)");
  return this;

}

// Return true if the result changes:
bool IntegrationAttempt::tryEvaluateTerminator(ShadowInstruction* SI, bool thisBlockLoadedVararg) {

  // Clarify branch target if possible:
  bool anyChange = tryEvaluateTerminatorInst(SI);

  // Return instruction breaks early to avoid the refcount juggling below:
  // a live return always has one successor, the call-merge.
  if(inst_is<ReturnInst>(SI)) {
    // Drop local allocas from the store:
    if(invarInfo->frameSize != -1)
      SI->parent->popStackFrame();
    return false;
  }

  ShadowBB* BB = SI->parent;
  ShadowBBInvar* BBI = BB->invar;

  for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {

    if(!BB->succsAlive[i])
      continue;

    if(shouldIgnoreEdge(BB->invar, getBBInvar(BB->invar->succIdxs[i]))) {
      if(anyChange)
	getFunctionRoot()->markBlockAndSuccsFailed(BB->invar->succIdxs[i], 0);
      continue;
    }

    // Create a store reference for each live successor
    ++SI->parent->localStore->refCount;

    // And similarly count the edge towards determining block certainty:
    ++pendingEdges;

  }

  //errs() << "Leaving block " << SI->parent->invar->BB->getParent()->getName() << "/" << SI->parent->invar->BB->getName() << " with store " << SI->parent->localStore << " refcount " << SI->parent->localStore->refCount << "\n";

  // This block relinquishes its reference. Might free the store in e.g. an unreachable block.
  SI->parent->localStore->dropReference();

  uint32_t uniqueSucc = 0xffffffff;

  for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {
    
    if(!BB->succsAlive[i])
      continue;

    if(uniqueSucc == BBI->succIdxs[i] || uniqueSucc == 0xffffffff)
      uniqueSucc = BBI->succIdxs[i];
    else {
      uniqueSucc = 0xffffffff;
      break;
    }

  }

  if(!anyChange)
    return false;

  for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {

    if(!BB->succsAlive[i])
      continue;

    ShadowBBInvar* SBBI = getBBInvar(BB->invar->succIdxs[i]);

    if(shouldIgnoreEdge(BB->invar, SBBI))
      continue;

    IntegrationAttempt* IA = getIAForScope(SBBI->naturalScope);

    if(!IA->getBB(BB->invar->succIdxs[i])) {

      // Can grant the new block some status if either (a) I have status and this is my only live successor,
      // or (b) this edge should be assumed.
      // In practice this is mainly useful conferring ASSUMED status; certainty is detected mainly
      // using checkBlockStatus, below.

      ShadowBBStatus newStatus = BBSTATUS_UNKNOWN;
      
      if(BB->status != BBSTATUS_UNKNOWN && uniqueSucc != 0xffffffff)
	newStatus = BB->status;
      else if(shouldAssumeEdge(BBI->BB, SBBI->BB))
	newStatus = BBSTATUS_ASSUMED;

      ShadowBBInvar* SBB = getBBInvar(BB->invar->succIdxs[i]);
      IA->setBlockStatus(SBB, newStatus);

    }
    
    IA->getBB(BB->invar->succIdxs[i])->useSpecialVarargMerge = thisBlockLoadedVararg;

  }

  return true;

}

void IntegrationAttempt::checkBlockStatus(ShadowBB* BB, bool inLoopAnalyser) {

  for(uint32_t i = 0, ilim = BB->invar->predIdxs.size(); i != ilim; ++i) {

    ShadowBBInvar* predBBI = getBBInvar(BB->invar->predIdxs[i]);

    if(edgeIsDead(predBBI, BB->invar))
      continue;

    if(shouldIgnoreEdge(predBBI, BB->invar))
      continue;
      
    release_assert(pendingEdges != 0 && "pendingEdges falling below zero");
    --pendingEdges;
      
  }

  if(pendingEdges == 0) {

    if(!inLoopAnalyser)
      BB->status = BBs[0]->status;

  }

}
