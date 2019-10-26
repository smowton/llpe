//===-- CFGEval.cpp -------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "CFGEval"

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/AliasAnalysis.h" // For isIdentifiedObject
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

// Implement instruction/block analysis concerning control flow, i.e. determining a block's
// status and relatedly analysing terminator instructions.

// Return true if, when LLPE's specialisation assumptions hold, this function is certain
// to be entered.
bool InlineAttempt::entryBlockIsCertain() {

  if(Callers.empty())
    return true;
  release_assert(!isShared());
  return Callers[0]->parent->isMarkedCertain();

}

// Return true if, when LLPE's specialisation assumptions hold, this loop iteration is certain
// to be entered.
bool PeelIteration::entryBlockIsCertain() {

  if(iterationCount == 0)
    return parent->getBB(parentPA->L->preheaderIdx)->isMarkedCertain();

  // Otherwise it's certain if we're certain to iterate and at least the previous header was certain.
  PeelIteration* prevIter = parentPA->Iterations[iterationCount - 1];
  return prevIter->getBB(parentPA->L->latchIdx)->isMarkedCertain() && prevIter->allExitEdgesDead();

}

// Return true if the user has instructed we should explore this function aggressively, using the same
// rules as for code that is certainly reachable.
bool InlineAttempt::entryBlockAssumed() {

  // The specialisation root is certainly entered
  if(Callers.empty())
    return true;

  release_assert(!isShared());

  if(Callers[0]->parent->isMarkedCertainOrAssumed())
    return true;

  // Nominated by the user?
  if(pass->shouldAlwaysExplore(&F))
    return true;

  return false;

}

// Return true if the user has instructed we should explore this loop iteration aggressively, using the same
// rules as for code that is certainly reachable.
bool PeelIteration::entryBlockAssumed() {
    
  // A PeelIteration object being created at all indicates at least the assumption that we will run.
  return true;

}

// Create the entry block (function entry point or loop header) and set it certain or assumed-reachable
// if appropriate. Return true if the block was created or its status changed.
bool IntegrationAttempt::createEntryBlock() {

  // Block already created? Header status cannot change after creation.
  if(BBs[0])
    return false;

  ShadowBBStatus newStatus = BBSTATUS_UNKNOWN;

  if(entryBlockIsCertain())
    newStatus = BBSTATUS_CERTAIN;
  else if(entryBlockAssumed())
    newStatus = BBSTATUS_ASSUMED;

  ShadowBB* BB = getOrCreateBB(getBBInvar(BBsOffset));
  BB->status = newStatus;

  return true;

}

// Set edge from block-instance BB with terminator TI to Target alive. Return true
// if the edge status changed (i.e. it was not already marked alive)
static bool setEdgeAlive(Instruction* TI, ShadowBB* BB, BasicBlock* Target) {

  const unsigned NumSucc = TI->getNumSuccessors();
  bool changed = false;

  for (unsigned I = 0; I != NumSucc; ++I) {

    BasicBlock* thisTarget = TI->getSuccessor(I);

    if(thisTarget == Target) {

      // Mark this edge alive. In some cases there may be multiple copies of the edge
      // e.g. for several switch cases with the same destination.
      if(!BB->succsAlive[I])
	changed = true;
      BB->succsAlive[I] = true;

    }

  }

  return changed;

}

// Is BB1I -> BB2I known to be infeasible in this context?
bool IntegrationAttempt::edgeIsDead(ShadowBBInvar* BB1I, ShadowBBInvar* BB2I) {

  bool BB1InScope;

  if(ShadowBB* BB1 = getBB(BB1I->idx, &BB1InScope)) {

    return BB1->edgeIsDead(BB2I);

  }
  else if(BB1InScope) {

    // Source block doesn't exist despite being in scope, edge must be dead.
    return true;

  }

  return false;

}

// Is BB1I -> BB2I known to be infeasible in this context and all child loop contexts?
bool IntegrationAttempt::edgeIsDeadRising(ShadowBBInvar& BB1I, ShadowBBInvar& BB2I, bool ignoreThisScope) {

  if((!ignoreThisScope) && edgeIsDead(&BB1I, &BB2I))
    return true;

  if(BB1I.naturalScope == L)
    return false;
  
  if(PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(L, BB1I.naturalScope))) {

    if(LPA->isTerminated()) {

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i) {
	  
	if(!LPA->Iterations[i]->edgeIsDeadRising(BB1I, BB2I))
	  return false;
	
      }

      return true;

    }

  }
    
  return false;

}

// Is BBI known to be unreachable in this and all child loop contexts?
bool IntegrationAttempt::blockIsDeadRising(ShadowBBInvar& BBI) {

  if(getBB(BBI))
    return false;

  if(BBI.naturalScope == L)
    return true;

  if(PeelAttempt* LPA = getPeelAttempt(immediateChildLoop(L, BBI.naturalScope))) {

    if(LPA->isTerminated()) {

      for(unsigned i = 0; i < LPA->Iterations.size(); ++i) {
	  
	if(!LPA->Iterations[i]->blockIsDeadRising(BBI))
	  return false;
	
      }

      return true;

    }

  }

  return true;

}

// Set outgoing edges alive dependent on the terminator instruction SI.
// If the terminator is an Invoke instruction, the call has already been run.
// Return true if anything changed.
bool IntegrationAttempt::checkBlockOutgoingEdges(ShadowInstruction* SI) {

  // TOCHECK: I think this only returns false if the block ends with an Unreachable inst?
  switch(SI->invar->I->getOpcode()) {
  case Instruction::Br:
  case Instruction::Switch:
  case Instruction::Invoke:
  case Instruction::Resume:
    break;
  default:
    return false;
  }

  if(inst_is<InvokeInst>(SI)) {

    InlineAttempt* IA = getInlineAttempt(SI);

    bool changed = false;

    // !localStore indicates the invoke instruction doesn't return normally
    if(SI->parent->localStore) {

      changed |= !SI->parent->succsAlive[0];
      SI->parent->succsAlive[0] = true;

    }      

    // I mark the exceptional edge reachable here if the call is disabled, even though
    // we might have proved it isn't feasible. This could be improved by converting the
    // invoke into a call in the final program.
    if((!IA) || (!IA->isEnabled()) || IA->mayUnwind) {

      changed |= !SI->parent->succsAlive[1];
      SI->parent->succsAlive[1] = true;

    }

    return changed;
    
  }
  else if(inst_is<ResumeInst>(SI)) {

    bool changed = !mayUnwind;
    mayUnwind = true;
    return changed;

  }
  else if(BranchInst* BI = dyn_cast_inst<BranchInst>(SI)) {

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

  const unsigned NumSucc = SI->getNumSuccessors();

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
      takenTarget = targetidx->getCaseSuccessor();
    }
    if(takenTarget) {
      // We know where the instruction is going -- remove this block as a predecessor for its other targets.
      LPDEBUG("Branch or switch instruction given known target: " << takenTarget->getName() << "\n");

      return setEdgeAlive(SI->getInstruction(), SI->parent, takenTarget);

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
      
      SwitchInst::CaseIt targetit = Switch->findCaseValue(cast<ConstantInt>(getConstReplacement(IVS->Values[i].V)));
      BasicBlock* target = targetit->getCaseSuccessor();
      changed |= setEdgeAlive(SI->getInstruction(), SI->parent, target);

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

// Evaluate the block terminator instruction SI to determine feasible successors, and juggle
// store reference counts to give a reference to each live successor and drop this block's
// reference. If the terminator is an Invoke the call has already been explored if appropriate.
// Returns true if anything changed.
bool IntegrationAttempt::tryEvaluateTerminator(ShadowInstruction* SI, bool thisBlockLoadedVararg) {

  // Clarify branch target if possible:
  bool anyChange = checkBlockOutgoingEdges(SI);

  // Return instruction breaks early to avoid the refcount juggling below:
  // a live return always has one successor, the call-merge.
  if(inst_is<ReturnInst>(SI)) {

    // Drop local allocas from the store:
    if(invarInfo->frameSize != -1) {

      SI->parent->popStackFrame();
      if(SI->parent->tlStore) {
	SI->parent->tlStore = SI->parent->tlStore->getWritableFrameList();
	SI->parent->tlStore->popStackFrame();
      }
      if(SI->parent->dseStore) {
	SI->parent->dseStore = SI->parent->dseStore->getWritableFrameList();
	SI->parent->dseStore->popStackFrame();
      }

    }
    
    return false;
  }

  ShadowBB* BB = SI->parent;
  ShadowBBInvar* BBI = BB->invar;

  for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {

    if(!BB->succsAlive[i])
      continue;

    if(edgeBranchesToUnspecialisedCode(BB->invar, getBBInvar(BB->invar->succIdxs[i]))) {
      if(anyChange)
	getFunctionRoot()->markBlockAndSuccsReachableUnspecialised(BB->invar->succIdxs[i], 0);
      continue;
    }

    // Create a store reference for each live successor
    SI->parent->refStores();

    // And similarly count the edge towards determining block certainty:
    ++pendingEdges;

  }

  //errs() << "Leaving block " << SI->parent->invar->BB->getParent()->getName() << "/" << SI->parent->invar->BB->getName() << " with store " << SI->parent->localStore << " refcount " << SI->parent->localStore->refCount << "\n";

  // This block relinquishes its reference. Might free the store in e.g. an unreachable block.
  
  if(SI->parent->localStore)
    SI->parent->derefStores();

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

    if(edgeBranchesToUnspecialisedCode(BB->invar, SBBI))
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
      
      ShadowBB* BB = IA->getOrCreateBB(SBB);
      BB->status = newStatus;

    }
    
    IA->getBB(BB->invar->succIdxs[i])->useSpecialVarargMerge = thisBlockLoadedVararg;

  }

  return true;

}

// Check if this block post-dominates the context entry block (that is, if the
// context is entered, this block will definitely be reached). If it does, and the
// entry block is certainly- or assumed-reachable, inherit its status.
// Note this is distinct from LLVM's post-dominator analysis because it takes
// edges proved dead during partial evaluation into account. It also depends on
// visiting blocks in topological order.
void IntegrationAttempt::checkBlockStatus(ShadowBB* BB, bool inLoopAnalyser) {

  for(uint32_t i = 0, ilim = BB->invar->predIdxs.size(); i != ilim; ++i) {

    ShadowBBInvar* predBBI = getBBInvar(BB->invar->predIdxs[i]);

    if(edgeIsDead(predBBI, BB->invar))
      continue;

    if(edgeBranchesToUnspecialisedCode(predBBI, BB->invar))
      continue;
      
    release_assert(pendingEdges != 0 && "pendingEdges falling below zero");
    --pendingEdges;
      
  }

  if(pendingEdges == 0) {

    if(!inLoopAnalyser)
      BB->status = BBs[0]->status;

  }

}

