//===-- IntBenefit.cpp ----------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

const uint32_t eliminatedInstructionPoints = 2;
const uint32_t extraInstructionPoints = 1;

static uint32_t intBenefitProgressN = 0;
const uint32_t intBenefitProgressLimit = 1000;

static void intBenefitProgress() {

  intBenefitProgressN++;
  if(intBenefitProgressN == intBenefitProgressLimit) {

    errs() << ".";
    intBenefitProgressN = 0;

  }

}

unsigned IntegrationAttempt::getTotalInstructions() {
  return improvableInstructions;
}

unsigned IntegrationAttempt::getElimdInstructions() {
  return improvedInstructions;
}

int64_t IntegrationAttempt::getTotalInstructionsIncludingLoops() {
  return improvableInstructionsIncludingLoops;
}

// getResidualInstructions: return a best-case residual instruction count, where we assume
// that any code size increase will cause us to opt not to unroll a loop.

int64_t PeelAttempt::getResidualInstructions() {

  if(residualInstructions != -1)
    return residualInstructions;

  int64_t totalInstructions = 0;
  int64_t maxSize = (*(Iterations.begin()))->getTotalInstructionsIncludingLoops();

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {
    
    totalInstructions += (*it)->getResidualInstructions();
    if(totalInstructions > maxSize)
      return maxSize;

  }

  residualInstructions = totalInstructions;
  return totalInstructions;

}

int64_t IntegrationAttempt::getResidualInstructions() {

  if(residualInstructions != -1)
    return residualInstructions;

  // Total excluding explored child loops:
  int64_t totalInstructions = ((int)getTotalInstructions()) - ((int)getElimdInstructions());

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    totalInstructions += it->second->getResidualInstructions();

  }

  residualInstructions = totalInstructions;
  return totalInstructions;

}

// Determine if C is a constant expression that mentions one or more functions.

static void findResidualFunctionsInConst(DenseSet<Function*>& ElimFunctions, Constant* C) {

  if(Function* F = dyn_cast<Function>(C)) {

    ElimFunctions.erase(F);

  }
  else if(ConstantExpr* CE = dyn_cast<ConstantExpr>(C)) {

    for(ConstantExpr::op_iterator it = CE->op_begin(), it2 = CE->op_end(); it != it2; ++it) {

      findResidualFunctionsInConst(ElimFunctions, cast<Constant>(*it));
      
    }

  }

}

// Count instructions likely to be residualised (retained in the specialised program) in this context.
void InlineAttempt::findResidualFunctions(DenseSet<Function*>& ElimFunctions, DenseMap<Function*, unsigned>& TotalResidualInsts) {

  TotalResidualInsts[&F] += getResidualInstructions();
  IntegrationAttempt::findResidualFunctions(ElimFunctions, TotalResidualInsts);

}

void IntegrationAttempt::findResidualFunctions(DenseSet<Function*>& ElimFunctions, DenseMap<Function*, unsigned>& TotalResidualInsts) {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    const ShadowLoopInvar* BBL = BB->invar->outerScope;
    if(L != BBL)
      continue;

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);

      if(inst_is<CallInst>(I) || inst_is<InvokeInst>(I)) {

	Function* F = getCalledFunction(I);
	if(F) {

	  if(getInlineAttempt(I))
	    ElimFunctions.erase(F);

	}
	// Else the caller is unresolved: we'll eliminate all possibly-called functions
	// because they're used in a live instruction somewhere.

      }
      else {

	for(Instruction::op_iterator opit = I->invar->I->op_begin(), opend = I->invar->I->op_end(); opit != opend; ++opit) {

	  if(Constant* C = dyn_cast<Constant>(opit)) {

	    findResidualFunctionsInConst(ElimFunctions, C);
	    
	  }

	}

      }

    }

  }

  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {

    it->second->findResidualFunctions(ElimFunctions, TotalResidualInsts);

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    unsigned iterCount = it->second->Iterations.size();
    for(unsigned i = 0; i < iterCount; ++i) {

      it->second->Iterations[i]->findResidualFunctions(ElimFunctions, TotalResidualInsts);

    }

  }

}

// Determine (roughly) whether it will be profitable to specialise this context.
void PeelAttempt::findProfitableIntegration() {

  if(integrationGoodnessValid)
    return;

  totalIntegrationGoodness = 0;

  for(unsigned i = 0; i < Iterations.size(); ++i) {
    Iterations[i]->findProfitableIntegration();
    totalIntegrationGoodness += Iterations[i]->totalIntegrationGoodness;
  }

  if(totalIntegrationGoodness < 0) {

    // Overall, not profitable to peel this loop.
    setEnabled(false, true);

  }

  integrationGoodnessValid = true;

}

void IntegrationAttempt::findProfitableIntegration() {

  if(integrationGoodnessValid)
    return;

  // Stack of calls leading to a checked read call remains alive no matter what.
  if(containsCheckedReads)
    return;

  totalIntegrationGoodness = 0;
  int64_t childIntegrationGoodness = 0;

  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {

    if(!it->second->isEnabled())
      continue;
    it->second->findProfitableIntegration();
    if(it->second->isEnabled()) {
      totalIntegrationGoodness += it->second->totalIntegrationGoodness;
      childIntegrationGoodness += it->second->totalIntegrationGoodness;
    }

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    if(!it->second->isEnabled())
      continue;
    it->second->findProfitableIntegration();
    if(it->second->isEnabled()) {
      totalIntegrationGoodness += it->second->totalIntegrationGoodness;
      childIntegrationGoodness += it->second->totalIntegrationGoodness;
    }
    
  }

  // OK, calculate own integration goodness:
  // 1. Points for residual instructions introduced:
  int64_t newInstPenalty = extraInstructionPoints * getResidualInstructions();
  totalIntegrationGoodness -= newInstPenalty;

  // 2. Points for instructions which *would* be performed but are eliminated.
  // This differs from the elimdInstructions value in that dead blocks are not counted
  // since they wouldn't get run at all.

  int64_t timeBonus = 0;

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;
   
    const ShadowLoopInvar* BBL = BB->invar->outerScope;
    
    if(L != BBL && ((!L) || L->contains(BBL))) {

      DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator findit = peelChildren.find(immediateChildLoop(L, BBL));

      // Count unexpanded loops as ours:
      if(findit == peelChildren.end() || (!findit->second->isEnabled()) || (!findit->second->isTerminated()))
	BBL = L;

    }

    if(L == BBL) {

      for(uint32_t j = 0; j < BB->insts.size(); ++j) {

	ShadowInstruction* I = &(BB->insts[j]);
	if(willBeReplacedOrDeleted(ShadowValue(I))) {
	  totalIntegrationGoodness += eliminatedInstructionPoints;
	  timeBonus += eliminatedInstructionPoints;
	}

      }

    }

  }

  integrationGoodnessValid = true;

  intBenefitProgress();

  //errs() << getShortHeader() << ": int-goodness " << totalIntegrationGoodness << " (child: " << childIntegrationGoodness << ", codesize: " << newInstPenalty << ", timebonus: " << timeBonus << ")\n";

}

void InlineAttempt::findProfitableIntegration() {

  if(isModel) {

    setEnabled(false, true);
    return;

  }
  else if(isShared()) {

    return;

  }

  IntegrationAttempt::findProfitableIntegration();

  if(totalIntegrationGoodness < 0)
    setEnabled(false, true);

}

// Does this instruction count for accounting / performance measurement? Essentially: can this possibly be improved?
bool llvm::instructionCounts(Instruction* I) {

  if (isa<DbgInfoIntrinsic>(I))
    return false;
  if(BranchInst* BI = dyn_cast<BranchInst>(I))
    if(BI->isUnconditional()) // Don't count unconditional branches as they're already as specified as they're getting
      return false;
  return true;

}

// Count instructions that have been improved (resolved to a constant or similar) in this block.
void IntegrationAttempt::collectBlockStats(ShadowBBInvar* BBI, ShadowBB* BB) {

  uint32_t i = 0;
  
  for(BasicBlock::iterator BI = BBI->BB->begin(), BE = BBI->BB->end(); BI != BE; ++BI, ++i) {
      
    const ShadowLoopInvar* BBL = BBI->naturalScope;
    if(L != BBL && ((!L) || L->contains(BBL))) {

      // Count unexplored loops as part of my own context.
      if(!peelChildren.count(immediateChildLoop(L, BBL)))
	BBL = L;

    }

    if(BBL != L) {

      if(instructionCounts(&*BI))
	improvableInstructionsIncludingLoops++;

    }
    else {

      if(instructionCounts(&*BI)) { 

	//if(BB == getEntryBlock() && isa<PHINode>(BI))
	//  continue;

	improvableInstructions++;
	improvableInstructionsIncludingLoops++;

	if(!BB)
	  improvedInstructions++;
	else if(hasConstReplacement(&(BB->insts[i])))
	  improvedInstructions++;
	else if(BB->insts[i].dieStatus != INSTSTATUS_ALIVE)
	  improvedInstructions++;

      }

    }

  }

  if(BB) {

    bool deadEdgeFound = false;
    for(uint32_t i = 0; i < BBI->succIdxs.size(); ++i) {
      
      if(!BB->succsAlive[i])
	deadEdgeFound = true;

    }

    if(deadEdgeFound) {

      // Elim of branch:
      improvedInstructions++;

    }

  }

}

void IntegrationAttempt::collectLoopStats(const ShadowLoopInvar* LoopI) {

  DenseMap<const ShadowLoopInvar*, PeelAttempt*>::const_iterator it = peelChildren.find(LoopI);

  if(it == peelChildren.end()) {

    for(uint32_t i = LoopI->headerIdx; i < invarInfo->BBs.size(); ++i) {
      ShadowBBInvar* BBI = getBBInvar(i);
      if(!LoopI->contains(BBI->naturalScope))
	break;
      ShadowBB* BB = getBB(*BBI);
      collectBlockStats(BBI, BB);
    }

  }

}

void IntegrationAttempt::collectAllBlockStats() {

  for(uint32_t i = 0; i < nBBs; ++i) {
    collectBlockStats(&(invarInfo->BBs[i + BBsOffset]), BBs[i]);
  }

}

void InlineAttempt::collectAllLoopStats() {

  for(SmallVector<ShadowLoopInvar*, 4>::const_iterator LoopI = invarInfo->TopLevelLoops.begin(), 
	LoopE = invarInfo->TopLevelLoops.end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelIteration::collectAllLoopStats() {

  for(SmallVector<ShadowLoopInvar*, 1>::const_iterator LoopI = L->childLoops.begin(), 
	LoopE = L->childLoops.end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelAttempt::collectStats() {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->collectStats();

}

void IntegrationAttempt::collectStats() {

  improvedInstructions = 0;
  improvableInstructions = 0;
  improvableInstructionsIncludingLoops = 0;

  collectAllBlockStats();
  collectAllLoopStats();

  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {
    if(!it->second->isCommitted())
      it->second->collectStats();
  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it)
    it->second->collectStats();

}
