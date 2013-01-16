
#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Constants.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

const uint32_t eliminatedInstructionPoints = 2;
const uint32_t extraInstructionPoints = 1;

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
  int64_t totalInstructions = getTotalInstructions() - getElimdInstructions();

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    totalInstructions += it->second->getResidualInstructions();

  }

  residualInstructions = totalInstructions;
  return totalInstructions;

}

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

void InlineAttempt::findResidualFunctions(DenseSet<Function*>& ElimFunctions, DenseMap<Function*, unsigned>& TotalResidualInsts) {

  TotalResidualInsts[&F] += getResidualInstructions();
  IntegrationAttempt::findResidualFunctions(ElimFunctions, TotalResidualInsts);

}

void IntegrationAttempt::findResidualFunctions(DenseSet<Function*>& ElimFunctions, DenseMap<Function*, unsigned>& TotalResidualInsts) {

  const Loop* MyL = getLoopContext();

  for(Function::iterator BI = F.begin(), BE = F.end(); BI != BE; ++BI) {

    BasicBlock* BB = BI;

    if(blockIsDead(BB))
      continue;

    const Loop* BBL = getBlockScopeVariant(BB);
    if(MyL != BBL)
      continue;

    for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II) {

      if(CallInst* CI = dyn_cast<CallInst>(II)) {

	Function* F = getCalledFunction(CI);
	if(F) {

	  if(!inlineChildren.count(CI))
	    ElimFunctions.erase(F);

	}
	// Else the caller is unresolved: we'll eliminate all possibly-called functions
	// because they're used in a live instruction somewhere.

      }
      else {

	for(Instruction::op_iterator opit = II->op_begin(), opend = II->op_end(); opit != opend; ++opit) {

	  if(Constant* C = dyn_cast<Constant>(opit)) {

	    findResidualFunctionsInConst(ElimFunctions, C);

	  }

	}

      }

    }

  }

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->findResidualFunctions(ElimFunctions, TotalResidualInsts);

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    unsigned iterCount = it->second->Iterations.size();
    for(unsigned i = 0; i < iterCount; ++i) {

      it->second->Iterations[i]->findResidualFunctions(ElimFunctions, TotalResidualInsts);

    }

  }

}

void PeelAttempt::findProfitableIntegration(DenseMap<Function*, unsigned>& nonInliningPenalty) {

  totalIntegrationGoodness = 0;
  int64_t itersGoodness = 0;

  for(unsigned i = 0; i < Iterations.size(); ++i) {
    Iterations[i]->findProfitableIntegration(nonInliningPenalty);
    itersGoodness += Iterations[i]->totalIntegrationGoodness;
  }

  // This figure already includes penalties for forcing functions to stay alive.
  // One possible argument against now is that we might bring loads of outside
  // instructions to life by not unrolling:
  
  int64_t daeBonus = extraInstructionPoints * parent->disablePeel(L, true);
  daeBonus += (extraInstructionPoints * nDependentLoads);

  // Another possible argument: a non-terminated loop will necessarily retain a whole copy of the loop
  // (i.e. will definitely increase code size).

  int64_t nonTermPenalty = 0;

  if(Iterations.back()->iterStatus != IterationStatusFinal) {

    for(std::vector<BasicBlock*>::iterator it = LoopBlocks.begin(), it2 = LoopBlocks.end(); it != it2; ++it) {

      nonTermPenalty += (extraInstructionPoints * (*it)->size());

    }

  }

  totalIntegrationGoodness = itersGoodness + daeBonus - nonTermPenalty;

  errs() << getShortHeader() << ": goodness " << totalIntegrationGoodness << " (dae bonus: " << daeBonus << ", nonterm penalty: " << nonTermPenalty << ", iters total: " << itersGoodness << ")\n";

  if(totalIntegrationGoodness < 0) {

    // Overall, not profitable to peel this loop.
    parent->disablePeel(L, false);

    // Decided to fold this context: deduct the penalty from parent contexts.
    parent->reduceDependentLoads(nDependentLoads);

  }

}

void PeelAttempt::reduceDependentLoads(int64_t nLoads) {

  nDependentLoads -= nLoads;
  parent->reduceDependentLoads(nLoads);

}

void InlineAttempt::reduceDependentLoads(int64_t nLoads) {

  nDependentLoads -= nLoads;
  if(parent)
    parent->reduceDependentLoads(nLoads);

}

void PeelIteration::reduceDependentLoads(int64_t nLoads) {

  nDependentLoads -= nLoads;
  parentPA->reduceDependentLoads(nLoads);

}

void IntegrationAttempt::findProfitableIntegration(DenseMap<Function*, unsigned>& nonInliningPenalty) {

  totalIntegrationGoodness = 0;
  int64_t childIntegrationGoodness = 0;

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if(!it->second->isEnabled())
      continue;
    it->second->findProfitableIntegration(nonInliningPenalty);
    if(it->second->isEnabled()) {
      totalIntegrationGoodness += it->second->totalIntegrationGoodness;
      childIntegrationGoodness += it->second->totalIntegrationGoodness;
    }

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    if(!it->second->isEnabled())
      continue;
    it->second->findProfitableIntegration(nonInliningPenalty);
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

  const Loop* MyL = getLoopContext();

  int64_t timeBonus = 0;

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    if(blockIsDead(FI))
      continue;
   
    const Loop* BBL = getBlockScopeVariant(FI);
    
    if(MyL != BBL && ((!MyL) || MyL->contains(BBL))) {

      // Count unexpanded loops as ours:
      if(!peelChildren.count(immediateChildLoop(MyL, BBL)))
	BBL = MyL;
      else if(!peelChildren[immediateChildLoop(MyL, BBL)]->isEnabled())
	BBL = MyL;

    }

    if(MyL == BBL) {

      for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; ++BI) {

	if(valueWillBeRAUWdOrDeleted(BI)) {
	  totalIntegrationGoodness += eliminatedInstructionPoints;
	  timeBonus += eliminatedInstructionPoints;
	}

      }

    }

  }

  errs() << getShortHeader() << ": int-goodness " << totalIntegrationGoodness << " (child: " << childIntegrationGoodness << ", codesize: " << newInstPenalty << ", timebonus: " << timeBonus << ")\n";

}

void InlineAttempt::findProfitableIntegration(DenseMap<Function*, unsigned>& nonInliningPenalty) {

  IntegrationAttempt::findProfitableIntegration(nonInliningPenalty);

  // Add goodness due to instructions that can be eliminated if we're inlined:
  int64_t daeBonus = 0;
  if(parent) {
    daeBonus = (extraInstructionPoints * parent->disableInline(CI, true));
    daeBonus += (extraInstructionPoints * nDependentLoads);
  }
  totalIntegrationGoodness += daeBonus;

  // See if the incentive to inline this function everywhere makes it worth inlining:
  int64_t usedNIPenalty = 0;
  if(totalIntegrationGoodness < 0) {

    if(nonInliningPenalty.count(&F)) {

      if(nonInliningPenalty[&F] > -totalIntegrationGoodness) {

	// Deduct from the penalty to symbolise that inlining has had some cost.
	// The second pass will see other callers moved back out-of-line in this case.
	usedNIPenalty = -totalIntegrationGoodness;
	// For now express our own goodness assuming we're the only obstacle
	// to deleting the function entirely. If that doesn't turn out to be so,
	// other uses will exhaust the credit for that function and we'll opt not to
	// inline at the second pass.
	totalIntegrationGoodness += nonInliningPenalty[&F];
	nonInliningPenalty[&F] += totalIntegrationGoodness;

      }
      else {

	nonInliningPenalty[&F] = 0;
	
      }

    }

  }

  errs() << getShortHeader() << ": adjusted total: " << totalIntegrationGoodness << " (dae bonus: " << daeBonus << ", NIPenalty used: " << usedNIPenalty << ")\n";

  if(parent && (totalIntegrationGoodness < 0)) {

    parent->disableInline(CI, false);
    parent->reduceDependentLoads(nDependentLoads);

  }

}

void PeelAttempt::countDependentLoads() {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->countDependentLoads();

  }

}

void IntegrationAttempt::countDependentLoads() {

  for(DenseMap<Value*, ValCtx>::iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {

    LoadInst* LI = dyn_cast<LoadInst>(it->first);

    if(LI && isa<Instruction>(it->second.first)) {

      it->second.second->nDependentLoads++;

    }

  }


  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->countDependentLoads();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    it->second->countDependentLoads();

  }

}

void PeelAttempt::propagateDependentLoads() {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->propagateDependentLoads();
    nDependentLoads += (*it)->nDependentLoads;

  }

}

void IntegrationAttempt::propagateDependentLoads() {

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->propagateDependentLoads();
    nDependentLoads += it->second->nDependentLoads;

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    it->second->propagateDependentLoads();
    nDependentLoads += it->second->nDependentLoads;

  }

}

void IntegrationHeuristicsPass::estimateIntegrationBenefit() {

  errs() << "Selecting initial integration candidates...\n";

  Module& M = RootIA->getModule();

  DenseSet<Function*> ElimFunctions;
  DenseMap<Function*, unsigned> TotalResidualInsts;

  for(Module::iterator it = M.begin(), itend = M.end(); it != itend; ++it) {

    if(it->isDeclaration())
      continue;
    ElimFunctions.insert(it);

  }

  RootIA->findResidualFunctions(ElimFunctions, TotalResidualInsts);

  DEBUG(dbgs() << ElimFunctions.size() << " functions may be entirely eliminated:\n");
  for(DenseSet<Function*>::iterator it = ElimFunctions.begin(), it2 = ElimFunctions.end(); it != it2; ++it) {
    
    DEBUG(dbgs() << (*it)->getName() << "\n");

  }

  // ElimFunctions now contains only those functions we think could be removed as dead post-integration.
  // TotalResidualInsts should have the total number of instructions that will be residualised per-function.
  // Now build a map from Function to the code size increase that would result from preventing inlining
  // an instance of that function.

  DenseMap<Function*, unsigned> nonInliningPenalty;

  for(Module::iterator it = M.begin(), itend = M.end(); it != itend; ++it) {

    if(it->isDeclaration())
      continue;

    unsigned totalInstructions = 0;

    Function& F = *it;
    for(Function::iterator Fit = F.begin(), Fend = F.end(); Fit != Fend; ++Fit) {

      totalInstructions += Fit->size();

    }

    if(TotalResidualInsts[&F] < totalInstructions) {
      DEBUG(dbgs() << "Function " << F.getName() << " non-inline penalty: " << totalInstructions - TotalResidualInsts[&F] << "\n");
      nonInliningPenalty[&F] = totalInstructions - TotalResidualInsts[&F];
    }
    else {
      DEBUG(dbgs() << "Function " << F.getName() << " will residualise more instructions (" << TotalResidualInsts[&F] << ") than its size (" << totalInstructions << ")\n");
    }
    
  }

  // findProftiableIntegration uses disableInline / disablePeel, which in turn call revertLoadsFromFoldedContexts.
  // This is inefficient when we know that we'll be querying a lot of contexts without changing the integration results!
  // Therefore build an inverse map: this relates an integration context to how many loads which would otherwise would
  // be eliminated must be executed for real if we fold this context.
  // Tricky bit: if we're already decided not to integration some descendent contexts we shouldn't pay the penalty twice.
  // To solve this, when we decide not to integrate some context we deduct its entry from each parent.
  // e.g. if we had f calls g calls h, and f has 1 and 2 resolved loads dependent on pointers in g and h respectively,
  // we initially map g -> 3, h -> 2. Then if we decide to leave h alone we deduct its penalty to leave g -> 1, the additional
  // cost of declining to inline g.
  // Rather than store this as a map there's a member 'nDependentLoads' of each IntegrationContext.

  RootIA->countDependentLoads();
  RootIA->propagateDependentLoads();

  DenseMap<Function*, unsigned> savedInliningPenalties;
  savedInliningPenalties.insert(nonInliningPenalty.begin(), nonInliningPenalty.end());

  // Run once: some functions' nonInliningPenalty may be exhausted.
  RootIA->findProfitableIntegration(nonInliningPenalty);

  // Remove penalties for not inlining functions which were exhausted:
  for(DenseMap<Function*, unsigned>::iterator it = nonInliningPenalty.begin(), it2 = nonInliningPenalty.end();
      it != it2; ++it) {

    if(it->second == 0) {
      DEBUG(dbgs() << "After first round, removing incentive not to inline " << it->first->getName() << "\n");
      savedInliningPenalties.erase(it->first);
    }

  }

  RootIA->findProfitableIntegration(savedInliningPenalties);

  RootIA->collectStats();

}
