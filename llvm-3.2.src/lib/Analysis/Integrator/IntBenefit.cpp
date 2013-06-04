
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

static uint32_t intBenefitProgressN = 0;
const uint32_t intBenefitProgressLimit = 1000;

static void intBenefitProgress() {

  intBenefitProgressN++;
  if(intBenefitProgressN == intBenefitProgressLimit) {

    errs() << ".";
    intBenefitProgressN = 0;

  }

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

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    const Loop* BBL = BB->invar->outerScope;
    if(L != BBL)
      continue;

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);

      if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {

	Function* F = getCalledFunction(I);
	if(F) {

	  if(!inlineChildren.count(CI))
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
  
  //int64_t daeBonus = extraInstructionPoints * parent->disablePeel(L, true);
  //daeBonus += (extraInstructionPoints * nDependentLoads);

  // Another possible argument: a non-terminated loop will necessarily retain a whole copy of the loop
  // (i.e. will definitely increase code size).

  int64_t nonTermPenalty = 0;

  if(Iterations.back()->iterStatus != IterationStatusFinal) {

    for(Loop::block_iterator it = L->block_begin(), it2 = L->block_end(); it != it2; ++it) {

      nonTermPenalty += (extraInstructionPoints * (*it)->size());

    }

  }

  totalIntegrationGoodness = itersGoodness - nonTermPenalty;

  //errs() << getShortHeader() << ": goodness " << totalIntegrationGoodness << " (dae bonus: " << daeBonus << ", nonterm penalty: " << nonTermPenalty << ", iters total: " << itersGoodness << ")\n";

  if(totalIntegrationGoodness < 0) {

    // Overall, not profitable to peel this loop.
    parent->disablePeel(L);

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

  int64_t timeBonus = 0;

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;
   
    const Loop* BBL = BB->invar->outerScope;
    
    if(L != BBL && ((!L) || L->contains(BBL))) {

      // Count unexpanded loops as ours:
      if(!peelChildren.count(immediateChildLoop(L, BBL)))
	BBL = L;
      else if(!peelChildren[immediateChildLoop(L, BBL)]->isEnabled())
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

  intBenefitProgress();

  //errs() << getShortHeader() << ": int-goodness " << totalIntegrationGoodness << " (child: " << childIntegrationGoodness << ", codesize: " << newInstPenalty << ", timebonus: " << timeBonus << ")\n";

}

void InlineAttempt::findProfitableIntegration(DenseMap<Function*, unsigned>& nonInliningPenalty) {

  IntegrationAttempt::findProfitableIntegration(nonInliningPenalty);

  // Add goodness due to instructions that can be eliminated if we're inlined:
  int64_t daeBonus = 0;
  if(parent) {
    daeBonus = (extraInstructionPoints * nDependentLoads);
  //daeBonus += (extraInstructionPoints * parent->disableInline(CI, true));
  }
  totalIntegrationGoodness += daeBonus;

  // See if the incentive to inline this function everywhere makes it worth inlining:
  int64_t usedNIPenalty = 0;
  if(totalIntegrationGoodness < 0) {

    if(nonInliningPenalty.count(&F)) {

      if(nonInliningPenalty[&F] > -totalIntegrationGoodness) {

	// Deduct from the penalty to symbolise that inlining has had some cost.
	// The second pass will see other callers moved back out-of-line in this case.
	usedNIPenalty += -totalIntegrationGoodness;
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

  //errs() << getShortHeader() << ": adjusted total: " << totalIntegrationGoodness << " (dae bonus: " << daeBonus << ", NIPenalty used: " << usedNIPenalty << ")\n";

  if(parent && (totalIntegrationGoodness < 0)) {

    parent->disableInline(cast<CallInst>(CI->invar->I));
    parent->reduceDependentLoads(nDependentLoads);

  }

}

void PeelAttempt::countDependentLoads() {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->countDependentLoads();

  }

}

void IntegrationAttempt::countDependentLoads() {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {
      
      ShadowInstruction* I = &(BB->insts[j]);
      if(inst_is<LoadInst>(I)) {

	ShadowValue Base;
	int64_t IgnOffset;
	if(getBaseAndConstantOffset(ShadowValue(I), Base, IgnOffset)) {

	  if(ShadowInstruction* ReplI = Base.getInst()) {
	    
	    ReplI->parent->IA->nDependentLoads++;

	  }

	}

      }
      
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

  //errs() << "Selecting initial integration candidates...\n";

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

  // Build an inverse map: this relates an integration context to how many loads which would otherwise would
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

void IntegrationAttempt::collectBlockStats(ShadowBBInvar* BBI, ShadowBB* BB) {

  uint32_t i = 0;
  for(BasicBlock::iterator BI = BBI->BB->begin(), BE = BBI->BB->end(); BI != BE; ++BI, ++i) {
      
    const Loop* BBL = BBI->naturalScope;
    if(L != BBL && ((!L) || L->contains(BBL))) {

      // Count unexplored loops as part of my own context.
      if(!peelChildren.count(immediateChildLoop(L, BBL)))
	BBL = L;

    }

    if(BBL != L) {

      if(instructionCounts(BI))
	improvableInstructionsIncludingLoops++;

    }
    else {

      if(instructionCounts(BI)) { 

	//if(BB == getEntryBlock() && isa<PHINode>(BI))
	//  continue;

	improvableInstructions++;
	improvableInstructionsIncludingLoops++;

	if(!BB)
	  improvedInstructions++;
	else if(getConstReplacement(&(BB->insts[i])))
	  improvedInstructions++;
	else if(BB->insts[i].i.dieStatus != INSTSTATUS_ALIVE)
	  improvedInstructions++;

      }

      if(CallInst* CI = dyn_cast<CallInst>(BI)) {
	DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.find(CI);
	if(it == inlineChildren.end())
	  unexploredCalls.push_back(CI);
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

void IntegrationAttempt::collectLoopStats(const Loop* LoopI) {

  DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.find(LoopI);

  if(it == peelChildren.end()) {

    unexploredLoops.push_back(LoopI);

    for(uint32_t i = invarInfo->LInfo[LoopI]->headerIdx; i < invarInfo->BBs.size(); ++i) {
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

  for(LoopInfo::iterator LoopI = LI[&F]->begin(), LoopE = LI[&F]->end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelIteration::collectAllLoopStats() {

  for(Loop::iterator LoopI = L->begin(), LoopE = L->end(); LoopI != LoopE; ++LoopI)
    collectLoopStats(*LoopI);

}

void PeelAttempt::collectStats() {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it)
    (*it)->collectStats();

}

void IntegrationAttempt::collectStats() {

  unexploredCalls.clear();
  unexploredLoops.clear();
  improvedInstructions = 0;
  improvableInstructions = 0;
  improvableInstructionsIncludingLoops = 0;

  collectAllBlockStats();
  collectAllLoopStats();

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it)
    it->second->collectStats();

  for(DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it)
    it->second->collectStats();

}
