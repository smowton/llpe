// Functions which enable / disable inlining or peeling of particular sub-elements of the program
// and which queue reconsideration of parts whose results will have changed.

#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Instructions.h"

using namespace llvm;

void IntegrationAttempt::disablePeel(const Loop* L) {

  // It's up to the caller whether we end up trying to inline the children of the loop.
  // e.g. if there are child calls and loops (and loops within calls within loops),
  // they should have called disable* functions on them before calling us.

  // We simply have to disable the named loop, and if it's current enabled and expanded,
  // queue an attempt to do an invariant improvement of the loop's body.

  // We must also reconsider DSE, DAE and DIE because loads might have been restored to the loop
  // body, in turn resurrecting store instructions that feed them, as well as locations and
  // intermediate values that they use.

  PeelAttempt* PA = getPeelAttempt(L);
  if(!ignorePAs.insert(L).second)
    return;
  if(!PA)
    return;

  // First, queue an improvement attempt against the loop's headers, and load forwarding attempts
  // against all within the loop:

  /*

    // Disabled this for now because it requires quite a bit of work to cope with trying to evaluate
    // instructions in a context that ought to be possible to explore further.
    // This should in future be combined with attempting to find DE FACTO VARIANTS: before trying to
    // figure the value of an instruction, result of a load or liveness of an edge, try to do it at each
    // parent context (i.e. with progressively more information / specialisation). Then if we find we *can*
    // (e.g. because an instruction turned out to be effectively invariant in a certain context) then we
    // can both avoid repeating the work for every iteration of the loop AND figure out to what degree
    // the inner loop could be improved if we left the outer loop un-peeled.
    // This would also include the ideas of skipping levels of loops in peeling and attempting to inline
    // calls in an invariant context.

  BasicBlock* LHeader = L->getHeader();
  for(BasicBlock::iterator BI = LHeader->begin(), BE = LHeader->end(); BI != BE && isa<PHINode>(BI); ++BI) {
    pass->queueTryEvaluate(this, BI);
  }

  queueCheckAllLoadsInScope(L);

  // Evaluate the PHIs and loads queued above.
  pass->runQueue();

  */

  // Now undo any DSE and consequent DAE / DIE that resolved to a lifespan including the offending loop.
  // For now this is quite simple: both DSE and DAE can't find something dead if there's an unexpanded
  // loop in their path, so there's no sense even retrying these.

  // Similarly the formerly dead instructions which return to life because they now have a user shouldn't
  // be re-tested because we've just exhibited a concrete user: they're certainly alive now.
  
  PA->revertDSEandDAE();

  // Another reason why values might return to life: they're conventionally used, either as
  // loop header PHI arguments or as invariants.
  
  PA->revertExternalUsers();

}

void IntegrationAttempt::disableInline(CallInst* CI) {

  // Much like the above, but disabling an inline attempt rather than a peel. This is rather simpler
  // because instructions can only be directly used via the arguments. The DSE / DAE situation is
  // identical.

  InlineAttempt* IA = getInlineAttempt(CI);
  if(!ignoreIAs.insert(CI).second)
    return;
  if(!IA)
    return;

  IA->revertDSEandDAE();

  for(unsigned i = 0; i < CI->getNumArgOperands(); ++i) {

    revertDeadValue(CI->getArgOperand(i));

  }

}

void IntegrationAttempt::revertDSEandDAE() {

  for(DenseSet<ValCtx>::iterator it = deadValuesTraversingThisContext.begin(),
	it2 = deadValuesTraversingThisContext.end(); it != it2; ++it) {

    it->second->revertDeadValue(it->first);

  }

}

void PeelAttempt::revertDSEandDAE() {

  for(unsigned i = 0; i < Iterations.size(); ++i)
    Iterations[i]->revertDSEandDAE();

}

class llvm::ProcessExternalCallback : public OpCallback {
public:
  
  const Loop* L;

  ProcessExternalCallback(const Loop* _L) : L(_L) {} 

  virtual void processExtOperand(IntegrationAttempt* Ctx, Value* V) = 0;

  virtual void callback(IntegrationAttempt* Ctx, Value* V) {

    const Loop* ArgL = Ctx->getLoopContext();
    if((!ArgL) || !L->contains(ArgL)) // Is V from a context outside our caller's?
      processExtOperand(Ctx, V);

  }

};

class RevertExternalCallback : public ProcessExternalCallback {
public:
  
  RevertExternalCallback(const Loop* _L) : ProcessExternalCallback(_L)  {}

  virtual void processExtOperand(IntegrationAttempt* Ctx, Value* V) {
    Ctx->revertDeadValue(V);
  }

};

class RetryExternalCallback : public ProcessExternalCallback {
public:
  
  RetryExternalCallback(const Loop* _L) : ProcessExternalCallback(_L)  {}

  virtual void processExtOperand(IntegrationAttempt* Ctx, Value* V) {
    Ctx->queueDIE(V);
  }

};

void PeelAttempt::callExternalUsers(ProcessExternalCallback& PEC) {

  for(Loop::block_iterator BI = L->block_begin(), BE = L->block_end(); BI != BE; ++BI) {

    for(BasicBlock::iterator II = (*BI)->begin(), IE = (*BI)->end(); II != IE; ++II) {

      const Loop* ICtx = Iterations[0]->getValueScope(II);
      if((!ICtx) || !L->contains(ICtx))
	continue;

      Iterations[0]->walkOperands(II, PEC);

    }

  }

}

void PeelAttempt::revertExternalUsers() {

  RevertExternalCallback REC(L);
  callExternalUsers(REC);

}

void PeelAttempt::retryExternalUsers() {

  RetryExternalCallback REC(L);
  callExternalUsers(REC);

}

class RevertDeadValueCallback : public OpCallback {
public:

  virtual void callback(IntegrationAttempt* Ctx, Value* V) {

    Ctx->revertDeadValue(V);

  }

};

void IntegrationAttempt::revertDeadValue(Value* V) {

  if(!deadValues.erase(V))
    return;

  RevertDeadValueCallback CB;
  walkOperands(V, CB);

}

void IntegrationAttempt::tryKillAndQueue(Instruction* I) {

  bool killed;
  if(StoreInst* SI = dyn_cast<StoreInst>(I))
    killed = tryKillStore(SI);
  else if(MemTransferInst* MTI = dyn_cast<MemTransferInst>(I))
    killed = tryKillMTI(MTI);
  else if(MemIntrinsic* MSI = dyn_cast<MemIntrinsic>(I))
    killed = tryKillMemset(MSI);

  if(killed) {

    queueDIEOperands(I);

  }

}

void IntegrationAttempt::getRetryStoresAndAllocs(std::vector<ValCtx>& Result) {

  for(DenseSet<ValCtx>::iterator it = deadValuesTraversingThisContext.begin(),
	it2 = deadValuesTraversingThisContext.end(); it != it2; ++it) {

    Result.push_back(*it);

  }

}

void PeelAttempt::getRetryStoresAndAllocs(std::vector<ValCtx>& storesAndAllocs) {

  for(unsigned i = 0; i < Iterations.size(); ++i) {

    Iterations[i]->getRetryStoresAndAllocs(storesAndAllocs);

  }

  std::sort(storesAndAllocs.begin(), storesAndAllocs.end());
  std::unique(storesAndAllocs.begin(), storesAndAllocs.end());
 
}

void IntegrationAttempt::retryStoresAndAllocs(std::vector<ValCtx>& storesAndAllocs) {

  // Same sequence as for DSE/DAE/DIE in the first place: first MTIs, then stores, then memsets.

  for(std::vector<ValCtx>::iterator it = storesAndAllocs.begin(), it2 = storesAndAllocs.end(); it != it2; ++it) {

    if(MemTransferInst* MTI = dyn_cast<MemTransferInst>(it->first))
      it->second->tryKillAndQueue(MTI);

  }

  for(std::vector<ValCtx>::iterator it = storesAndAllocs.begin(), it2 = storesAndAllocs.end(); it != it2; ++it) {

    if(Instruction* I = dyn_cast<Instruction>(it->first)) {
      if(isa<StoreInst>(I) || isa<MemSetInst>(I))
	it->second->tryKillAndQueue(I);
    }

  }

  for(std::vector<ValCtx>::iterator it = storesAndAllocs.begin(), it2 = storesAndAllocs.end(); it != it2; ++it) {
    
    if(Instruction* I = dyn_cast<Instruction>(it->first)) {
      if(isa<AllocaInst>(I) || isMalloc(I))
	it->second->tryKillAlloc(I);
    }

  }

}

void IntegrationAttempt::enablePeel(const Loop* L) {

  // For now this function assumes that the peel being enabled has been enabled before,
  // i.e. that it proved natural to peel this loop in the initial deep investigation.
  // Soon this will change so that the user can ask for a loop to be expanded that they believe
  // is worth exploring (e.g. a loop nested 2 deep, or a loop entered by an undecidable branch)

  if(!ignorePAs.erase(L))
    return;

  PeelAttempt* PA = getPeelAttempt(L);
  if(!PA)
    return;

  // Reverse the work done by disablePeel: store / allocation elim which once passed through
  // this scope should be retried, and dead instruction elim should be tried again for anything
  // with a user inside the loop or which was used by the stores that are re-eliminated.

  std::vector<ValCtx> VCs;
  PA->getRetryStoresAndAllocs(VCs);
  retryStoresAndAllocs(VCs);

  // Queue any external users of in-loop instructions for DIE.
  PA->retryExternalUsers();

  // All of the above will have populated the DIE queue. Empty it.
  pass->runDIEQueue();

}

void IntegrationAttempt::enableInline(CallInst* CI) {

  // Nearly the above, but with similar simplifications to the disable function above.
  
  if(!ignoreIAs.erase(CI))
    return;

  InlineAttempt* IA = getInlineAttempt(CI);
  if(!IA)
    return;

  std::vector<ValCtx> VCs;
  IA->getRetryStoresAndAllocs(VCs);
  retryStoresAndAllocs(VCs);

  pass->runDIEQueue();

}

bool IntegrationAttempt::loopIsEnabled(const Loop* L) {

  return !ignorePAs.count(L);

}

bool IntegrationAttempt::inlineIsEnabled(CallInst* CI) {

  return !ignoreIAs.count(CI);

}

bool InlineAttempt::isEnabled() {

  if(!parent)
    return true;
  else
    return parent->inlineIsEnabled(CI);

}

bool PeelIteration::isEnabled() {

  return parentPA->isEnabled();

}

bool PeelAttempt::isEnabled() {

  return parent->loopIsEnabled(L);

}

void InlineAttempt::setEnabled(bool en) {

  if(!parent)
    return;

  if(en)
    parent->enableInline(CI);
  else
    parent->disableInline(CI);

}

void PeelIteration::setEnabled(bool en) {

  assert(0 && "Can't individually disable iterations yet");

}

void PeelAttempt::setEnabled(bool en) {

  if(en)
    parent->enablePeel(L);
  else
    parent->disablePeel(L);

}
