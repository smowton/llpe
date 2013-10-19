
#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"

#include <vector>

using namespace llvm;

static uint32_t DIEProgressN = 0;
const uint32_t DIEProgressLimit = 10000;

static void DIEProgress() {

  DIEProgressN++;
  if(DIEProgressN == DIEProgressLimit) {

    errs() << ".";
    DIEProgressN = 0;

  }

}

static bool isAllocationInstruction(ShadowValue V) {

  if(val_is<AllocaInst>(V))
    return true;

  if(val_is<CallInst>(V)) {

    ShadowInstruction* SI = V.getInst();

    Function* F = getCalledFunction(SI);
    DenseMap<Function*, specialfunctions>::iterator findit;

    if((findit = SpecialFunctionMap.find(F)) != SpecialFunctionMap.end()) {

      switch(findit->second) {

      case SF_REALLOC:
      case SF_MALLOC:
	return true;

      default:
	break;

      }

    }

  }

  return false;

}

bool IntegrationAttempt::shouldDIE(ShadowInstruction* I) {

  if(inst_is<CallInst>(I)) {

    if(getInlineAttempt(I))
      return true;
    if(pass->forwardableOpenCalls.count(I))
      return true;
    if(isAllocationInstruction(ShadowValue(I)))
       return true;

    return false;

  }

  switch(I->invar->I->getOpcode()) {
  default:
    return true;
  case Instruction::VAArg:
  case Instruction::Invoke:
  case Instruction::Store:
  case Instruction::Br:
  case Instruction::IndirectBr:
  case Instruction::Switch:
  case Instruction::Resume:
  case Instruction::Unreachable:
    return false;
  }

}

// Implement a visitor that gets called for every dynamic use of an instruction.

bool IntegrationAttempt::visitNextIterationPHI(ShadowInstructionInvar* I, VisitorContext& Visitor) {

  return false;

}

bool PeelIteration::visitNextIterationPHI(ShadowInstructionInvar* I, VisitorContext& Visitor) {

  if(PHINode* PN = dyn_cast_inst<PHINode>(I)) {

    if(PN->getParent() == L->getHeader()) {

      if(PeelIteration* PI = getNextIteration()) {

	Visitor.visit(PI->getInst(I));

      }
      else if(parentPA->isTerminated()) {

	// The instruction would be used by the next iteration,
	// but there is no such iteration, so it is unused.
	return true;

      }
      else {

	Visitor.notifyUsersMissed();

      }

      return true;

    }

  }

  return false;

}

void PeelIteration::visitVariant(ShadowInstructionInvar* VI, VisitorContext& Visitor) {

  const Loop* immediateChild = immediateChildLoop(L, VI->parent->outerScope);

  PeelAttempt* LPA = getPeelAttempt(immediateChild);
  if(LPA && LPA->isEnabled())
    LPA->visitVariant(VI, Visitor);
  else 
    Visitor.notifyUsersMissed();

}

void PeelAttempt::visitVariant(ShadowInstructionInvar* VI, VisitorContext& Visitor) {

  if(Iterations.back()->iterStatus != IterationStatusFinal)
    Visitor.notifyUsersMissed();

  // Is this a header PHI? If so, this definition-from-outside can only matter for the preheader edge.
  if(VI->parent->naturalScope == L && VI->I->getParent() == L->getHeader() && isa<PHINode>(VI->I)) {

    Visitor.visit(Iterations[0]->getInst(VI));
    return;

  }

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), itend = Iterations.end(); it != itend; ++it) {

    if(VI->parent->outerScope == L) {
      Visitor.visit((*it)->getInst(VI));
    }
    else
      (*it)->visitVariant(VI, Visitor);

  }

}
  
void InlineAttempt::visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor) {

  release_assert(UserI->parent->naturalScope == 0 && "Reached bottom visiting exit PHI");
  Visitor.visit(getInst(UserI));

}

void PeelIteration::visitExitPHI(ShadowInstructionInvar* UserI, VisitorContext& Visitor) {

  if(parentPA->isTerminated()) {
    assert(isa<PHINode>(UserI));
    if(UserI->parent->naturalScope != L)
      parent->visitExitPHI(UserI, Visitor);
    else
      Visitor.visit(getInst(UserI));
  }
  else {
    Visitor.notifyUsersMissed();
  }

}

void IntegrationAttempt::visitUser(ShadowInstIdx& User, VisitorContext& Visitor) {

  // Figure out what context cares about this value. The only possibilities are: this loop iteration, the next iteration of this loop (latch edge of header phi),
  // a child loop (defer to it to decide what to do), or a parent loop (again defer).
  // Note that nested cases (e.g. this is an invariant two children deep) are taken care of in the immediate child or parent's logic.

  if(User.blockIdx == INVALID_BLOCK_IDX || User.instIdx == INVALID_INSTRUCTION_IDX)
    return;

  if(getFunctionRoot()->blocksReachableOnFailure && 
     getFunctionRoot()->blocksReachableOnFailure->count(User.blockIdx)) {
    Visitor.notifyUsersMissed();
    return;
  }

  ShadowInstructionInvar* SII = getInstInvar(User.blockIdx, User.instIdx);
  const Loop* UserL = SII->parent->outerScope;

  if(UserL == L) {
	  
    if(!visitNextIterationPHI(SII, Visitor)) {

      // Just an ordinary user in the same iteration (or out of any loop!).
      Visitor.visit(getInst(User.blockIdx, User.instIdx));

    }

  }
  else {

    if((!L) || L->contains(UserL)) {

      const Loop* outermostChildLoop = immediateChildLoop(L, UserL);
      // Used in a child loop. Check if that child exists at all and defer to it.

      PeelAttempt* LPA = getPeelAttempt(outermostChildLoop);

      if(LPA && LPA->isEnabled())
	LPA->visitVariant(SII, Visitor);
      else if(!getBB(invarInfo->LInfo[outermostChildLoop]->headerIdx))
	return; // Block was not explored, hence failing to find the loop
      else
	Visitor.notifyUsersMissed();

    }
    else {

      visitExitPHI(SII, Visitor);

    }

  }

}

void IntegrationAttempt::visitUsers(ShadowValue V, VisitorContext& Visitor) {

  ImmutableArray<ShadowInstIdx>* Users;
  if(V.isInst()) {
    Users = &(V.getInst()->invar->userIdxs);
  }
  else {
    Users = &(V.getArg()->invar->userIdxs);
  }
  
  for(uint32_t i = 0; i < Users->size() && Visitor.shouldContinue(); ++i) {

    visitUser((*Users)[i], Visitor);

  }

}

static bool _willBeDeleted(ShadowValue V) {

  uint32_t dieStatus;

  if(ShadowInstruction* SI = V.getInst()) {
    dieStatus = SI->dieStatus;
  }
  else if(ShadowArg* SA = V.getArg()) {
    dieStatus = SA->dieStatus;
  }
  else {
    return false;
  }

  if(isAllocationInstruction(V))
    return dieStatus == (INSTSTATUS_DEAD | INSTSTATUS_UNUSED_WRITER);
  else
    return dieStatus != INSTSTATUS_ALIVE;

}

bool llvm::willBeDeleted(ShadowValue V) {

  if(requiresRuntimeCheck(V, false))
    return false;
  return _willBeDeleted(V);

}

static bool _willBeReplacedOrDeleted(ShadowValue V) {

  if(_willBeDeleted(V))
    return true;

  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(V));
  if(!IVS)
    return false;

  if(IVS->Values.size() != 1)
    return false;

  if(!V.getCtx()->canSynthVal(V.isInst() ? V.getInst() : 0, IVS->SetType, IVS->Values[0]))
    return false;
  
  return true;

}

bool llvm::willBeReplacedOrDeleted(ShadowValue V) {

  if(requiresRuntimeCheck(V, false))
    return false;
  return _willBeReplacedOrDeleted(V);

}

bool llvm::willBeReplacedWithConstantOrDeleted(ShadowValue V) {

  if(requiresRuntimeCheck(V, false))
    return false;

  if(_willBeDeleted(V))
    return true;
  if(getConstReplacement(V))
    return true;

  return false;

}

class DIVisitor : public VisitorContext {

  ShadowValue V;

public:

  bool maybeLive;

  DIVisitor(ShadowValue _V) : V(_V), maybeLive(false) { }

  virtual void visit(ShadowInstruction* UserI) {

    // Null instruction means we found a user in a dead block.
    if(!UserI)
      return;

    CallInst* CI;
    if((CI = dyn_cast_inst<CallInst>(UserI)) && !isa<MemIntrinsic>(CI)) {

      if(UserI->parent->IA->isResolvedVFSCall(UserI)) {

	if(V == UserI->getCallArgOperand(0) && !UserI->parent->IA->VFSCallWillUseFD(UserI))
	  return;
	
	// The buffer argument isn't needed if the read call will be deleted.
	if(UserI->parent->IA->isUnusedReadCall(UserI)) {

	  if(V == UserI->getCallArgOperand(1))
	    return;

	}

      }

      InlineAttempt* IA = UserI->parent->IA->getInlineAttempt(UserI);
      if((!IA) || (!IA->isEnabled()) || IA->commitsOutOfLine()) {
	DEBUG(dbgs() << "Must assume instruction alive due to use in unexpanded call " << UserI->parent->IA->itcache(*CI) << "\n");
	maybeLive = true;
	return;
      }

      // == called value?
      if(V == UserI->getOperandFromEnd(1)) {
	maybeLive = true;
	return;
      }
      else {

	Function* CalledF = getCalledFunction(UserI);

	if(CalledF) {

	  Function::arg_iterator it = CalledF->arg_begin();
	  for(unsigned i = 0; i < CI->getNumArgOperands(); ++i) {

	    if(UserI->getCallArgOperand(i) == V) {

	      if(it == CalledF->arg_end()) {

		// Varargs
		maybeLive = true;
		return;

	      }
	      else if(!willBeReplacedOrDeleted(ShadowValue(&(IA->argShadows[i])))) {

		maybeLive = true;
		return;

	      }

	    }

	    if(it != CalledF->arg_end())
	      ++it;

	  }
	}
	else {
	  maybeLive = true;
	  return;
	}

      }

    }
    else if(willBeReplacedOrDeleted(ShadowValue(UserI)))
      return;
    else {

      maybeLive = true;

    }

  }
  
  virtual void notifyUsersMissed() {
    maybeLive = true;
  }

  virtual bool shouldContinue() {
    return !maybeLive;
  }

};

bool InlineAttempt::isOwnCallUnused() {

  if(Callers.empty())
    return false;
  else if(isPathCondition)
    return false;
  else {

    for(SmallVector<ShadowInstruction*, 1>::iterator it = Callers.begin(),
	  itend = Callers.end(); it != itend; ++it) {

      if((*it)->dieStatus == INSTSTATUS_ALIVE)
	return false;

    }

    return true;

  }

}

bool IntegrationAttempt::valueIsDead(ShadowValue V) {

  bool verbose = false;

  if(val_is<ReturnInst>(V)) {
    
    if(F.getType()->isVoidTy())
      return false;
    InlineAttempt* CallerIA = getFunctionRoot();
    return CallerIA->isOwnCallUnused();

  }
  else {

    if(requiresRuntimeCheck(V, false))
      return false;

    // At the moment only FDs and allocations have indirect users like this.
    // These are instructions that don't directly use this instruction
    // but will do in the final committed program. Check that each is dead:
    if(ShadowInstruction* I = V.getInst()) {

      DenseMap<ShadowInstruction*, std::vector<ShadowValue> >::iterator findit = 
	GlobalIHP->indirectDIEUsers.find(I);
      if(findit != GlobalIHP->indirectDIEUsers.end()) {

	std::vector<ShadowValue>& Users = findit->second;

	for(uint32_t i = 0; i < Users.size(); ++i) {

	  if(!willBeDeleted(Users[i])) {

	    if(verbose) {
	      errs() << itcache(V) << " used by " << itcache(Users[i]);
	      if(IntegrationAttempt* IA = Users[i].getCtx()) {

		errs() << " in context " << IA->SeqNumber;

	      }
	      errs() << "\n";
	    }

	    return false;

	  }

	}

      }

      if(InlineAttempt* IA = getInlineAttempt(I)) {

	if(IA->hasFailedReturnPath())
	  return false;

      }

    }

    DIVisitor DIV(V);
    visitUsers(V, DIV);
    
    if(verbose) {
      if(DIV.maybeLive)
	errs() << itcache(V) << " used directly\n";
      else
	errs() << itcache(V) << " not used\n";
    }
    

    return !DIV.maybeLive;

  }

}

// Try to kill all instructions in this context, and if appropriate, arguments.
// Everything should be killed in reverse topological order.
void InlineAttempt::runDIE() {

  // First try to kill our instructions:
  IntegrationAttempt::runDIE();

  // Don't eliminate 
  if(Callers.empty())
    return;
  
  // And then our formal arguments:
  for(uint32_t i = 0; i < F.arg_size(); ++i) {
    ShadowArg* SA = &(argShadows[i]);
    if(willBeReplacedWithConstantOrDeleted(ShadowValue(SA)))
      continue;
    if(Callers.empty() && SA->invar->A->hasNoAliasAttr())
      continue;
    if(valueIsDead(ShadowValue(SA))) {
      SA->dieStatus |= INSTSTATUS_DEAD;
    }
  }

}

void IntegrationAttempt::runDIE() {

  // BBs are already in topological order:
  for(uint32_t i = nBBs; i > 0; --i) {

    ShadowBB* BB = BBs[i-1];
    if(!BB)
      continue;

    if(BB->invar->naturalScope != L) {

      const Loop* EnterL = immediateChildLoop(L, BB->invar->naturalScope);
      if(PeelAttempt* LPA = getPeelAttempt(EnterL)) {

	for(int i = LPA->Iterations.size() - 1; i >= 0; --i) {

	  LPA->Iterations[i]->runDIE();
	  
	}

      }

      // Skip loop blocks regardless of whether we entered the loop:
      while(i > 0 && ((!BBs[i-1]) || EnterL->contains(BBs[i-1]->invar->naturalScope)))
	--i;
      ++i;
      continue;

    }

    for(uint32_t j = BB->insts.size(); j > 0; --j) {

      DIEProgress();

      ShadowInstruction* SI = &(BB->insts[j-1]);

      if(!shouldDIE(SI))
	continue;

      bool delOrConst = willBeReplacedWithConstantOrDeleted(ShadowValue(SI));

      if(inst_is<CallInst>(SI)) {

	if((!delOrConst) && valueIsDead(ShadowValue(SI)))
	  SI->dieStatus |= INSTSTATUS_DEAD; 

	if(InlineAttempt* IA = getInlineAttempt(SI)) {

	  IA->runDIE();

	}

      }
      else {

	if(delOrConst)
	  continue;

	if(SI->invar->I->mayHaveSideEffects())
	  continue;

	if(valueIsDead(ShadowValue(SI)))
	  SI->dieStatus |= INSTSTATUS_DEAD;

      }

    }

  }

}
