//===-- DIE.cpp -----------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "DIE"

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/raw_ostream.h"

#include <vector>

using namespace llvm;

// Functions relating to dead instruction elimination. This used to be a seperate phase, but is now run for each context
// as soon as possible after PE has completed. It should detect as many instructions as possible that aren't going
// to have users in the specialised program and save us synthesising them (motivation: creating then deleting an instruction
// in LLVM is quite expensive, and can 'leak' memory due to uniqued constants)

static uint32_t DIEProgressN = 0;
const uint32_t DIEProgressLimit = 10000;

// Just print some reassuring progress indicator
static void DIEProgress() {

  DIEProgressN++;
  if(DIEProgressN == DIEProgressLimit) {

    errs() << ".";
    DIEProgressN = 0;

  }

}

// This visitor will have its visit(...) method called for every user of a particular value V that we're trying to
// show is dead. It sets maybeLive whenever we conclude V might be necessary in the final program.
class llvm::DIVisitor {

public:

  ShadowValue V;
  bool maybeLive;

  DIVisitor(ShadowValue _V) : V(_V), maybeLive(false) { }

  virtual void visit(ShadowInstruction* UserI, IntegrationAttempt* UserIA, uint32_t blockIdx, uint32_t instIdx) {

    InlineAttempt* UserInA = UserIA->getFunctionRoot();

    // Null instruction means we found a user in a dead block.
    if(!UserI) {

      if(UserInA->blocksReachableOnFailure && 
	 UserInA->blocksReachableOnFailure->count(blockIdx))
	maybeLive = true;

      return;

    }

    // The instruction must remain around if it might be used by failed code paths.
    // Ideally we would only keep things whose live ranges extend across tests
    // that branch to failed code, but here's a cheap approximation:
    // If the user block can be reached on failed paths, and the user is not certainly
    // committed to the same block as the original, then such a live range may exist and
    // we'll keep the value.

    if(UserInA->blocksReachableOnFailure && 
       UserInA->blocksReachableOnFailure->count(UserI->parent->invar->idx)) {

      if((!V.isInst()) || 
	 UserI->parent != V.u.I->parent ||
	 UserI->parent->IA->hasSplitInsts(UserI->parent)) {

	maybeLive = true;
	return;

      }

    }

    if((inst_is<CallInst>(UserI) || inst_is<InvokeInst>(UserI)) && !inst_is<MemIntrinsic>(UserI)) {

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
	LLVM_DEBUG(dbgs() << "Must assume instruction alive due to use in unexpanded call " << itcache(UserI) << "\n");
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

	  ImmutableCallSite ICS(UserI->invar->I);

	  Function::arg_iterator it = CalledF->arg_begin();
	  for(unsigned i = 0; i < ICS.arg_size(); ++i) {

	    if(UserI->getCallArgOperand(i) == V) {

	      if(it == CalledF->arg_end()) {

		// Varargs
		maybeLive = true;
		return;

	      }
	      else if(!IA->willBeReplacedOrDeleted(ShadowValue(&(IA->argShadows[i])))) {

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
    else if(inst_is<MemTransferInst>(UserI) && UserI->parent->IA->canSynthMTI(UserI)) {

      // Memcpy et al won't use their arguments if they're to be synthesised.
      return;

    }
    else if(UserI->parent->IA->willBeReplacedOrDeleted(ShadowValue(UserI)))
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

// Does V allocate memory, either on the stack or by calling a known allocation function?
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

// Eliminate some easy cases of instructions that might appear dead, but need to be kept for their side-effects.
// Some, such as branches, might get eliminated through other means, but shouldn't go away just because they aren't directly used.
bool IntegrationAttempt::shouldDIE(ShadowInstruction* I) {

  if(inst_is<CallInst>(I) || inst_is<InvokeInst>(I)) {

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

// Implement logic passing the visitor around. Might genericise this if more situations emerge
// requiring us to visit users across contexts.

// PeelIteration overrides this; if not overridden this is a function instance and there is no
// next iteration to worry about.
bool IntegrationAttempt::visitNextIterationPHI(ShadowInstructionInvar* I, DIVisitor& Visitor) {

  return false;

}

// See if the next iteration's header phis use I. We'll assume they need it if we didn't establish
// a unique iteration count for this loop, or if there are branches out of specialised code, e.g. due to
// guard check failures, leading to an unspecialised copy of the loop.
bool PeelIteration::visitNextIterationPHI(ShadowInstructionInvar* I, DIVisitor& Visitor) {

  if(inst_is<PHINode>(I)) {

    if(I->parent->idx == L->headerIdx) {

      if(PeelIteration* PI = getNextIteration()) {

	Visitor.visit(PI->getInst(I), PI, I->parent->idx, I->idx);

      }
      else if(parentPA->isTerminated()) {

	// The instruction would be used by the next iteration,
	// but there is no such iteration, so it is unused unless there may be an out-of-loop user.

	InlineAttempt* UserInA = getFunctionRoot();

	if(UserInA->blocksReachableOnFailure && 
	   UserInA->blocksReachableOnFailure->count(I->parent->idx)) {
	  
	  Visitor.notifyUsersMissed();

	}

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

// VI is an in-loop instruction that uses Visitor.V, a loop invariant. Check whether any
// iteration will require the value. Assume it is used if we're synthesising an unspecialised
// copy of the loop for any reason.
void PeelIteration::visitVariant(ShadowInstructionInvar* VI, DIVisitor& Visitor) {

  const ShadowLoopInvar* immediateChild = immediateChildLoop(L, VI->parent->outerScope);

  PeelAttempt* LPA = getPeelAttempt(immediateChild);
  if(LPA && LPA->isEnabled())
    LPA->visitVariant(VI, Visitor);
  else 
    Visitor.notifyUsersMissed();

}

// Visit each iteration of this loop, looking for VI using Visitor.V. This might involve
// exploring nested loops recursively.
void PeelAttempt::visitVariant(ShadowInstructionInvar* VI, DIVisitor& Visitor) {

  if(!isTerminated())
    Visitor.notifyUsersMissed();

  // Is this a header PHI? If so, this definition-from-outside can only matter for the preheader edge.
  if(VI->parent->naturalScope == L && VI->parent->idx == L->headerIdx && isa<PHINode>(VI->I)) {

    Visitor.visit(Iterations[0]->getInst(VI), Iterations[0], VI->parent->idx, VI->idx);
    return;

  }

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), itend = Iterations.end(); it != itend; ++it) {

    if(VI->parent->outerScope == L) {
      Visitor.visit((*it)->getInst(VI), *it, VI->parent->idx, VI->idx);
    }
    else
      (*it)->visitVariant(VI, Visitor);

  }

}
  
// Visitor.V is defined in-loop, used out-of-loop by UserI (but we require LCSSA form,
// so certainly an exit phi node). Check if UserI is alive.
void InlineAttempt::visitExitPHI(ShadowInstructionInvar* UserI, DIVisitor& Visitor) {

  release_assert(UserI->parent->naturalScope == 0 && "Reached bottom visiting exit PHI");
  Visitor.visit(getInst(UserI), this, UserI->parent->idx, UserI->idx);

}

// Walk up the tree of loops to find Visitor.V's user UserI. Note if we discover any
// loop without a known iteration count, the loops will be emitted unchanged and Visitor.V
// should be marked alive.
void PeelIteration::visitExitPHI(ShadowInstructionInvar* UserI, DIVisitor& Visitor) {

  if(parentPA->isTerminated()) {
    assert(inst_is<PHINode>(UserI));
    if(UserI->parent->naturalScope != L)
      parent->visitExitPHI(UserI, Visitor);
    else
      Visitor.visit(getInst(UserI), this, UserI->parent->idx, UserI->idx);
  }
  else {
    Visitor.notifyUsersMissed();
  }

}

void IntegrationAttempt::visitUser(ShadowInstIdx& User, DIVisitor& Visitor) {

  // Figure out what context cares about this value. The only possibilities are: this loop iteration, the next iteration of this loop (latch edge of header phi),
  // a child loop (defer to it to decide what to do), or a parent loop (again defer).
  // Note that nested cases (e.g. this is an invariant two children deep) are taken care of in the immediate child or parent's logic.

  if(User.blockIdx == INVALID_BLOCK_IDX || User.instIdx == INVALID_INSTRUCTION_IDX)
    return;

  ShadowInstructionInvar* SII = getInstInvar(User.blockIdx, User.instIdx);
  const ShadowLoopInvar* UserL = SII->parent->outerScope;

  if(UserL == L) {
	  
    if(!visitNextIterationPHI(SII, Visitor)) {

      // Just an ordinary user in the same iteration (or out of any loop!).
      Visitor.visit(getInst(User.blockIdx, User.instIdx), this, User.blockIdx, User.instIdx);

    }

  }
  else {

    if((!L) || L->contains(UserL)) {

      const ShadowLoopInvar* outermostChildLoop = immediateChildLoop(L, UserL);
      // Used in a child loop. Check if that child exists at all and defer to it.

      PeelAttempt* LPA = getPeelAttempt(outermostChildLoop);

      if(LPA && LPA->isEnabled())
	LPA->visitVariant(SII, Visitor);
      else if((!getBB(outermostChildLoop->headerIdx)))
	Visitor.visit(0, this, User.blockIdx, User.instIdx); // Loop not explored, but a failed version may exist
      else
	Visitor.notifyUsersMissed();

    }
    else {

      visitExitPHI(SII, Visitor);

    }

  }

}

// Visit each user for V (== Visitor.V), looking for live users that will require
// us to synthesise V.
void IntegrationAttempt::visitUsers(ShadowValue V, DIVisitor& Visitor) {

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

// Returns true if V is *already* tagged dead.
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

// Returns true if V is *already* tagged dead and isn't needed for other reasons
bool llvm::willBeDeleted(ShadowValue V) {

  if(requiresRuntimeCheck(V, false))
    return false;

  if(val_is<AtomicRMWInst>(V) || val_is<AtomicCmpXchgInst>(V))
    return false;

  return _willBeDeleted(V);

}

// Returns true if V is *already* tagged dead, and/or will be replaced in the specialised program
bool IntegrationAttempt::_willBeReplacedOrDeleted(ShadowValue V) {

  if(_willBeDeleted(V))
    return true;

  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(V));
  if(!IVS)
    return false;

  if(IVS->Values.size() != 1)
    return false;

  if(!canSynthVal(&V, IVS->SetType, IVS->Values[0]))
    return false;
  
  return true;

}

// Returns true if V is *already* tagged dead, and/or will be replaced in the specialised program
bool IntegrationAttempt::willBeReplacedOrDeleted(ShadowValue V) {

  if(requiresRuntimeCheck(V, false))
    return false;

  if(val_is<AtomicRMWInst>(V) || val_is<AtomicCmpXchgInst>(V))
    return false;

  return _willBeReplacedOrDeleted(V);

}

// Returns true if V is *already* tagged dead, and/or will be replaced with a constant in the specialised program
bool IntegrationAttempt::willBeReplacedWithConstantOrDeleted(ShadowValue V) {

  if(requiresRuntimeCheck(V, false))
    return false;

  if(val_is<AtomicRMWInst>(V) || val_is<AtomicCmpXchgInst>(V))
    return false;

  if(_willBeDeleted(V))
    return true;
  if(hasConstReplacement(V))
    return true;

  return false;

}

// Is this call's return value needed?
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

// Tag a value as unused if possible
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

    DenseMap<ShadowValue, std::vector<std::pair<ShadowValue, uint32_t > > >::iterator findit = 
      GlobalIHP->indirectDIEUsers.find(V);
    if(findit != GlobalIHP->indirectDIEUsers.end()) {

      // TODO: come up with a more memory-efficient way to determine when an allocation, FD or similar
      // can be removed.

      return false;

      /*
      // First check if users have already been committed:
      release_assert(I->i.PB && 
      isa<ImprovedValSetSingle>(I->i.PB) && 
      cast<ImprovedValSetSingle>(I->i.PB)->Values.size() == 1);
	
      if(cast<ImprovedValSetSingle>(I->i.PB)->Values[0].V.isPtrIdx()) {

      AllocData* AD = getAllocData(cast<ImprovedValSetSingle>(I->i.PB)->Values[0].V);
      if(AD->PatchRefs.size())
      return false;

      }
      else if(cast<ImprovedValSetSingle>(I->i.PB)->Values[0].V.isFdIdx()) {

      FDGlobalState& GFDS = GlobalIHP->fds[cast<ImprovedValSetSingle>(I->i.PB)->Values[0].V.getFd()];
      if(GFDS.PatchRefs.size())
      return false;

      }
      else {

      release_assert(0 && "Not an allocation, not an FD, but has indirect users?");

      }

      std::vector<std::pair<ShadowValue, uint32_t> >& Users = findit->second;

      for(uint32_t i = 0; i < Users.size(); ++i) {

      // If the IA has been deallocated then the user must have been committed already
      // or thrown away, and can be spotted as a patch request.
      if(!pass->IAs[Users[i].second])
      continue;

      if(!willBeDeleted(Users[i].first)) {

      if(verbose)
      errs() << itcache(V) << " used by " << itcache(Users[i].first) << "\n";	      

      return false;

      }

      */

    }

    if(ShadowInstruction* I = V.getInst()) {

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

  if(isCommitted())
    return;

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

      const ShadowLoopInvar* EnterL = immediateChildLoop(L, BB->invar->naturalScope);
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

      bool delOrConst = willBeDeleted(ShadowValue(SI));

      if(inst_is<CallInst>(SI) || inst_is<InvokeInst>(SI)) {

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

// Tag allocations and file descriptors that are used indirectly (via memory)
void InlineAttempt::gatherIndirectUsers() {

  for(uint32_t i = 0, ilim = argShadows.size(); i != ilim; ++i) {

    if(argShadows[i].i.PB)
      noteIndirectUse(ShadowValue(&argShadows[i]), argShadows[i].i.PB);

  }

  gatherIndirectUsersInLoop(0);

}

// Called only for unbounded loops, which cannot contain expanded subloops, so no need to check.
void IntegrationAttempt::gatherIndirectUsersInLoop(const ShadowLoopInvar* L) {

  uint32_t bbi;
  if(L)
    bbi = L->headerIdx;
  else
    bbi = 0;

  for(uint32_t bblim = BBsOffset + nBBs; 
      bbi != bblim && ((!L) || L->contains(getBBInvar(bbi)->naturalScope)); ++bbi) {

    ShadowBB* BB = getBB(bbi);
    if(!BB)
      continue;
    
    for(uint32_t i = 0, ilim = BB->insts.size(); i != ilim; ++i) {

      if(InlineAttempt* IA = getInlineAttempt(&BB->insts[i]))
	IA->gatherIndirectUsers();

      if(BB->insts[i].i.PB)
	noteIndirectUse(ShadowValue(&BB->insts[i]), BB->insts[i].i.PB);

    }

  }

}
