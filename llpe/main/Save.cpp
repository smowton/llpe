//===- Save.cpp -----------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

// These functions relate to committing the specialised program as concrete bitcode.
// ConditionalSpec.cpp implements the aspects of commit which insert unspecialised function
// fragments for the case where specialisation assumptions are found to be false at runtime.

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Attributes.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LLPE.h"
#include "llvm/Analysis/LLPECopyPaste.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/DIBuilder.h"

#include <unistd.h>
#include <stdlib.h>

using namespace llvm;

// Name the output basic blocks for easier debugging? Significantly increases output size.
cl::opt<bool> VerboseNames("int-verbose-names");

static uint32_t SaveProgressN = 0;
const uint32_t SaveProgressLimit = 1000;

static void SaveProgress() {

  SaveProgressN++;
  if(SaveProgressN == SaveProgressLimit) {

    errs() << ".";
    SaveProgressN = 0;

  }

}

// Prepare for the commit: remove instruction mappings that are (a) invalid to write to the final program
// and (b) difficult to reason about once the loop structures start to be modified by unrolling and so on.

void InlineAttempt::prepareCommitCall() {

  if(isCommitted())
    return;

  IntegrationAttempt::prepareCommit();

}

void IntegrationAttempt::prepareCommit() {
  
  for(IAIterator it = child_calls_begin(this), it2 = child_calls_end(this); it != it2; ++it) {

    if(!it->second->isEnabled())
      continue;

    it->second->prepareCommitCall();

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    unsigned iterCount = it->second->Iterations.size();
    unsigned iterLimit = (it->second->Iterations.back()->iterStatus == IterationStatusFinal) ? iterCount : iterCount - 1;

    if(!it->second->isEnabled()) {
    
      if(it->second->isTerminated()) {

	// Loop hasn't been analysed for the general case -- do a rough and ready approximation
	// that emits any edge that is alive in any iteration.

	const ShadowLoopInvar* LInfo = it->second->L;
	for(uint32_t i = LInfo->headerIdx; i < nBBs && it->first->contains(getBBInvar(i)->naturalScope); ++i) {

	  ShadowBB* BB = getBB(i);
	  if(!BB) {

	    // See if block is ever live:
	    if(!blockIsDeadRising(*getBBInvar(i)))
	      BB = createBB(getBBInvar(i));

	  }

	  ShadowBBInvar* BBI = BB->invar;
	  for(uint32_t j = 0, jlim = BBI->succIdxs.size(); j != jlim; ++j) {

	    BB->succsAlive[j] = !edgeIsDeadRising(*BBI, *getBBInvar(BBI->succIdxs[j]), true);

	  }

	}

      }

      continue;
      
    }

    for(unsigned i = 0; i < iterLimit; ++i) {

      it->second->Iterations[i]->prepareCommit();

    }

  }  

}

// Assign basic blocks a name like f-N, where f is the source function name and N
// is a sequential identifier also visible in the GUI.
std::string InlineAttempt::getCommittedBlockPrefix() {

  std::string ret;
  {
    raw_string_ostream RSO(ret);
    RSO << F.getName() << "-" << SeqNumber << " ";
  }
  return ret;

}

std::string PeelIteration::getCommittedBlockPrefix() {

  std::string ret;
  {
    raw_string_ostream RSO(ret);
    RSO << F.getName() << "-L" << getLName() << "-I" << iterationCount << "-" << SeqNumber << " ";
  }
  return ret;

}

// Create an empty function which has the same attributes, linkage etc as F. If addFailedReturnFlag is set,
// change the existing return type T into { T, i1 } (or just i1 if void), where the new boolean return
// will be used to indicate whether this function wants to bail out to unspecialised code.
Function* llvm::cloneEmptyFunction(Function* F, GlobalValue::LinkageTypes LT, const Twine& Name, bool addFailedReturnFlag) {

  FunctionType* NewFType = F->getFunctionType();

  if(addFailedReturnFlag) {

    Type* OldReturn = NewFType->getReturnType();
    Type* FlagType = Type::getInt1Ty(F->getContext());
    Type* NewReturn;

    if(OldReturn->isVoidTy()) {

      NewReturn = FlagType;

    }
    else {

      Type* NewReturnArgs[2] = { OldReturn, FlagType };
      NewReturn = StructType::get(F->getContext(), ArrayRef<Type*>(NewReturnArgs, 2));

    }

    NewFType = FunctionType::get(NewReturn, ArrayRef<Type*>(&*NewFType->param_begin(), &*NewFType->param_end()), NewFType->isVarArg());

  }

  Function* NewF = Function::Create(NewFType, LT, Name, F->getParent());

  // Register the new function so that post-commit optimisation can find it.
  GlobalIHP->commitFunctions.push_back(NewF);

  Function::arg_iterator DestI = NewF->arg_begin();
  for (Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end();
       I != E; ++I, ++DestI)
    DestI->setName(I->getName());
  
  NewF->copyAttributesFrom(F);

  if(addFailedReturnFlag) {

    // The zeroext and signext attributes specify that codegen should expand these
    // to fill a register if it needs to satisfy the C ABI. Since cloned functions (except for the root,
    // whose type is never altered) are not externally called, we don't care about the CC.

    // SRet is an ABI-compliance thing too, and is illegal when the return type is not void.

    auto attrs = NewF->getAttributes();

    attrs = attrs.removeAttribute(F->getContext(), AttributeList::ReturnIndex, Attribute::ZExt);
    attrs = attrs.removeAttribute(F->getContext(), AttributeList::ReturnIndex, Attribute::SExt);
    if(NewFType->getNumParams() != 0)
      attrs = attrs.removeAttribute(F->getContext(), 1, Attribute::StructRet);

    NewF->setAttributes(attrs);

  }

  return NewF;

}

// Return true if it will be necessary to insert code on the path leading from specialised to unspecialised code following
// a failed check that SI's result was as expected.
bool IntegrationAttempt::requiresBreakCode(ShadowInstruction* SI) {

  return SI->needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD && 
    pass->resolvedReadCalls.count(SI);

}

// Create a new specialised basic block. If AddF is specified, put it in that function; otherwise note it as a BB
// that contains specialised code / is a clone of an unspecialised block in the original program (according to isFailedBlock);
// it will get added to a function later.
// If isEntryBlock is set, ensure it is at the front of the block list.
BasicBlock* IntegrationAttempt::createBasicBlock(LLVMContext& Ctx, const Twine& Name, Function* AddF, bool isEntryBlock, bool isFailedBlock) {

  Function* AddTo;
  if(isEntryBlock)
    AddTo = 0;
  else
    AddTo = AddF;
  
  BasicBlock* newBlock;
  if(AddTo && getFunctionRoot()->firstFailedBlock != AddTo->end() && !isFailedBlock) {

    // Add block before any failed blocks
    newBlock = BasicBlock::Create(Ctx, Name, AddTo, &*(getFunctionRoot()->firstFailedBlock));

  }
  else {
    
    // Add block to end of function, or to no function if !AddTo
    newBlock = BasicBlock::Create(Ctx, Name, AddTo);
    if(AddTo && isFailedBlock && getFunctionRoot()->firstFailedBlock == AddTo->end())
      getFunctionRoot()->firstFailedBlock = Function::iterator(newBlock);

  }

  if(!AddF) {

    // Commit function unknown at the moment: save the block for later addition
    // when a function is chosen in SaveSplits.cpp
    if(isFailedBlock)
      getFunctionRoot()->CommitFailedBlocks.push_back(newBlock);
    else
      getFunctionRoot()->CommitBlocks.push_back(newBlock);

  }
  else if(isEntryBlock) {
    
    AddF->getBasicBlockList().push_front(newBlock);

  }

  return newBlock;

}

// Write the basic-block graph for this function specialsiation instance.
// If this function will be committed inline, create special blocks that correspond to the return path
// or the failed-specialisation-assumptions path to unspecialised code.
void InlineAttempt::commitCFG() {

  if(isCommitted())
    return;

  if(!commitsOutOfLine()) {

    std::string Pref;
    if(VerboseNames)
      Pref = getCommittedBlockPrefix();
    returnBlock = createBasicBlock(F.getContext(), VerboseNames ? (StringRef(Pref) + "callexit") : "", CommitF, false, false);

    if(hasFailedReturnPath()) {

      std::string PreName;
      if(VerboseNames)
	PreName = "prereturn";

      failedReturnBlock = createBasicBlock(F.getContext(), PreName, CommitF, false, true);

    }
    else {

      failedReturnBlock = 0;

    }

  }
  else {

    returnBlock = 0;
    failedReturnBlock = 0;

  }

  IntegrationAttempt::commitCFG();

}

// Commit the basic block graph for this specialisation context. 
void IntegrationAttempt::commitCFG() {

  commitState = COMMIT_STARTED;

  Function* CF = getFunctionRoot()->CommitF;
  const ShadowLoopInvar* currentLoop = L;
  
  initFailedBlockCommit();

  for(uint32_t i = 0; i < nBBs; ++i) {

    // Create failed block if necessary:
    createFailedBlock(i + BBsOffset);

    // Now create the specialised block if it exists:
    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    if(currentLoop == L && BB->invar->naturalScope != L) {

      // Entering a loop. First write the blocks for each iteration that's being unrolled:
      PeelAttempt* PA = getPeelAttempt(BB->invar->naturalScope);
      if(PA && PA->isEnabled() && PA->isTerminated()) {

	const ShadowLoopInvar* skipL = BB->invar->naturalScope;

	// Create failed blocks before the loop iterations, so they're available as branch targets.
	for(unsigned j = i + 1; j != nBBs && skipL->contains(getBBInvar(j + BBsOffset)->naturalScope); ++j)
	  createFailedBlock(j + BBsOffset);

	// Create the loop iterations
	for(unsigned j = 0; j < PA->Iterations.size(); ++j)
	  PA->Iterations[j]->commitCFG();

	// If the loop has terminated, skip emitting specialised blocks in this context.
	while(i < nBBs && skipL->contains(getBBInvar(i + BBsOffset)->naturalScope))
	  ++i;
	--i;
	continue;

      }

    }
    
    // Skip loop-entry processing until we're back in local scope.
    // Can't go direct from one loop to another due to preheader.
    currentLoop = BB->invar->naturalScope;
    
    bool isEntryBlock = (!L) && i == 0;
    bool isCommittedEntryBlock = isEntryBlock && commitsOutOfLine();

    std::string Name;
    if(VerboseNames) {
      raw_string_ostream RSO(Name);
      RSO << getCommittedBlockPrefix() << BB->invar->BB->getName();
    }
    else if(isEntryBlock)
      Name = "entry";
    
    BasicBlock* firstNewBlock = createBasicBlock(F.getContext(), Name, CF, isCommittedEntryBlock, false);

    BB->committedBlocks.push_back(CommittedBlock(firstNewBlock, firstNewBlock, 0));
    if(isEntryBlock)
      getFunctionRoot()->entryBlock = firstNewBlock;
      
    // Create extra empty blocks for each path condition that's effective here:
    // If OmitChecks is specified, no tests are emitted and so no blocks are needed.
    uint32_t nCondsHere = pass->omitChecks ? 0 : pass->countPathConditionsAtBlockStart(BB->invar, BB->IA);

    for(uint32_t k = 0; k < nCondsHere; ++k) {

      if(pass->verbosePCs) {

	// The previous block will contain a path condition check: give it a break block that will
	// sit on the edge from specialised to unspecialised code.

	std::string BlockName;
	if(VerboseNames)
	  BlockName = (BB->invar->BB->getName() + ".break").str();
	else
	  BlockName = "";
	BasicBlock* breakBlock = createBasicBlock(F.getContext(), BlockName, CF, false, true);
	BB->committedBlocks.back().breakBlock = breakBlock;

      }

      std::string CondName;
      if(VerboseNames)
	CondName = (BB->invar->BB->getName() + ".pathcond").str();
      else
	CondName = "";

      BasicBlock* newBlock = 
	createBasicBlock(F.getContext(), CondName, CF, false, false);

      BB->committedBlocks.push_back(CommittedBlock(newBlock, newBlock, 0));

    }

    // Create one extra top block if there's a special check at the beginning
    if(BB->insts[0].needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD && !pass->omitChecks) {

      if(pass->verbosePCs || requiresBreakCode(&BB->insts[0])) {
	
	std::string BreakName;
	if(VerboseNames)
	  BreakName = (BB->invar->BB->getName() + ".break").str();
	else
	  BreakName = "";

	BasicBlock* breakBlock = createBasicBlock(F.getContext(), BreakName, CF, false, true);
	BB->committedBlocks.back().breakBlock = breakBlock;

      }

      std::string CheckName;
      if(VerboseNames)
	CheckName = (BB->invar->BB->getName() + ".vfscheck").str();
      else
	CheckName = "";

      BasicBlock* newBlock =
	createBasicBlock(F.getContext(), CheckName, CF, false, false);	

      // New block-let starts from instruction #1
      BB->committedBlocks.push_back(CommittedBlock(newBlock, newBlock, 1));

    }
     
    // Determine if we need to create more BBs because of call inlining, instruction checks and so on.

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* SI = &(BB->insts[j]);
      if(InlineAttempt* IA = getInlineAttempt(SI)) {

	if(IA->isEnabled()) {

	  IA->activeCaller = SI;
	  IA->commitCFG();

	  std::string Pref;
	  if(VerboseNames)
	    Pref = IA->getCommittedBlockPrefix();

	  if(!IA->commitsOutOfLine()) {

	    // Adopt the return block:
	    BB->committedBlocks.push_back(CommittedBlock(IA->returnBlock, IA->returnBlock, j+1));

	    // Direct the call to the appropriate fail block:
	    if(IA->failedReturnBlock) {

	      BasicBlock* targetBlock;
	      if(inst_is<CallInst>(SI))
		targetBlock = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, j + 1);
	      else
		targetBlock = getFunctionRoot()->getSubBlockForInst(BB->invar->succIdxs[1], 0);
	      BranchInst::Create(targetBlock, IA->failedReturnBlock);

	    }

	  }
	  else {

	    // Requires a break afterwards if the target function might branch onto a failed path.
	    // Invoke instructions are a bit special in this respect, as the new block will only
	    // contain a failure check.
	    if(IA->hasFailedReturnPath()) {

	      BasicBlock* newBlock = createBasicBlock(F.getContext(), VerboseNames ? StringRef(Pref) + "OOL callexit" : "", CF, false, false);
	      BB->committedBlocks.push_back(CommittedBlock(newBlock, newBlock, j+1));

	    }

	  }

	  continue;

	}

      }

      // If we need a check *before* this instruction (at the moment only true if it's a read or [f]stat
      // call that will require an inline check) then add a break.
      if(SI->needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD && !GlobalIHP->omitChecks) {

	if(j != 0) {

	  if(pass->verbosePCs || requiresBreakCode(SI)) {

	    BasicBlock* breakBlock = createBasicBlock(F.getContext(), VerboseNames ? StringRef(Name) + ".vfsbreak" : "", CF, false, true);
	    BB->committedBlocks.back().breakBlock = breakBlock;

	  }

	  BasicBlock* newSpecBlock = createBasicBlock(F.getContext(), VerboseNames ? StringRef(Name) + ".vfspass" : "", CF, false, false);
	  BB->committedBlocks.push_back(CommittedBlock(newSpecBlock, newSpecBlock, j + 1));

	}

      }

      // If we have a disabled call, exit phi for a disabled loop, or tentative load
      // then insert a break for a check.
      // This path also handles path conditions that are checked as they are defined,
      // rather than at the top of a block that may be remote from the definition site.
      // Thankfully for my sanity, having your return value checked and being committed
      // as a specialised call are mutually exclusive.
      if(requiresRuntimeCheck(SI, true) && SI->needsRuntimeCheck != RUNTIME_CHECK_READ_LLIOWD) {

	if(j + 1 != BB->insts.size() && inst_is<PHINode>(SI) && inst_is<PHINode>(&BB->insts[j+1]))
	  continue;

	BasicBlock* breakBlock = 0;

	if(pass->verbosePCs) {
	
	  // The previous block will break due to a tentative load. Give it a break block.
	  // For most kinds of break this should belong to the old subblock;
	  // for invoke instructions it should belong to the new one so that the old one's break edge
	  // doesn't have an intermediary block and so can be used for the unwind edge.
	  breakBlock = createBasicBlock(F.getContext(), VerboseNames ? StringRef(Name) + ".tlbreak" : "", CF, false, true);
	  if(!inst_is<InvokeInst>(SI))
	    BB->committedBlocks.back().breakBlock = breakBlock;

	}

	BasicBlock* newSpecBlock = createBasicBlock(F.getContext(), VerboseNames ? StringRef(Name) + ".checkpass" : "", CF, false, false);
	BB->committedBlocks.push_back(CommittedBlock(newSpecBlock, newSpecBlock, j+1));

	if(inst_is<InvokeInst>(SI) && breakBlock)
	  BB->committedBlocks.back().breakBlock = breakBlock;

      }

    }

    // If the block has ignored edges outgoing, it will branch direct to unspecialised code.
    // Make a break block for that purpose.
    if(pass->verbosePCs && hasLiveIgnoredEdges(BB)) {

      BB->committedBlocks.back().breakBlock = 
	createBasicBlock(F.getContext(), VerboseNames ? StringRef(Name) + ".directbreak" : "", CF, false, true);

    }

  }

}

// Convert a shadow-value to the value we should refer to in the committed program.
Value* IntegrationAttempt::getCommittedValue(ShadowValue SV) {

  switch(SV.t) {
  case SHADOWVAL_OTHER:
    return SV.u.V;
  case SHADOWVAL_GV:
    return SV.u.GV->G;
  case SHADOWVAL_INST: 
    {
      release_assert(SV.u.I->committedVal && "Instruction depends on uncommitted instruction");
      return SV.u.I->committedVal;
    }
  case SHADOWVAL_ARG:
    {
      // It can be valid to find a root function argument without committed value
      // as they are pseudo-allocations that will be patched in later.
      release_assert((SV.u.A->committedVal || SV.u.A->IA->isRootMainCall()) && 
		     "Instruction depends on uncommitted instruction");
      return SV.u.A->committedVal;
    }
  case SHADOWVAL_PTRIDX:
    {
      AllocData* AD = getAllocData(SV);
      return AD->committedVal;
    }
  case SHADOWVAL_FDIDX:
  case SHADOWVAL_FDIDX64:
    {
      FDGlobalState& FDS = pass->fds[SV.u.PtrOrFd.idx];
      return FDS.CommittedVal;
    }
  case SHADOWVAL_CI8:
  case SHADOWVAL_CI16:
  case SHADOWVAL_CI32:
  case SHADOWVAL_CI64:
    return getSingleConstant(SV);
  default:
    release_assert(0 && "Bad SV type");
    llvm_unreachable("Bad SV type");
  }
  
}

// Resolve a symbolic argument to a concrete value usable during commit. If we're committing out of line
// that just means an actual Argument; if we're committing inline it means the concrete value passed to
// the "call", or value-forwarding trickery if our parent hasn't been concretised yet.
Value* InlineAttempt::getArgCommittedValue(ShadowArg* SA, Instruction* insertBefore) {

  return getArgCommittedValue2(SA, 0, insertBefore);

}

Value* InlineAttempt::getArgCommittedValue(ShadowArg* SA, BasicBlock* emitBB) {

  return getArgCommittedValue2(SA, emitBB, 0);

}

Value* InlineAttempt::getArgCommittedValue2(ShadowArg* SA, BasicBlock* emitBB, Instruction* insertBefore) {

  unsigned n = SA->invar->A->getArgNo();

  if(commitsOutOfLine() || !isEnabled()) {

    // Use corresponding argument:
    release_assert(CommitF);
    Function::arg_iterator it = CommitF->arg_begin();
    for(unsigned i = 0; i < n; ++i)
      ++it;

    return &*it;

  }
  else {

    if(!uniqueParent->commitStarted()) {

      // The function outwith this one isn't being committed at this point.
      // Return a forwarding instruction and request that it be patched.
      Value* True = ConstantInt::getTrue(F.getContext());
      Value* UD = UndefValue::get(SA->getType());      
      if(emitBB)
	SA->patchInst = SelectInst::Create(True, UD, UD, "", emitBB);
      else
	SA->patchInst = SelectInst::Create(True, UD, UD, "", insertBefore);
      return SA->patchInst;

    }
    else {

      // Inlined in place -- use the corresponding value of our call instruction.
      // For sharing to work all arg values must match, so just use caller #0.
      return getCommittedValue(Callers[0]->getCallArgOperand(n));

    }

  }

}

BasicBlock* InlineAttempt::getCommittedEntryBlock() {

  return entryBlock;

}

// Get the succIdx'th committed successor of BB, which is complicated when edges branch
// out of a loop or into a region of a function that isn't considered for specialisation.
BasicBlock* PeelIteration::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  // Is this the latch->header edge?
  if(BB->invar->idx == parentPA->L->latchIdx && succIdx == parentPA->L->headerIdx) {

    // Usually this will point to the next iteration's header. The second case tries to
    // cater for committing several specialised iterations followed by a general
    // iteration, but I think at the moment the specialised iterations are discarded in this case
    // (i.e. either the loop is unrolled either totally or not at all)
    if(PeelIteration* PI = getNextIteration())
      return PI->getBB(succIdx)->committedBlocks.front().specBlock;
    else {
      if(iterStatus == IterationStatusFinal) {
	release_assert(pass->assumeEndsAfter(&F, getBBInvar(L->headerIdx)->BB, iterationCount)
		       && "Branch to header in final iteration?");
	markUnreachable = true;
	return 0;
      }
      else
	return parent->getBB(succIdx)->committedBlocks.front().specBlock;
    }

  }

  return IntegrationAttempt::getSuccessorBB(BB, succIdx, markUnreachable);

}

// The tricky case here happens when the user has specified that particular paths
// are not interesting for specialisation and so we want to branch directly
// to an unspecialised variant.
BasicBlock* InlineAttempt::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  if(edgeBranchesToUnspecialisedCode(BB->invar, getBBInvar(succIdx))) {

    if(pass->omitChecks) {
      markUnreachable = true;
      return 0;
    }
    
    release_assert(failedBlocks[succIdx].size());
    return failedBlocks[succIdx].front().first;

  }

  return IntegrationAttempt::getSuccessorBB(BB, succIdx, markUnreachable);

}

// Fetch a successor committed-block for BB. This is tricky when we're entering or leaving loops, which
// means finding an appropriate block in a child or parent context.
BasicBlock* IntegrationAttempt::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  ShadowBBInvar* SuccBBI = getBBInvar(succIdx);

  ShadowBB* SuccBB;
  if((!SuccBBI->naturalScope) || SuccBBI->naturalScope->contains(L))
    SuccBB = getBBFalling(SuccBBI);
  else {

    // Else, BBI is further in than this block: we must be entering exactly one loop.
    // Only enter if we're emitting the loop in its proper scope: otherwise we're
    // writing the residual version of a loop.
    if(BB->invar->outerScope == L) {
      PeelAttempt* PA;
      if((PA = getPeelAttempt(SuccBBI->naturalScope)) && PA->isTerminated() && PA->isEnabled())
	return PA->Iterations[0]->getBB(*SuccBBI)->committedBlocks.front().specBlock;
    }

    // Otherwise loop unexpanded or disabled: jump direct to the residual loop.
    SuccBB = getBB(*SuccBBI);

  }

  if(!SuccBB) {
    markUnreachable = true;
    return 0;
  }
  else {
    return SuccBB->committedBlocks.front().specBlock;
  }

}

// Helpers for above.
ShadowBB* InlineAttempt::getBBFalling2(ShadowBBInvar* BBI) {

  release_assert((!BBI->naturalScope) && "Out of scope in getBBFalling");
  return getBB(*BBI);

}

ShadowBB* PeelIteration::getBBFalling2(ShadowBBInvar* BBI) {

  if(BBI->naturalScope == L)
    return getBB(*BBI);
  else
    return parent->getBBFalling2(BBI);

}

ShadowBB* IntegrationAttempt::getBBFalling(ShadowBBInvar* BBI) {

  if((!L) || L->contains(BBI->naturalScope))
    return getBB(*BBI);
  return getBBFalling2(BBI);
  
}

// Synthesise an appropriate constexpr-cast.
Constant* llvm::getConstAsType(Constant* C, Type* Ty) {

  release_assert(CastInst::isCastable(C->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(C, false, Ty, false);
  return ConstantExpr::getCast(Op, C, Ty);

}

// Synthesise an appropriate cast instruction.
Value* llvm::getValAsType(Value* V, Type* Ty, Instruction* insertBefore) {

  if(Ty == V->getType())
    return V;

  if(isa<Constant>(V))
    return getConstAsType(cast<Constant>(V), Ty);

  release_assert(CastInst::isCastable(V->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(V, false, Ty, false);
  return CastInst::Create(Op, V, Ty, "speccast", insertBefore);

}

Value* llvm::getValAsType(Value* V, Type* Ty, BasicBlock* insertAtEnd) {

  if(Ty == V->getType())
    return V;

  if(isa<Constant>(V))
    return getConstAsType(cast<Constant>(V), Ty);

  release_assert(CastInst::isCastable(V->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(V, false, Ty, false);
  return CastInst::Create(Op, V, Ty, VerboseNames ? "speccast" : "", insertAtEnd);

}

// Add an empty phi node to emitBB.
PHINode* llvm::makePHI(Type* Ty, const Twine& Name, BasicBlock* emitBB) {

  // Manually check for existing non-PHI instructions because BB->getFirstNonPHI assumes a finished block

  BasicBlock::iterator it = emitBB->begin();
  while(it != emitBB->end() && isa<PHINode>(it))
    ++it;
  
  if(it != emitBB->end())
    return PHINode::Create(Ty, 0, Name, &*it);
  else
    return PHINode::Create(Ty, 0, Name, emitBB);

}

// Make a phi node corresponding to specialised instruction I, committing to emitBB, in the special loop-header case.
void PeelIteration::emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  // Special case: emitting own header PHI. Emit a unary PHI drawing on either the preheader
  // argument or the latch one.

  PHINode* PN = cast_inst<PHINode>(I);

  if(BB->invar->idx == parentPA->L->headerIdx) {
    
    ShadowValue SourceV = getLoopHeaderForwardedOperand(I);

    PHINode* NewPN;
    I->committedVal = NewPN = makePHI(I->invar->I->getType(), VerboseNames ? "header" : "", emitBB);
    ShadowBB* SourceBB;

    if(iterationCount == 0) {

      SourceBB = parent->getBB(parentPA->L->preheaderIdx);

    }
    else {

      PeelIteration* prevIter = parentPA->Iterations[iterationCount-1];
      SourceBB = prevIter->getBB(parentPA->L->latchIdx);

    }

    // Emit any necessary casts into the predecessor block.
    Value* PHIOp = getValAsType(getCommittedValue(SourceV), PN->getType(), SourceBB->committedBlocks.back().specBlock->getTerminator());
    NewPN->addIncoming(PHIOp, SourceBB->committedBlocks.back().specBlock);
    return;

  }

  IntegrationAttempt::emitPHINode(BB, I, emitBB);

}

// Gather operands for loop-exit-phi SI. Only phi nodes need to do this because
// the source program is required in LCSSA form. ops gathers arguments,
// and BBs if supplied gathers predecessor blocks.
void IntegrationAttempt::getCommittedExitPHIOperands(ShadowInstruction* SI, uint32_t valOpIdx, SmallVector<ShadowValue, 1>& ops, SmallVector<ShadowBB*, 1>* BBs) {

  uint32_t blockIdx = SI->invar->operandBBs[valOpIdx];

  assert(blockIdx != INVALID_BLOCK_IDX);

  ShadowBBInvar* OpBB = getBBInvar(blockIdx);

  // SI->parent->invar->scope != L checks if we're emitting a PHI for a residual loop body.
  if(SI->parent->invar->naturalScope != L) {

    // Arg is local (can't be lower or this is a header phi)
    if(!edgeIsDead(OpBB, SI->invar->parent)) {
      ops.push_back(SI->getOperand(valOpIdx));
      if(BBs) {
	ShadowBB* NewBB = getBBFalling(OpBB);
	release_assert(NewBB);
	BBs->push_back(NewBB);
      }
    }

    return;

  }

  getExitPHIOperands(SI, valOpIdx, ops, BBs);


}

// Populate phi node NewPN corresponding to I.
void IntegrationAttempt::populatePHINode(ShadowBB* BB, ShadowInstruction* I, PHINode* NewPN) {

  // There used to be a case here handling loops with one or more specialised iterations
  // but which were ultimately unbounded. I scrapped that because it's too complicated
  // handling the intermediate case between straightened and fully general loops,
  // but it's in git if you need it.

  // Emit a normal PHI; all arguments have already been prepared.
  for(uint32_t i = 0, ilim = I->invar->operandIdxs.size(); i != ilim; i++) {
      
    SmallVector<ShadowValue, 1> predValues;
    SmallVector<ShadowBB*, 1> predBBs;
    getCommittedExitPHIOperands(I, i, predValues, &predBBs);

    for(uint32_t j = 0; j < predValues.size(); ++j) {
      Value* PHIOp = getValAsType(getCommittedValue(predValues[j]), NewPN->getType(), predBBs[j]->committedBlocks.back().specBlock->getTerminator());
      NewPN->addIncoming(PHIOp, predBBs[j]->committedBlocks.back().specBlock);
    }

  }

}

// Make a phi node corresponding to specialised instruction I, committing to emitBB.
void IntegrationAttempt::emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  PHINode* NewPN;
  I->committedVal = NewPN = makePHI(I->invar->I->getType(), "", emitBB);

  // Special case: emitting the header PHI of a residualised loop.
  // Make an empty node for the time being; this will be revisted once the loop body is emitted
  if(BB->invar->naturalScope && BB->invar->naturalScope->headerIdx == BB->invar->idx)
    return;

  populatePHINode(BB, I, NewPN);

}

// After writing a loop, attach the latch->header phi operands.
void IntegrationAttempt::fixupHeaderPHIs(ShadowBB* BB) {

  uint32_t i;
  for(i = 0; i < BB->insts.size() && inst_is<PHINode>(&(BB->insts[i])); ++i) {
    if((!BB->insts[i].committedVal) || !isa<PHINode>(BB->insts[i].committedVal))
      continue;
    populatePHINode(BB, &(BB->insts[i]), cast<PHINode>(BB->insts[i].committedVal));
  }

}

// Get the committed version of I's idx'th operand. If we're returning an unspecialised basic block because I is branching
// out of the user-directed specialisation region, and the user has requested verbose diagnostics in this case, failValue and failBlock
// are populated with the branch target and perhaps switch value by which we left specialised code.
Value* IntegrationAttempt::getCommittedValueOrBlock(ShadowInstruction* I, uint32_t idx, ConstantInt*& failValue, BasicBlock*& failBlock) {

  ShadowBB* BB = I->parent;

  if(I->invar->operandIdxs[idx].instIdx == INVALID_INSTRUCTION_IDX && 
     I->invar->operandIdxs[idx].blockIdx != INVALID_BLOCK_IDX) {

    // Argument is a BB.
    bool markUnreachable = false;
    uint32_t succIdx = I->invar->operandIdxs[idx].blockIdx;
    BasicBlock* SBB = getSuccessorBB(BB, succIdx, markUnreachable);

    release_assert((SBB || markUnreachable) && "Failed to get successor BB (2)");

    if(markUnreachable) {

      // Create an unreachable BB to branch to:
      BasicBlock* UBB = createBasicBlock(I->invar->I->getContext(), VerboseNames ? "synth-unreachable" : "", 
					 getFunctionRoot()->CommitF, false, true);
      // The following is only currently needed when running with int-omit-checks: exceptions lead
      // to immediate death, but we still need a landingpad to produce a sane module.
      if(LandingPadInst* LPI = dyn_cast<LandingPadInst>(getBBInvar(succIdx)->BB->getFirstNonPHI())) {

	Instruction* NewLPI = LPI->clone();
	// No remapping necessary, as LP arg is just a constant pointer to a personality function
	UBB->getInstList().push_back(NewLPI);

      }
	
      new UnreachableInst(UBB->getContext(), UBB);
      return UBB;

    }
    else {
	  
      ShadowBBInvar* TargetBBI = getBBInvar(I->invar->operandIdxs[idx].blockIdx);

      if(pass->verbosePCs && edgeBranchesToUnspecialisedCode(BB->invar, TargetBBI) && !isExceptionEdge(BB->invar, TargetBBI)) {

	if(inst_is<SwitchInst>(I)) {

	  if(idx == 1) {
	    // Default target
	    failValue = 0;
	  }
	  else {
	    // Switch value comes before this target block.
	    failValue = cast<ConstantInt>(getSingleConstant(I->getOperand(idx - 1)));
	  }

	}
	else {

	  failValue = 0;

	}
	      
	failBlock = SBB;

	BasicBlock* breakBlock = BB->committedBlocks.back().breakBlock;
	release_assert(breakBlock && "Should have a break block");
	return breakBlock;

      }
      else {

	return SBB;

      }

    }

  }
  else { 

    ShadowValue op = I->getOperand(idx);
    Value* opV = getCommittedValue(op);
    return opV;

  }

}

// Synthesise I, a terminator instruction for BB, writing to emitBB. This is a little complicated
// when we're committing a return instruction out-of-line or we need to deal with branches to
// unspecialised code.
void IntegrationAttempt::emitTerminator(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  if(inst_is<UnreachableInst>(I) || inst_is<ResumeInst>(I)) {

    emitInst(BB, I, emitBB);
    return;
    
  }

  if(inst_is<ReturnInst>(I)) {

    InlineAttempt* IA = getFunctionRoot();

    if(!IA->returnBlock) {

      // This is an out-of-line commit, so CommitF should be decided.
      release_assert(getFunctionRoot()->CommitF);

      // Return undef if we know the value won't be used.
      Value* retVal;
      if((!F.getFunctionType()->getReturnType()->isVoidTy()) && I->dieStatus != INSTSTATUS_ALIVE)
	retVal = UndefValue::get(F.getReturnType());
      else if(F.getFunctionType()->getReturnType()->isVoidTy())
	retVal = 0;
      else
	retVal = getCommittedValue(I->getOperand(0));

      // If it's possible for specialisation assumptions to fail here or in a child context, we need to return
      // an extra flag indicating whether or not this has happened. Here we always return 'true' indicating
      // to continue on the specialised path; in ConditionalSpec.cpp we can see the opposite case being synthesised.
      if(IA->hasFailedReturnPath() && !IA->isRootMainCall()) {

	Constant* retFlag = ConstantInt::getTrue(emitBB->getContext());	
	if(!retVal) {

	  // Function was void before; just return true.
	  retVal = retFlag;
	  
	}
	else {

	  // Function was non-void; return { retval, true }
	  StructType* retType = cast<StructType>(getFunctionRoot()->CommitF->getFunctionType()->getReturnType());
	  Type* normalRet = retType->getElementType(0);
	  Constant* undefRet = UndefValue::get(normalRet);
	  // Create { undef, true }
	  Value* aggTemplate = ConstantStruct::get(retType, {undefRet, retFlag});
	  // Return { retval, true }
	  retVal = InsertValueInst::Create(aggTemplate, retVal, 0, VerboseNames ? "success_ret" : "", emitBB);

	}

      }

      // If emitting runtime debug information, report success.
      if(pass->verbosePCs && (!L) && getFunctionRoot()->isRootMainCall()) {

	std::string msg;
	{
	  raw_string_ostream RSO(msg);
	  RSO << "Successfully exiting specialised function " << F.getName() << "\n";
	}

	escapePercent(msg);
	emitRuntimePrint(emitBB, msg, 0);

      }

      ReturnInst::Create(emitBB->getContext(), retVal, emitBB);

    }
    else {

      // This is a return instruction but we're committing inline. We should have a target phi node
      // to give the 'returned' value. No need for the success flag dealt with above, as failed paths
      // have a dedicated return block separate from this one.
      
      // Branch to the exit block
      Instruction* BI = BranchInst::Create(IA->returnBlock, emitBB);

      if(IA->returnPHI && I->dieStatus == INSTSTATUS_ALIVE) {
	Value* PHIVal = getValAsType(getCommittedValue(I->getOperand(0)), F.getFunctionType()->getReturnType(), BI);
	IA->returnPHI->addIncoming(PHIVal, BB->committedBlocks.back().specBlock);
      }

    }

    return;

  }

  // Do we know where this terminator will go?
  uint32_t knownSucc = 0xffffffff;
  for(uint32_t i = 0; i < BB->invar->succIdxs.size(); ++i) {

    if(BB->succsAlive[i]) {

      if(pass->omitChecks && edgeBranchesToUnspecialisedCode(BB->invar, getBBInvar(BB->invar->succIdxs[i])))
	continue;

      if(knownSucc == 0xffffffff)
	knownSucc = BB->invar->succIdxs[i];
      else if(knownSucc == BB->invar->succIdxs[i])
	continue;
      else {

	knownSucc = 0xffffffff;
	break;

      }

    }

  }

  // If we know one true successor:
  if(knownSucc != 0xffffffff) {

    // Emit uncond branch
    bool markUnreachable = false;
    BasicBlock* SBB = getSuccessorBB(BB, knownSucc, markUnreachable);
    release_assert((SBB || markUnreachable) && "Failed to get successor BB");
    if(markUnreachable)
      new UnreachableInst(emitBB->getContext(), emitBB);
    else
      BranchInst::Create(SBB, emitBB);

  }
  else {

    // Clone existing branch/switch
    release_assert((inst_is<SwitchInst>(I) || inst_is<BranchInst>(I)) && "Unsupported terminator type");
    
    SmallVector<std::pair<ConstantInt*, BasicBlock*>, 1> breakSuccessors;

    Instruction* newTerm = I->invar->I->clone();
    emitBB->getInstList().push_back(newTerm);

    BasicBlock* defaultSwitchTarget = 0;
    
    // Like emitInst, but can emit BBs.
    for(uint32_t i = 0; i < I->getNumOperands(); ++i) {

      // switchVal and block are only used to generate runtime debugging prints.
      ConstantInt* switchVal = 0;
      BasicBlock* switchBlock = 0;
      Value* replVal = getCommittedValueOrBlock(I, i, switchVal, switchBlock);
      release_assert(replVal);
      newTerm->setOperand(i, replVal);

      if(switchVal || switchBlock)
	breakSuccessors.push_back(std::make_pair(switchVal, switchBlock));
      if(inst_is<SwitchInst>(I) && i == 1)
	defaultSwitchTarget = cast<BasicBlock>(replVal);

    }

    if(!breakSuccessors.empty()) {

      // If we're going to report departing specialised code at a switch instruction,
      // make a block that reports the failure and then switches again to reach unspecialised code.
      // This path should never handle invoke instructions, and so this treatment of
      // failed paths is acceptable.

      BasicBlock* breakBlock = BB->committedBlocks.back().breakBlock;

      std::string msg;
      {
	raw_string_ostream RSO(msg);
	RSO << "Left via an ignored edge, to block " << breakBlock->getName() << "\n";
      }

      escapePercent(msg);
      emitRuntimePrint(breakBlock, msg, 0);

      if(breakSuccessors.size() == 1) {

	BranchInst::Create(breakSuccessors[0].second, breakBlock);

      }
      else {

	release_assert(inst_is<SwitchInst>(I));
	
	// If the default does not break, use the first target as a default.
	if(!defaultSwitchTarget)
	  defaultSwitchTarget = breakSuccessors[0].second;

	unsigned nCases = defaultSwitchTarget == 0 ? breakSuccessors.size() : breakSuccessors.size() - 1;

	SwitchInst* NewSI = SwitchInst::Create(newTerm->getOperand(0), defaultSwitchTarget,
					       nCases, breakBlock);

	for(uint32_t i = 0, ilim = breakSuccessors.size(); i != ilim; ++i) {

	  // Skip default case.
	  if(!breakSuccessors[i].second)
	    continue;
	  NewSI->addCase(breakSuccessors[i].first, breakSuccessors[i].second);
	  
	}

      }

    }
    
  }

}

// Create a constant global containing the bytes read by this ReadFile call.
static GlobalVariable* getFileBytesGlobal(ReadFile& RF) {

  std::vector<Constant*> constBytes;
  std::string errors;
  LLVMContext& Context = GInt8->getContext();
  if(!getFileBytes(RF.name, RF.incomingOffset, RF.readSize, constBytes, Context, errors)) {

    errs() << "Failed to read file " << RF.name << " in commit\n";
    exit(1);

  }

  ArrayType* ArrType = ArrayType::get(IntegerType::get(Context, 8), constBytes.size());
  Constant* ByteArray = ConstantArray::get(ArrType, constBytes);

  // Create a const global for the array:

  return new GlobalVariable(*getGlobalModule(), ArrType, true, GlobalValue::InternalLinkage, ByteArray, "");

}

// Can't just use getOrInsertFunction as it ignores functions with local/private linkage.
static Constant* getOrInsertLocalFunction(StringRef Name, FunctionType* FT) {

  Module* M = getGlobalModule();
  if(Function* F = M->getFunction(Name))
    return F;
  return cast<Constant>(M->getOrInsertFunction(Name, FT).getCallee());

}

// Emit an lseek64 call to reposition a given FD.
static void emitSeekTo(Value* FD, uint64_t Offset, BasicBlock* emitBB) {

  LLVMContext& Context = FD->getContext();

  Type* Int64Ty = IntegerType::get(Context, 64);
  Constant* NewOffset = ConstantInt::get(Int64Ty, Offset);
  Type* Int32Ty = IntegerType::get(Context, 32);
  Constant* SeekSet = ConstantInt::get(Int32Ty, SEEK_SET);

  Type* ArgTypes[3] = { Int32Ty, Int64Ty, Int32Ty };
  FunctionType* FT = FunctionType::get(/* ret = */ Int64Ty, ArrayRef<Type*>(ArgTypes, 3), false);

  Constant* SeekFn = getOrInsertLocalFunction("lseek64", FT);

  Value* CallArgs[] = { FD, NewOffset, SeekSet };

  CallInst* SeekC = CallInst::Create(SeekFn, ArrayRef<Value*>(CallArgs, 3), "", emitBB);
  if(Function* SeekF = dyn_cast<Function>(SeekFn))
    SeekC->setCallingConv(SeekF->getCallingConv());

}

// Emit a syscall instruction. It might be resolved down to a no-op, or might require repositioning with lseek64 before execution.
bool IntegrationAttempt::emitVFSCall(ShadowBB* BB, ShadowInstruction* I, SmallVector<CommittedBlock, 1>::iterator& emitBBIter) {

  BasicBlock* emitBB = emitBBIter->specBlock;

  // No VFS invokes.
  CallInst* CI = dyn_cast_inst<CallInst>(I);
  if(!CI)
    return false;

  {
    DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(I);
    if(it != pass->resolvedReadCalls.end()) {

      // This is a read() call that was successfully executed at specialisation time.
      LLVMContext& Context = CI->getContext();

      if((I->needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD || 
	  I->needsRuntimeCheck == RUNTIME_CHECK_READ_MEMCMP) 
	 && !pass->omitChecks) {

	// We need to check the read result is still valid, either with straightforward memcmp
	// or by checking with the watch daemon.
	BasicBlock* breakBlock = emitBBIter->breakBlock;
	Value* CheckTest;

	if(it->second.isFifo) {

	  // As a fifo, we must (a) do the read as usual, then (b) use memcmp to check
	  // that the results are the way we expect.

	  // Emit the read as-is
	  CallInst* readInst = cast<CallInst>(emitInst(BB, I, emitBB));

	  // Build a memcmp check. Always tested this with images already linked
	  // to a libc implementation, but hopefully this produces the right memcmp
	  // signature to acquire a dynamically-linked version too.
	  Value* readBuffer = readInst->getArgOperand(1);
	  if(readBuffer->getType() != GInt8Ptr)
	    readBuffer = new BitCastInst(readBuffer, GInt8Ptr, VerboseNames ? "readcast" : "", emitBB);

	  Value* checkBuffer = getFileBytesGlobal(it->second);
	  if(checkBuffer->getType() != GInt8Ptr)
	    checkBuffer = new BitCastInst(checkBuffer, GInt8Ptr, VerboseNames ? "readcast" : "", emitBB);

	  Constant* MemcmpSize = ConstantInt::get(GInt64, it->second.readSize);

	  Value *MemCmpFn = cast<Constant>(F.getParent()->getOrInsertFunction("memcmp", GInt32, GInt8Ptr, GInt8Ptr, GInt64, (Type*)0).getCallee());
	  
	  Value *CallArgs[] = { readBuffer, checkBuffer, MemcmpSize };
	  Instruction* ReadMemcmp = CallInst::Create(MemCmpFn, ArrayRef<Value*>(CallArgs, 3), "", emitBB);
	  // CheckTest must be true on failure, so we test memcmp(...) != 0
	  
	  Constant* Zero32 = Constant::getNullValue(GInt32);
	  CheckTest = new ICmpInst(*emitBB, CmpInst::ICMP_NE, ReadMemcmp, Zero32);

	  DenseMap<ShadowInstruction*, TrackedStore*>::iterator findit = pass->trackedStores.find(I);
	  if(findit != pass->trackedStores.end()) {

	    findit->second->isCommitted = true;

	  }
	  
	}
	else {

	  // Read from a regular file.
	  // Emit a check that file specialisations are still admissible:
	  Type* Int32Ty = IntegerType::get(Context, 32);
	  Constant* CheckFn = cast<Constant>(F.getParent()->getOrInsertFunction("lliowd_ok", Int32Ty).getCallee());
	  Value* CheckResult = CallInst::Create(CheckFn, ArrayRef<Value*>(), "readcheck", emitBB);
      
	  Constant* Zero32 = Constant::getNullValue(Int32Ty);
	  CheckTest = new ICmpInst(*emitBB, CmpInst::ICMP_EQ, CheckResult, Zero32);

	  // Seek to the right position in the break block, so that unspecialised
	  // code finds the file pointer where it expects to.
	  emitSeekTo(getCommittedValue(I->getCallArgOperand(0)), 
		     it->second.incomingOffset, breakBlock);

	}
      
	// Print failure notice if building a verbose specialisation:
	if(pass->verbosePCs) {
	
	  std::string message;
	  {
	    raw_string_ostream RSO(message);
	    RSO << "Denied permission to use specialised files reading " << it->second.name << " in " << emitBB->getName() << "\n";
	  }
	
	  emitRuntimePrint(breakBlock, message, 0);
	
	}

	// A checked read instruction terminates this block. Emit on-success code to the next BB:
	++emitBBIter;

	// Branch to the real read instruction on failure for lliowd checks, or the instruction after otherwise
	// (in that case the read has already been executed)
	uint32_t targetInst = it->second.isFifo ? I->invar->idx + 1 : I->invar->idx;
	BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, targetInst);
	BasicBlock* successTarget = emitBBIter->specBlock;

	release_assert(failTarget && successTarget && CheckTest);
      
	if(breakBlock != emitBB) {

	  BranchInst::Create(breakBlock, successTarget, CheckTest, emitBB);
	  BranchInst::Create(failTarget, breakBlock);

	}
	else {

	  BranchInst::Create(failTarget, successTarget, CheckTest, emitBB);

	}
      
	// Emit the rest of the read implementation in the next specialised block:
	emitBB = successTarget;

      }

      // Insert a seek call if that turns out to be necessary (i.e. if that FD may be subsequently
      // used without an intervening SEEK_SET)
      if(it->second.needsSeek) {
	
	emitSeekTo(getCommittedValue(I->getCallArgOperand(0)), 
		   it->second.incomingOffset + it->second.readSize, emitBB);
	  
      }

      // If the read may be used, copy from the global containing the file's bytes into the given buffer
      // (i.e. a read() becomes a memcpy from a constant global).
      // If it's a read from a fifo then the copy was emitted *before* the check.

      if(it->second.readSize > 0 && 
	 (!(it->second.isFifo && !pass->omitChecks)) && 
	 !(I->dieStatus & INSTSTATUS_UNUSED_WRITER)) {
	
	GlobalVariable *ArrayGlobal = getFileBytesGlobal(it->second);

	Type* Int64Ty = IntegerType::get(Context, 64);
	Type* VoidPtrTy = Type::getInt8PtrTy(Context);

	Constant* ZeroIdx = ConstantInt::get(Int64Ty, 0);
	Constant* Idxs[2] = {ZeroIdx, ZeroIdx};
	Constant* CopySource = ConstantExpr::getGetElementPtr(0, ArrayGlobal, Idxs, 2);
      
	Constant* MemcpySize = ConstantInt::get(Int64Ty, it->second.readSize);

	Type *Tys[3] = {VoidPtrTy, VoidPtrTy, Int64Ty};
	Function *MemCpyFn = Intrinsic::getDeclaration(F.getParent(),
						       Intrinsic::memcpy, 
						       ArrayRef<Type*>(Tys, 3));
	Value *ReadBuffer = getCommittedValue(I->getCallArgOperand(1));
	release_assert(ReadBuffer && "Committing read atop dead buffer?");
	Value *DestCast = new BitCastInst(getCommittedValue(I->getCallArgOperand(1)), VoidPtrTy, VerboseNames ? "readcast" : "", emitBB);

	Value *CallArgs[] = {
	  DestCast, CopySource, MemcpySize,
	  ConstantInt::get(Type::getInt32Ty(Context), 1),
	  ConstantInt::get(Type::getInt1Ty(Context), 0)
	};
	
	Instruction* ReadMemcpy = CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", emitBB);

	DenseMap<ShadowInstruction*, TrackedStore*>::iterator findit = pass->trackedStores.find(I);
	if(findit != pass->trackedStores.end()) {

	  findit->second->isCommitted = true;
	  findit->second->committedInsts = new WeakVH[1];
	  findit->second->committedInsts[0] = ReadMemcpy;
	  findit->second->nCommittedInsts = 1;

	}
	
      }

      return true;

    }

  }

  // End of read call handling.
  // seek calls:
  
  {
    
    DenseMap<ShadowInstruction*, SeekFile>::iterator it = pass->resolvedSeekCalls.find(I);
    if(it != pass->resolvedSeekCalls.end()) {

      // MayDelete means this seek is redundant (every instruction that will read the file pointer in the future has been folded away)
      if(!it->second.MayDelete)
	emitInst(BB, I, emitBB);

      return true;

    }

  }

  Function* CalledF = getCalledFunction(I);

  // Check whether it's valid to assume stat returns zero for the given file:
  
  if((!pass->omitChecks) && I->needsRuntimeCheck == RUNTIME_CHECK_READ_LLIOWD && 
     (CalledF->getName() == "stat" || CalledF->getName() == "fstat")) {

    LLVMContext& Context = emitBB->getContext();

    // Emit an lliowd_ok check, and if it fails branch to the real stat instruction.
    Type* Int32Ty = IntegerType::get(Context, 32);
    Constant* CheckFn = cast<Constant>(F.getParent()->getOrInsertFunction("lliowd_ok", Int32Ty).getCallee());
    Value* CheckResult = CallInst::Create(CheckFn, ArrayRef<Value*>(), VerboseNames ? "readcheck" : "", emitBB);
	
    Constant* Zero32 = Constant::getNullValue(Int32Ty);
    Value* CheckTest = new ICmpInst(*emitBB, CmpInst::ICMP_EQ, CheckResult, Zero32);

    BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, I->invar->idx);

    // Print failure notice if building a verbose specialisation:
    if(pass->verbosePCs) {

      std::string message;
      {
	raw_string_ostream RSO(message);
	RSO << "Denied permission to use specialised files on (f)stat in " << emitBB->getName() << "\n";
      }

      emitRuntimePrint(emitBBIter->breakBlock, message, 0);

      BranchInst::Create(failTarget, emitBBIter->breakBlock);
      failTarget = emitBBIter->breakBlock;

    }
	
    ++emitBBIter;

    // Branch to the real read instruction on failure:
    BasicBlock* successTarget = emitBBIter->specBlock;
    
    release_assert(successTarget && failTarget && CheckTest);
    BranchInst::Create(failTarget, successTarget, CheckTest, emitBB);

    return true;
    
  }

  // Neither read nor seek nor stat (or any of those which couldn't be specialised?)
  return false;

}

// Get the basic block that follows from an 'invoke' on the non-exceptional path.
BasicBlock* IntegrationAttempt::getInvokeNormalSuccessor(ShadowInstruction* I, bool& toCheckBlock) {

  toCheckBlock = false;

  InlineAttempt* IA;

  // An invoke's normal return path should go to special block added to the end of its parent's
  // committedBlock list to perform a test if necessary.
  // This might be because its return value should be checked, or because it has a failed return path.
  // If no check is needed, simply branch to its ordinary successor.
  // This is a little trickier than a normal call because invoke is also a terminator.

  if(requiresRuntimeCheck(ShadowValue(I), false))
    toCheckBlock = true;
  else if((IA = getInlineAttempt(I)) && IA->hasFailedReturnPath())
    toCheckBlock = true;

  if(toCheckBlock)
    return I->parent->committedBlocks.back().specBlock;
  else {

    ConstantInt* ignFailValue = 0;
    BasicBlock* failBlock = 0;

    Value* opV = getCommittedValueOrBlock(I, I->getNumOperands() - 2, ignFailValue, failBlock);
    release_assert(opV);

    if(failBlock)
	release_assert(0 && "Case not covered yet: invoke instruction with ignored normal return edge");

    return cast<BasicBlock>(opV);

  }

}

// Synthesise call instruction I into *emitBBIter. Adjust emitBBIter to point to wherever the call's successor instruction
// should be emitted (i.e. leave it alone if the call was inlined straightforwardly, or bump it otherwise).
void IntegrationAttempt::emitCall(ShadowBB* BB, ShadowInstruction* I, SmallVector<CommittedBlock, 1>::iterator& emitBBIter) {

  BasicBlock* emitBB = emitBBIter->specBlock;

  if(InlineAttempt* IA = getInlineAttempt(I)) {

    if(IA->isEnabled()) {

      if(!IA->instructionsCommitted) {

	IA->activeCaller = I;
	IA->commitArgsAndInstructions();
	IA->instructionsCommitted = true;

      }

      if(!IA->commitsOutOfLine()) {

	// Commit will have written blocks in the same residual function as this context.
	
	// Branch from the current write BB to the call's entry block:
	BranchInst::Create(IA->getCommittedEntryBlock(), emitBB);

	// Take the return PHI (or lack thereof) as this instruction's committed value.
	I->committedVal = IA->returnPHI;

	// Emit further instructions in this ShadowBB to the successor block:
	++emitBBIter;
	release_assert(emitBBIter->specBlock == IA->returnBlock);
	
      }
      else {

	// Commit will have written to a new residual function.
	
	FunctionType* FType = IA->F.getFunctionType();

	// Build a call to IA->CommitF with some parameters stubbed out (replaced with undef)
	// if not required.

	ImmutableCallSite OldCI(I->invar->I);
	AttributeList attrs = OldCI.getAttributes();
	
	std::vector<Value*> Args;

	uint32_t ilim;
	if(FType->isVarArg())
	  ilim = OldCI.arg_size();
	else
	  ilim = FType->getNumParams();

	for(uint32_t i = 0; i != ilim; ++i) {
	    
	  Type* needTy;
	  if(i < FType->getNumParams()) {
	    // Normal argument: cast to target function type.
	    needTy = FType->getParamType(i);
	  }
	  else {
	    // Vararg: cast to old callinst arg type.
	    needTy = OldCI.getArgument(i)->getType();
	  }
	  
	  Value* opV;
	  if(IA->argShadows[i].dieStatus != INSTSTATUS_ALIVE)
	    opV = UndefValue::get(needTy);
	  else {
	    ShadowValue op = I->getCallArgOperand(i);
	    opV = getCommittedValue(op);
	  }

	  Args.push_back(getValAsType(opV, needTy, emitBB));

	}

	release_assert(IA->CommitF);
	Instruction* NewI;

	BasicBlock* invokeNormalDest = 0;
	bool advanceCBIter;

	if(inst_is<InvokeInst>(I)) {

	  // Note that the iterator is bumped forwards, but we keep emitBB as-is for now
	  // to emit the call or invoke into the old block.
	  invokeNormalDest = getInvokeNormalSuccessor(I, advanceCBIter);
	  if(advanceCBIter)
	    ++emitBBIter;

	}

	if(inst_is<CallInst>(I) || (inst_is<InvokeInst>(I) && !BB->succsAlive[1])) {

	  // A normal call or an invoke that cannot throw.
	  
	  NewI = CallInst::Create(IA->CommitF, Args, "", emitBB);

	  if(inst_is<InvokeInst>(I)) {
	    // Invoke that becomes a call because it cannot throw
	    BranchInst::Create(invokeNormalDest, emitBB);
	  }

	}
	else {

	  // Normal invoke that can throw
	  BasicBlock* exnBlock = getFunctionRoot()->getSubBlockForInst(BB->invar->succIdxs[1], 0);
	  NewI = InvokeInst::Create(IA->CommitF, invokeNormalDest, exnBlock, Args, "", emitBB);

	}

	// Bring emitBB back into sync with the iterator if we bumped it above getting an invoke
	// instruction's destination. This means that any checks needed by that invoke
	// will be emitted to this block.
	emitBB = emitBBIter->specBlock;

	CallSite NewCI(NewI);
	 
	NewCI.setCallingConv(OldCI.getCallingConv());
	NewCI.setAttributes(attrs);
	
	if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {
	  if(CI->isTailCall())
	    cast<CallInst>(NewI)->setTailCall();
	}

	NewI->setDebugLoc(I->invar->I->getDebugLoc());
	  
	I->committedVal = NewI;

	if(IA->hasFailedReturnPath()) {

	  // This out-of-line call might fail. If it did, branch to unspecialised code.
	  // Retrieve the boolean (or struct-with-boolean) it returned to indicate whether we should break to unspec code now:

	  Value* CallFailed;
	  if(IA->F.getFunctionType()->getReturnType()->isVoidTy()) {

	    CallFailed = NewI;

	  }
	  else {

	    CallFailed = ExtractValueInst::Create(NewI, ArrayRef<unsigned>(1), VerboseNames ? "retfailflag" : "", emitBB);
	    I->committedVal = ExtractValueInst::Create(NewI, ArrayRef<unsigned>(0), VerboseNames ? "ret" : "", emitBB);
	    
	  }

	  BasicBlock* successTarget;
	  BasicBlock* failTarget;

	  if(inst_is<CallInst>(I)) {

	    // If the call result isn't as expected, branch to the instruction after in unspecialised code.
	    ++emitBBIter;
	    successTarget = emitBBIter->specBlock; 
	    failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, I->invar->idx + 1);

	  }
	  else {

	    // Invoke is already a terminator -- branch chooses between the specialised or unspecialised successors.
	    // emititer already bumped above.
	    bool markUnreachable = false;
	    successTarget = getSuccessorBB(BB, BB->invar->succIdxs[0], markUnreachable);
	    if(markUnreachable) {
	      successTarget = createBasicBlock(emitBB->getContext(), 
					       VerboseNames ? "invoke-unreachable" : "", 
					       emitBB->getParent(), false, true);
	      new UnreachableInst(emitBB->getContext(), successTarget);
	    }

	    failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->succIdxs[0], 0);

	  }

	  release_assert(successTarget && failTarget && CallFailed);
	  BranchInst::Create(successTarget, failTarget, CallFailed, emitBB);

	}

      } // End of inline / out-of-line if/else.
   
      if(!IA->commitsOutOfLine()) {
	
	if(IA->emittedAlloca) {

	  // If the residual, inline function allocates stack memory, bound its lifetime
	  // with stacksave/restore.
	  // Sticking its allocas at top of function would create a huge stack frame.

	  Module *M = getGlobalModule();

	  Function *StackSave = Intrinsic::getDeclaration(M, Intrinsic::stacksave);
	  Function *StackRestore=Intrinsic::getDeclaration(M, Intrinsic::stackrestore);

	  // Save on entry
	  BasicBlock* FunctionEntry = IA->getCommittedEntryBlock();
	  BasicBlock* FunctionPred = FunctionEntry->getSinglePredecessor();
	  release_assert(FunctionPred && "No unique entry to inlined function?");
	  CallInst* SavedPtr = CallInst::Create(StackSave, VerboseNames ? "savedstack" : "", FunctionPred->getTerminator());

	  // Restore on successful return
	  CallInst::Create(StackRestore, SavedPtr, "", IA->returnBlock);

	  // Restore on failed 
	  if(IA->failedReturnBlock) {
	    CallInst::Create(StackRestore, SavedPtr, "", IA->failedReturnBlock->getFirstNonPHI());
	    (*getFunctionRoot()->failedBlockMap)[SavedPtr] = SavedPtr;
	  }

	}

	// No live return paths?
	if(IA->returnPHI && IA->returnPHI->getNumIncomingValues() == 0) {
	  IA->returnPHI->eraseFromParent();
	  IA->returnPHI = 0;
	  I->committedVal = UndefValue::get(IA->F.getFunctionType()->getReturnType());
	}

	// If it's an invoke instruction then this is the terminator!
	// If it commits out of line, then it doesn't unwind but might fail (deviate from specialisation
	// assumptions). The successful and failed return blocks should branch to the invoke's
	// non-exception successor.

	if(inst_is<InvokeInst>(I)) {
	  
	  bool markUnreachable = false;
	  BasicBlock* SBB = getSuccessorBB(BB, BB->invar->succIdxs[0], markUnreachable);
	  if(markUnreachable)
	    new UnreachableInst(IA->returnBlock->getContext(), IA->returnBlock);
	  else
	    BranchInst::Create(SBB, IA->returnBlock);
	  
	  if(IA->failedReturnBlock) {

	    BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->succIdxs[0], 0);
	    BranchInst::Create(failTarget, IA->failedReturnBlock);

	  }

	}
	
      } // End of if-commits-inline

      return;
    
    } // End of if-function-context-enabled

  } // End of if-function-has-specialisation

  // Is this a specialised VFS syscall?
  if(emitVFSCall(BB, I, emitBBIter))
    return;

  // Print a warning when leaving specialised code via an exception.
  // Hopefully the call always has the right attribute combination:

  if(pass->verbosePCs && !getInlineAttempt(I)) {

    Function* CalledF = getCalledFunction(I);
    if(CalledF && CalledF->doesNotReturn() && !CalledF->doesNotThrow()) {

      std::string msg;
      {
	raw_string_ostream RSO(msg);
	RSO << "Leaving specialised code by entering noreturn throws function " << CalledF->getName() << "\n";
      }

      emitRuntimePrint(emitBB, msg, 0);

    }

  }

  // Unexpanded call, emit it as a normal instruction.
  Instruction* NewI = emitInst(BB, I, emitBB);

  if(InvokeInst* NewInvoke = dyn_cast<InvokeInst>(NewI)) {

    // If an invoke with a disabled IA was emitted, its return value may need to be checked;
    // in this case it should branch to another subblock of the same BB rather than its usual
    // successor, and the check will be constructed by our caller.

    bool advanceIter;
    BasicBlock* normalDest = getInvokeNormalSuccessor(I, advanceIter);

    if(advanceIter) {

      NewInvoke->setNormalDest(normalDest);
      ++emitBBIter;

    }

  }

} // End of emit-call-instruction.

// Debug check
static void checkEmittedInst(Instruction* I) {

  bool Broken = false;

  if(StoreInst* SI = dyn_cast<StoreInst>(I)) {

    Value* WritePtr = SI->getPointerOperand();
    if(isa<ConstantPointerNull>(WritePtr) || isa<UndefValue>(WritePtr))
      Broken = true;

  }

  if(Broken) {

    errs() << "WARNING: suspicious instruction emitted in block " << I->getParent() << "\n";

  }

}

// Emit generic instruction I into emitBB. We already know it isn't resolved to a constant, dead etc.
Instruction* IntegrationAttempt::emitInst(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  // Clone all attributes:
  Instruction* newI = I->invar->I->clone();
  I->committedVal = newI;
  emitBB->getInstList().push_back(cast<Instruction>(newI));

  if(isa<AllocaInst>(newI))
    getFunctionRoot()->emittedAlloca = true;

  if(CallInst* CI = dyn_cast<CallInst>(newI))
    CI->setTailCall(false);

  // Normal instruction: no BB arguments apart from invoke instructions, 
  // and all args have been committed already.
  for(uint32_t i = 0; i < I->getNumOperands(); ++i) {

    ConstantInt* ignFailValue = 0;
    BasicBlock* failBlock = 0;

    Value* opV = getCommittedValueOrBlock(I, i, ignFailValue, failBlock);
    release_assert(opV);
    Type* needTy = newI->getOperand(i)->getType();
    newI->setOperand(i, getValAsType(opV, needTy, newI));

    release_assert((!failBlock) && "Case not handled yet: invoke with ignored normal return");

  }

  // Warn if specialised code has been left via an exception (but stayed within the general domain of specialisation)
  if(pass->verbosePCs && isa<LandingPadInst>(newI)) {

    std::string msg;
    {
      raw_string_ostream RSO(msg);
      RSO << "Landed at landing pad inst in block " << BB->invar->BB->getName() << " / " << F.getName() << " / " << SeqNumber << "\n";
    }
    emitRuntimePrint(emitBB, msg, 0);
    
  }
   
  // If it's an allocation instruction, record the committed instruction.
  ShadowValue Base;
  AllocData* AD;
  if(getBaseObject(ShadowValue(I), Base) && 
     Base.isPtrIdx() && 
     (AD = getAllocData(Base)) && 
     AD->allocValue.u.I == I) {

    AD->committedVal = newI;
    AD->isCommitted = true;
    if(Base.getFrameNo() == -1)
      pass->committedHeapAllocations[newI] = Base.getHeapKey();

  }

  // If it's a store that is tracked by DSE, note the committed instruction.
  if(isa<StoreInst>(newI) || isa<MemSetInst>(newI)) {

    DenseMap<ShadowInstruction*, TrackedStore*>::iterator findit = GlobalIHP->trackedStores.find(I);
    if(findit != GlobalIHP->trackedStores.end()) {
      findit->second->isCommitted = true;
      findit->second->committedInsts = new WeakVH[1];
      findit->second->committedInsts[0] = newI;
      findit->second->nCommittedInsts = 1;
    }

  }

  {

    // Don't use forwardableOpenCalls here because surrogates for FDs need recording too.
    // The defining characteristic is always resolving to an FD that points back to this instruction.

    ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(I->i.PB);
    if(IVS && IVS->SetType == ValSetTypeFD && IVS->Values.size() == 1 && IVS->Values[0].V.isFdIdx()) {

      uint32_t FD = IVS->Values[0].V.getFd();
      FDGlobalState& FDS = pass->fds[FD];
      if((!FDS.isCommitted) && FDS.SI == I) {
	
	FDS.CommittedVal = newI;
	FDS.isCommitted = true;
	pass->committedFDs[newI] = FD;
	
      }

    }

  }

  // Debug checks for suspect instructions:
  checkEmittedInst(newI);

  return newI;

}

// Build a constexpr for (targetType)(((char*)GV) + Offset)
Constant* llvm::getGVOffset(Constant* GV, int64_t Offset, Type* targetType) {

  Type* Int8Ptr = Type::getInt8PtrTy(GV->getContext());
  Constant* CastGV;
  
  if(Offset != 0 && GV->getType() != Int8Ptr)
    CastGV = ConstantExpr::getBitCast(GV, Int8Ptr);
  else
    CastGV = GV;

  Constant* OffsetGV;
  if(Offset == 0)
    OffsetGV = CastGV;
  else {
    Constant* OffC = ConstantInt::get(Type::getInt64Ty(GV->getContext()), (uint64_t)Offset, true);
    OffsetGV = ConstantExpr::getGetElementPtr(0, CastGV, OffC);
  }
    
  // Cast to proper type:
  if(targetType != OffsetGV->getType()) {
    return ConstantExpr::getBitCast(OffsetGV, targetType);
  }
  else {
    return OffsetGV;
  }

}

// Create a pointer described by I (i.e. make gep and cast instructions).
// May be impossible if I is not specific enough, or completely unknown. Return false in that case.
bool IntegrationAttempt::synthCommittedPointer(ShadowValue I, SmallVector<CommittedBlock, 1>::iterator emitBB) {

  Value* Result;
  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(I));
  if((!IVS) || IVS->SetType != ValSetTypePB || IVS->Values.size() != 1)
    return false;

  bool ret = synthCommittedPointer(&I, getValueType(I), IVS->Values[0], emitBB->specBlock, Result);
  if(ret)
    I.setCommittedVal(Result);
  return ret;
  
}

// Can IV be synthesised (constructed from a base object and offset)
// or do we need its literal operand around?
// One reason it may be impossible to synthesise is if its base object can't
// be directly referenced, e.g. because its specialisation context was not committed
// and so there is no unique instruction that describes this particular object.
bool IntegrationAttempt::canSynthPointer(ShadowValue* I, ImprovedVal IV) {

  ShadowValue Base = IV.V;
  int64_t Offset = IV.Offset;

  if(Offset == LLONG_MAX)
    return false;
  
  // If it points to itself then this is an allocation instruction.
  if(I) {

    if(Base.isPtrIdx()) {

      AllocData* AD = getAllocData(Base);
      if((!AD->committedVal) && AD->allocValue == *I)
	return false;

    }
    else if(Base == *I)
      return false;

  }

  if(!Base.objectAvailable())
    return false;

  return true;

}

// Get the InlineAttempt at a particular stack depth by walking our parent contexts.
InlineAttempt* InlineAttempt::getStackFrameCtx(int32_t frameIdx) {

  // frameSize == -1 means no stack frame and the allocation really belongs to our caller.
  if(stack_depth == frameIdx && invarInfo->frameSize != -1)
    return this;
  else
    return activeCaller->parent->IA->getFunctionRoot()->getStackFrameCtx(frameIdx);

}

// Synthesise a pointer if we know its base object, have a unique instruction that allocates it, etc.
// If we can't do that, return false and we'll have to keep the pointer reference verbatim, meaning we need
// the operand alive and so on.
bool IntegrationAttempt::synthCommittedPointer(ShadowValue* I, Type* targetType, ImprovedVal IV, BasicBlock* emitBB, Value*& Result) {

  if(!canSynthPointer(I, IV))
    return false;

  ShadowValue Base = IV.V;
  int64_t Offset = IV.Offset;
  
  Type* Int8Ptr = Type::getInt8PtrTy(emitBB->getContext());

  if(Base.isGV()) {

    // Rep as a constant expression:
    Result = (getGVOffset(Base.getGV()->G, Offset, targetType));

  }
  else {

    Value* BaseI = getCommittedValue(Base);
    if(!BaseI) {

      // Base has not been committed yet. Create a trivial select instruction that will be populated
      // with the allocation when it is committed.
      // This is rather wasteful, but it saves having every synthCommitedPointer do their
      // own check and register.
      Value* True = ConstantInt::getTrue(emitBB->getContext());
      Value* UD = UndefValue::get(getValueType(Base));      
      BaseI = SelectInst::Create(True, UD, UD, "", emitBB);
      addPatchRequest(Base, cast<Instruction>(BaseI), 1);

    }

    // Try a few tricks to get the right pointer without using an i8 cast:
    
    // 1. Correct offset already?
    if(Offset == 0) {
      
      if(BaseI->getType() == targetType)
	Result = BaseI;
      else
	Result = CastInst::CreatePointerCast(BaseI, targetType, VerboseNames ? "synthcast" : "", emitBB);
      return true;

    }

    // 2. Pointer to an array or struct with a member at the right offset?
    SmallVector<Value*, 4> GEPIdxs;
    Type* InTy = BaseI->getType();
    release_assert(isa<PointerType>(InTy));
    InTy = cast<PointerType>(InTy)->getElementType();
    if(Type* ElTy = XXXFindElementAtOffset(InTy, Offset, GEPIdxs, GlobalTD)) {

      Result = GetElementPtrInst::Create(ElTy, BaseI, GEPIdxs, VerboseNames ? "synthgep" : "", emitBB);
      if((!isa<PointerType>(targetType)) || ElTy != cast<PointerType>(targetType)->getElementType())
	Result = CastInst::CreatePointerCast(Result, targetType, VerboseNames ? "synthcastback" : "", emitBB);
      return true;

    }

    // OK, use i8 offset.

    // Get byte ptr:
    Value* CastI;
    if(BaseI->getType() != Int8Ptr)
      CastI = new BitCastInst(BaseI, Int8Ptr, VerboseNames ? "synthcast" : "", emitBB);
    else
      CastI = BaseI;

    // Offset:
    Constant* OffsetC = ConstantInt::get(Type::getInt64Ty(emitBB->getContext()), (uint64_t)Offset, true);
    Value* OffsetI = GetElementPtrInst::Create(Int8Ptr, CastI, OffsetC, VerboseNames ? "synthgep" : "", emitBB);

    // Cast back:
    if(targetType == Int8Ptr) {
      Result = (OffsetI);
    }
    else {
      Result = (CastInst::CreatePointerCast(OffsetI, targetType, VerboseNames ? "synthcastback" : "", emitBB));
    }

  }

  return true;

}

// Check whether I can be synthesised as a constant, pointer to a known base, etc.
// If not it must be represented literally in the output program.
bool IntegrationAttempt::canSynthVal(ShadowValue* I, ValSetType Ty, const ImprovedVal& IV) {

  if(Ty == ValSetTypeScalar)
    return true;
  else if(Ty == ValSetTypeFD) {
    return ((!I) || (!I->isInst()) || (I->u.I != pass->fds[IV.V.u.PtrOrFd.idx].SI)) 
      && IV.V.objectAvailable();
  }
  else if(Ty == ValSetTypePB) {
    return canSynthPointer(I, IV);
  }

  return false;

}

// Produce a Value describing I by any means other than literally cloning the instruction.
// If that's impossible return null and we'll do the plain clone elsewhere.
// Cast I to targetType when synthesising. I's unique ImprovedVal is already known to be IV with type Ty.
// Write any needed cast / GEP / load instructions to emitBB.
Value* IntegrationAttempt::trySynthVal(ShadowValue* I, Type* targetType, ValSetType Ty, const ImprovedVal& IV, BasicBlock* emitBB) {

  if(Ty == ValSetTypeScalar) {

    // Constant -- synthesise if possible as a constexpr!
    
    Constant* C = getSingleConstant(IV.V);
    if(!C)
      return 0;

    return getConstAsType(C, targetType);

  }
  else if(Ty == ValSetTypeFD) {

    // File descriptor! Refer to the original 'open' instruction if we can.
    
    if(canSynthVal(I, Ty, IV)) {
      
      FDGlobalState& FDS = pass->fds[IV.V.u.PtrOrFd.idx];
      if(!FDS.CommittedVal) {

	// Open instruction not committed yet. Create a 'select' instruction that will be patched
	// out when the open call is eventually committed.
	Value* True = ConstantInt::getTrue(emitBB->getContext());
	Value* UD = UndefValue::get(getValueType(IV.V));      
	Instruction* Fwd = SelectInst::Create(True, UD, UD, "", emitBB);
	addPatchRequest(IV.V, Fwd, 1);
	return Fwd;

      }
      else
	return FDS.CommittedVal;

    }
    
  }
  else if(Ty == ValSetTypePB) {

    // Pointer -- create a direct reference to the original allocation if possible.
    Value* V;
    if(synthCommittedPointer(I, targetType, IV, emitBB, V))
      return V;

  }

  return 0;

}

// Write a residual memcpy to emitBB.
static Instruction* emitMemcpyInst(Value* To, Value* From, uint64_t Size, BasicBlock* emitBB) {

  Type* BytePtr = Type::getInt8PtrTy(emitBB->getContext());
  Type* Int64Ty = Type::getInt64Ty(emitBB->getContext());
  Constant* MemcpySize = ConstantInt::get(Int64Ty, Size);

  Type *Tys[3] = {BytePtr, BytePtr, Int64Ty};
  Function *MemCpyFn = Intrinsic::getDeclaration(getGlobalModule(),
						 Intrinsic::memcpy, 
						 ArrayRef<Type*>(Tys, 3));

  Value *CallArgs[] = {
    To, From, MemcpySize,
    ConstantInt::get(Type::getInt32Ty(emitBB->getContext()), 1),
    ConstantInt::get(Type::getInt1Ty(emitBB->getContext()), 0)
  };
	
  return CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", emitBB);

}

// Emit code to write (chunkBegin-chunkEnd] to I's first operand. This might be a simple
// store, or might need a memcpy call from a composite-typed object.
// newInstructions accumulates the stores, calls and casts required to do this,
// which are also written to emitBB.
// 'Chunks' are written in this way because ideally we'd use a big memcpy in preference to many
// small store instructions, but pointers, FDs and other non-constants can prevent us from doing so.
void IntegrationAttempt::emitChunk(ShadowInstruction* I, BasicBlock* emitBB, SmallVector<IVSRange, 4>::iterator chunkBegin, SmallVector<IVSRange, 4>::iterator chunkEnd, SmallVector<Instruction*, 4>& newInstructions) {

  uint32_t chunkSize = std::distance(chunkBegin, chunkEnd);
  if(chunkSize == 0)
    return;

  Type* BytePtr = Type::getInt8PtrTy(emitBB->getContext());

  // Create pointer that should be written through:
  Type* targetType;
  if(chunkSize == 1 && GlobalTD->getTypeStoreSize(getValueType(chunkBegin->second.Values[0].V)) <= 8)
    targetType = PointerType::getUnqual(getValueType(chunkBegin->second.Values[0].V));
  else
    targetType = BytePtr;

  // Synthesise a pointer corresponding to I's first operand.
  // We have already checked that the target is visible, so this must succeed:
  Value* targetPtrSynth;
  ImprovedVal targetPtr;
  ShadowValue targetPtrOp = I->getCallArgOperand(0);
  getBaseObject(targetPtrOp, targetPtr.V);
  targetPtr.Offset = chunkBegin->first.first;
  synthCommittedPointer(0, targetType, targetPtr, emitBB, targetPtrSynth);
  
  if(chunkSize == 1) {

    ImprovedVal& IV = chunkBegin->second.Values[0];
    ShadowValue IVal(I);
    Value* newVal = trySynthVal(&IVal, getValueType(IV.V), chunkBegin->second.SetType, IV, emitBB);
    uint64_t elSize = GlobalTD->getTypeStoreSize(newVal->getType());

    if(elSize > 8) {

      release_assert(isa<Constant>(newVal));

      // Emit memcpy from single constant.
      GlobalVariable* CopyFrom = new GlobalVariable(*getGlobalModule(), newVal->getType(), 
						    true, GlobalValue::InternalLinkage, cast<Constant>(newVal));
      Constant* CopyFromPtr = ConstantExpr::getBitCast(CopyFrom, BytePtr);
      newInstructions.push_back(emitMemcpyInst(targetPtrSynth, CopyFromPtr, elSize, emitBB));

    }
    else {

      // Emit as simple store.
      release_assert(newVal->getType() == cast<PointerType>(targetPtrSynth->getType())->getElementType());
      newInstructions.push_back(new StoreInst(newVal, targetPtrSynth, emitBB));

    }
      
  }
  else {

    // Emit as memcpy-from-packed-struct.
    SmallVector<Type*, 4> Types;
    SmallVector<Constant*, 4> Copy;
    uint64_t lastOffset = 0;
    for(SmallVector<IVSRange, 4>::iterator it = chunkBegin; it != chunkEnd; ++it) {

      ImprovedVal& IV = it->second.Values[0];
      ShadowValue IVal(I);
      Value* newVal = trySynthVal(&IVal, getValueType(IV.V), it->second.SetType, IV, emitBB);
      release_assert(!isa<Instruction>(newVal));
      Types.push_back(newVal->getType());
      Copy.push_back(cast<Constant>(newVal));
      lastOffset = it->first.second;

    }

    StructType* SType = StructType::get(emitBB->getContext(), Types, /*isPacked=*/true);
    Constant* CS = ConstantStruct::get(SType, Copy);
    GlobalVariable* GCS = new GlobalVariable(*getGlobalModule(), SType, 
					     true, GlobalValue::InternalLinkage, CS);
    Constant* GCSPtr = ConstantExpr::getBitCast(GCS, BytePtr);

    newInstructions.push_back(emitMemcpyInst(targetPtrSynth, GCSPtr, lastOffset - chunkBegin->first.first, emitBB));

  }

}

// Can a memcpy or memmove (a memory-transfer instruction, MTI) be synthesised (i.e. do we know
// the unique objects it writes and where it writes them?)
bool IntegrationAttempt::canSynthMTI(ShadowInstruction* I) {

  if(!GlobalIHP->memcpyValues.count(I))
    return false;

  ShadowValue IVal(I);

  // Can we describe the target?
  ShadowValue TargetPtr = I->getCallArgOperand(0);
  {
    ImprovedVal Test;
    if(!getBaseAndConstantOffset(TargetPtr, Test.V, Test.Offset))
      return false;
    if(!canSynthVal(&IVal, ValSetTypePB, Test))
      return false;
  }
  
  SmallVector<IVSRange, 4>& Vals = GlobalIHP->memcpyValues[I];

  // Can we describe all the copied values?
  for(SmallVector<IVSRange, 4>::iterator it = Vals.begin(),
	itend = Vals.end(); it != itend; ++it) {

    if(it->second.isWhollyUnknown() || it->second.Values.size() != 1)
      return false;

    if(!canSynthVal(&IVal, it->second.SetType, it->second.Values[0]))
      return false;

  }

  return true;

}

// Emit a sequence of stores and/or memcpy-from-constant-global instructions that
// have the effect of memcpy/memmove call I. If this is impossible (e.g. we're not certain
// of what is written or where it is written), return false.
bool IntegrationAttempt::trySynthMTI(ShadowInstruction* I, BasicBlock* emitBB) {

  if(!canSynthMTI(I))
    return false;

  // OK, the entire memcpy is made of things we can synthesise -- do it!
  // The method: for consecutive scalars or pointers-to-globals, synthesise a packed struct and
  // memcpy from it. For non-constant pointers and FDs, produce stores.

  SmallVector<IVSRange, 4>& Vals = GlobalIHP->memcpyValues[I];
  SmallVector<Instruction*, 4> newInstructions;

  SmallVector<IVSRange, 4>::iterator chunkBegin = Vals.begin();

  for(SmallVector<IVSRange, 4>::iterator it = Vals.begin(),
	itend = Vals.end(); it != itend; ++it) {

    if(it->second.SetType == ValSetTypeScalar || 
       (it->second.SetType == ValSetTypePB && (it->second.Values[0].V.isGV() || it->second.Values[0].V.isVal()))) {

      // Emit shortly.
      continue;

    }
    else {

      // Emit the chunk.
      emitChunk(I, emitBB, chunkBegin, it, newInstructions);

      // Emit this item (simple store, same as a singleton chunk).
      SmallVector<IVSRange, 4>::iterator nextit = it;
      ++nextit;
      emitChunk(I, emitBB, it, nextit, newInstructions);

      // Next chunk starts /after/ this.
      chunkBegin = nextit;

    }

  }

  // Emit the rest if any.
  emitChunk(I, emitBB, chunkBegin, Vals.end(), newInstructions);
  
  DenseMap<ShadowInstruction*, TrackedStore*>::iterator findit = GlobalIHP->trackedStores.find(I);
  if(findit != GlobalIHP->trackedStores.end()) {
    findit->second->isCommitted = true;
    findit->second->committedInsts = new WeakVH[newInstructions.size()];
    for(uint32_t i = 0, ilim = newInstructions.size(); i != ilim; ++i)
      findit->second->committedInsts[i] = newInstructions[i];
    findit->second->nCommittedInsts = newInstructions.size();
  }

  return true;

}

// Try to synthesise instruction I, which means returning a constant if possible, or creating a pointer
// expressed as a simple gep-and-cast from a known base object (alloca, malloc/similar, global...)
// If we cannot do this (e.g. I doesn't have a known concrete result, or we can't synthesise an appropriate
// pointer) then return false and our caller will have to create a literal clone of the original instruction
// instead.
// For memcpy instructions, try to turn them into a series of memcpy or store actions drawing from constants
// and known pointers.
// Emit any necessary instructions (e.g. casts) to emitBB.
bool IntegrationAttempt::trySynthInst(ShadowInstruction* I, BasicBlock* emitBB, Value*& Result) {

  if(inst_is<MemTransferInst>(I)) {
    Result = 0;
    return trySynthMTI(I, emitBB);
  }

  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(I->i.PB);
  if(!IVS)
    return false;

  if(IVS->Values.size() != 1)
    return false;

  // AtomicRMW and AtomicCmpXchg can be assigned values and not require a runtime check
  // if their operand was known to be thread-local; however for now emit them for their
  // side-effects.

  if(inst_is<AtomicRMWInst>(I) || inst_is<AtomicCmpXchgInst>(I))
    return false;

  ShadowValue IVal(I);
  Result = trySynthVal(&IVal, I->getType(), IVS->SetType, IVS->Values[0], emitBB);
  return !!Result;
  
}

// Similar to above, but try to synthesise an argument value.
bool IntegrationAttempt::trySynthArg(ShadowArg* A, BasicBlock* emitBB, Value*& Result) {

  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(A->i.PB);
  if(!IVS)
    return false;

  if(IVS->Values.size() != 1)
    return false;

  ShadowValue AVal(A);
  Result = trySynthVal(&AVal, A->getType(), IVS->SetType, IVS->Values[0], emitBB);
  return !!Result;

}

// Identify functions like llvm.uadd.with.overflow which are essentially arithmetic instructions.
static bool isPureCall(ShadowInstruction* SI) {

  Function* CalledF = getCalledFunction(SI);
  return CalledF && CalledF->isIntrinsic() && CalledF->doesNotAccessMemory();

}

// Create a synthetic version of I, or if that's impossible clone it. Emit synthesised / cloned instructions
// to *emitBB, and bump the emitBB iterator if subsequent instructions should target a different block because
// we emitted an inline call or an out-of-line call that needed us to possibly branch to unspecialised code.
void IntegrationAttempt::emitOrSynthInst(ShadowInstruction* I, ShadowBB* BB, SmallVector<CommittedBlock, 1>::iterator& emitBB) {

  bool useCallPath = (inst_is<CallInst>(I) || inst_is<InvokeInst>(I)) && 
    (!inst_is<MemIntrinsic>(I)) && 
    !isPureCall(I);

  if(useCallPath) {
    emitCall(BB, I, emitBB);
    if(I->committedVal)
      return;
    // Else fall through to fill in a committed value:
  }

  // Return instruction "dead" status means it won't be used -- but we must synthesise something
  // if this is an out-of-line commit.
  // Read instruction "dead" status means its memory writes are useless, but its return value
  // is still perhaps used.
  
  if(willBeDeleted(ShadowValue(I)) 
     && (!I->isTerminator()) 
     && (!pass->resolvedReadCalls.count(I)))
    return;

  // If a runtime check is required we need the literal instruction available.
  // The second parameter specifies this doesn't catch instructions that requires custom checks
  // such as VFS operations.
  if(!requiresRuntimeCheck(I, false)) {

    Value* V;
    if(trySynthInst(I, emitBB->specBlock, V)) {

      I->committedVal = V;
      return;

    }

  }

  // Already emitted calls above:
  if(useCallPath)
    return;

  // We'll emit an instruction. Is it special?
  if(inst_is<PHINode>(I))
    emitPHINode(BB, I, emitBB->specBlock);
  else if(I->isTerminator())
    emitTerminator(BB, I, emitBB->specBlock);
  else
    emitInst(BB, I, emitBB->specBlock);

}

// Write all instructions that fall within loop ScopeL. i is the index of the first basic block
// that falls within it (i.e. the header), and as a side-effect this function should leave i pointing to the
// first block not in ScopeL.
// ScopeL might be null, in which case this is a function root scope.
void IntegrationAttempt::commitLoopInstructions(const ShadowLoopInvar* ScopeL, uint32_t& i) {

  uint32_t thisLoopHeaderIdx = i;

  for(; i < nBBs; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i + BBsOffset);

    if(ScopeL && !ScopeL->contains(BBI->naturalScope))
      break;

    if(BBI->naturalScope != ScopeL) {

      // Entering a nested loop. First write the blocks for each iteration that's being unrolled:
      PeelAttempt* PA = getPeelAttempt(BBI->naturalScope);
      if(PA && PA->isEnabled() && PA->isTerminated()) {

	for(unsigned j = 0; j < PA->Iterations.size(); ++j)
	  PA->Iterations[j]->commitInstructions();

	SmallVector<const ShadowLoopInvar*, 4> loopStack;
	loopStack.push_back(ScopeL);

	// If the loop has terminated, skip populating the blocks in this context, but
	// do allow any unspecialised ('failed') version of this loop and its children
	// to populate their header PHI nodes by pulling from the specialised iterations
	// we just committed.
	const ShadowLoopInvar* skipL = BBI->naturalScope;
	while(i < nBBs && skipL->contains(getBBInvar(i + BBsOffset)->naturalScope)) {

	  const ShadowLoopInvar* ThisL = getBBInvar(i + BBsOffset)->naturalScope;
	  const ShadowLoopInvar* TopL = loopStack.back();
	  if(ThisL != loopStack.back()) {

	    if((!TopL) || TopL->contains(ThisL))
	      loopStack.push_back(ThisL);
	    else {

	      // Exiting subloops, finish failed header PHIs off:
	      while(ThisL != loopStack.back()) {
		
		const ShadowLoopInvar* ExitL = loopStack.back();
		populateFailedHeaderPHIs(ExitL);
		loopStack.pop_back();
		
	      }

	    }

	  }

	  populateFailedBlock(i + BBsOffset);
	  ++i;

	}

	while(loopStack.back() != ScopeL) {
	  populateFailedHeaderPHIs(loopStack.back());
	  loopStack.pop_back();
	}

      }
      else {

	// Emit blocks for the residualised general loop iteration.
	// (also has the side effect of winding 'i' past the loop)
	commitLoopInstructions(BBI->naturalScope, i);

      }

      // 'i' will now point to the first block outside the child loop.
      // Back it up so that after 'continue' we'll look at that block again.
      --i;
      continue;

    }

    // If BB is dead within specialised code the problem of generating
    // an unspecialised variant is much simplified.
    ShadowBB* BB = BBs[i];
    if(!BB) {
      commitSimpleFailedBlock(BBsOffset + i);
      continue;
    }

    uint32_t j;
    SmallVector<CommittedBlock, 1>::iterator emitPHIsTo = BB->committedBlocks.begin();

    // Even if there are path conditions, emit specialised PHIs into the first committed block for BB.
    // This means if we need to make a top-of-block check, like checking that a specialisation assumption
    // still holds, the block's phi nodes precede it regardless.
    for(j = 0; j < BB->insts.size() && inst_is<PHINode>(&(BB->insts[j])); ++j) {
      
      ShadowInstruction* I = &(BB->insts[j]);
      I->committedVal = 0;
      emitOrSynthInst(I, BB, emitPHIsTo);

    }

    release_assert(emitPHIsTo == BB->committedBlocks.begin() && "PHI emission should not move the emit pointer");

    // Synthesise path condition checks, using a successive emitBB for each one:
    SmallVector<CommittedBlock, 1>::iterator emitBlockIt;
    if(pass->omitChecks)
      emitBlockIt = BB->committedBlocks.begin();
    else
      emitBlockIt = emitPathConditionChecks(BB);

    // If the PHI nodes are loop exit PHIs that need their values checking, emit the check.
    if(j != 0) {

      ShadowInstruction* prevSI = &BB->insts[j-1];
      if(inst_is<PHINode>(prevSI) && requiresRuntimeCheck(ShadowValue(prevSI), false))
	emitBlockIt = emitExitPHIChecks(emitBlockIt, BB);

    }

    // Emit instructions for this block (using the same j index as before)
    for(; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);
      I->committedVal = 0;
      emitOrSynthInst(I, BB, emitBlockIt);

      // This only emits "check as expected" checks: simple comparisons that ensure a value
      // determined during specialisation matches the real value.
      // VFS ops (and perhaps others to come) produce special checks.
      if(requiresRuntimeCheck(ShadowValue(I), false))
	emitBlockIt = emitOrdinaryInstCheck(emitBlockIt, I);

    }

    // All instructions in this block are now available, so any companion unspecialised block
    // should now be able to populate phi nodes at specialised-to-unspecialised junctions.
    populateFailedBlock(i + BBsOffset);

  } // End of loop over BBs in this loop scope.

  if(ScopeL != L) {
    populateFailedHeaderPHIs(ScopeL);
    if(BBs[thisLoopHeaderIdx])
      fixupHeaderPHIs(BBs[thisLoopHeaderIdx]);
  }

}

// Apply the same debug tag to all of 'blocks'. Used to provide simple insight in GDB about the provenance
// of specialised code that crashes.
static void applyLocToBlocks(const DebugLoc& loc, const std::vector<BasicBlock*>& blocks) {

    for(std::vector<BasicBlock*>::const_iterator it = blocks.begin(), itend = blocks.end(); it != itend; ++it) {
	for(BasicBlock::iterator IIt = (*it)->begin(), IEnd = (*it)->end(); IIt != IEnd; ++IIt) {
	    if(!IIt->getDebugLoc())
		IIt->setDebugLoc(loc);
	}
    }

}

// Commit all arguments and instructions in this function context, using synthetic constants / pointers
// instead of the original instructions wherever possible. This recurses into loop contexts and child calls
// as they are found, and calls to populate phi nodes that unify values at specialised-to-unspecialised control-flow
// edges as their source operands become available.
// Child calls may or may not already have been committed, depending on whether we're in straight-line specialised
// code or not.
void InlineAttempt::commitArgsAndInstructions() {

  if(isCommitted()) {

    // This context has already been committed.
    // Patch arguments up, if needed. This happens when a child got committed
    // before us, and needed to refer to one of our arguments. In this case a dummy 'select'
    // instruction will have been introduced which we can now replace.
    for(uint32_t i = 0; i < F.arg_size(); ++i) {

      ShadowArg* SA = &(argShadows[i]);
      if(SA->patchInst)
	SA->patchInst->replaceAllUsesWith(getArgCommittedValue(SA, (BasicBlock*)0));

    }

  }
  else {

    // Commit this context now. The CFG will have already been created, including multiple residual
    // blocks per BB ('committedBlocks') when a BB needs to have result-as-expected checks inserted,
    // e.g. to check against clobbering by concurrent threads.

    // Start emitting code to the first block:
    SmallVector<CommittedBlock, 1>::iterator emitBB = BBs[0]->committedBlocks.begin();

    // Emit all arguments:
    for(uint32_t i = 0; i < F.arg_size(); ++i) {

      ShadowArg* SA = &(argShadows[i]);
      if(SA->dieStatus != INSTSTATUS_ALIVE)
	continue;

      if(!trySynthArg(SA, emitBB->specBlock, SA->committedVal))
	SA->committedVal = getArgCommittedValue(SA, entryBlock);

    }

    bool isVoidTy = F.getFunctionType()->getReturnType()->isVoidTy();
    Type* Ret = F.getFunctionType()->getReturnType();

    // Create return PHI if needed. This is a phi node that collects return values
    // if we're committing inline.
    if(returnBlock && !isVoidTy)
      returnPHI = makePHI(Ret, VerboseNames ? "retval" : "", returnBlock);
    else
      returnPHI = 0;

    // ...and this is a phi node that collects return values if we branch to unspecialised code
    // e.g. due to an assumption check failing.
    // If we commit out-of-line then a separate boolean return is used instead of the two different
    // target blocks / phi nodes like this.
    if(failedReturnBlock && !isVoidTy)
      failedReturnPHI = makePHI(Ret, VerboseNames ? "failedretval" : "", failedReturnBlock);
    else
      failedReturnPHI = 0;

    // Introduce an lliowd_init call if ordered. This sets up a connection to the file-watcher daemon
    // which we will use to check that file-reading calls may still be assumed to yield their
    // specialisation-time results (i.e. the file we're reading has not changed in the meantime)
    if((pass->llioPreludeStackIdx != -1 && 
	targetCallInfo && targetCallInfo->targetStackDepth == (uint32_t)pass->llioPreludeStackIdx) ||
       (((uint32_t)pass->llioPreludeStackIdx) == pass->targetCallStack.size() && isStackTop)) {

      Type* Void = Type::getVoidTy(emitBB->specBlock->getContext());
      Constant* WDInit = cast<Constant>(getGlobalModule()->getOrInsertFunction("lliowd_init", Void).getCallee());
      CallInst::Create(WDInit, ArrayRef<Value*>(), "", emitBB->specBlock);

    }

    // Commit all local instructions.
    commitInstructions();

    // Patch any child contexts that wanted to refer to alloca instructions that take place here,
    // but which had to introduce a temporary select instruction instead because we hadn't committed yet.
    fixNonLocalStackUses();

    // Should we emit debug tags to indicate which binary code derived from which specialisation contexts?
    // It's 'fake' in that it doesn't describe the original source code file / line.
    if(pass->emitFakeDebug) {

      DenseMap<Function*, DebugLoc>::iterator findit = pass->fakeDebugLocs.find(&F);
      DebugLoc* pFakeLoc;

      if(findit == pass->fakeDebugLocs.end()) {

	std::string fakeFilename;
	{
	  raw_string_ostream RSO(fakeFilename);
	  RSO << "__llpe__" << F.getName();
	}

	DIBuilder DIB(*F.getParent());

	DIFile* fakeFile = DIB.createFile(fakeFilename, "/nonesuch");
	DISubprogram* fakeFunction = DIB.createFunction(fakeFile, fakeFilename,
						       fakeFilename, fakeFile, 1,
							pass->fakeDebugType, 1,
							DINode::FlagZero, DISubprogram::SPFlagDefinition);
	DILexicalBlock* fakeBlock = DIB.createLexicalBlock(fakeFunction, fakeFile, 1, 0);
	MDNode *Scope = fakeBlock->getScope();
	DebugLoc newFakeLoc = DebugLoc::get(fakeBlock->getLine(), fakeBlock->getColumn(), Scope, NULL);
	  
	pFakeLoc = &(pass->fakeDebugLocs[&F] = newFakeLoc);

      }
      else {

	pFakeLoc = &findit->second;

      }

      DebugLoc& fakeLoc = *pFakeLoc;

      if(CommitF) {

	for(Function::iterator it = CommitF->begin(), itend = CommitF->end();
	    it != itend; ++it) {

	  for(BasicBlock::iterator IIt = it->begin(), IEnd = it->end(); IIt != IEnd; ++IIt)
	    if(!IIt->getDebugLoc())
	      IIt->setDebugLoc(fakeLoc);

	}

      }
      else {

	applyLocToBlocks(fakeLoc, CommitBlocks);
	applyLocToBlocks(fakeLoc, CommitFailedBlocks);

      }
	
    }

    // Give our committed functions and blocks to our parent context.
    // Do this here rather than in CommitCFG because blocks handling unreachable branches can be
    // created during emitTerminator.
    if(uniqueParent) {
     
      // If we already know the residual function we're writing to, committed blocks should have been added to
      // it instead of entering these arrays.
      if(CommitF)
	release_assert(CommitBlocks.empty() && CommitFailedBlocks.empty());

      uniqueParent->inheritCommitBlocksAndFunctions(CommitBlocks, CommitFailedBlocks, CommitFunctions);

    }

  }

}

// Commit all instructions in this context.
void IntegrationAttempt::commitInstructions() {

  // Bump progress bar
  SaveProgress();

  // If the user asked for a verbose specialisation, print to indicate we entered specialised code.
  if((!L) && getFunctionRoot()->isRootMainCall()) {

    BasicBlock* emitBB = BBs[0]->committedBlocks[0].specBlock;

    if(pass->verbosePCs) {

      std::string msg;
      {
	raw_string_ostream RSO(msg);
	RSO << "Entering specialised function " << F.getName() << "\n";
      }
      
      escapePercent(msg);
      emitRuntimePrint(emitBB, msg, 0);

    }

  }

  // Commit instructions local to this loop (or the whole function if this is an InlineAttempt and so L is null)
  uint32_t i = 0;
  commitLoopInstructions(L, i);

  if((!L) && getFunctionRoot()->isRootMainCall()) {

    // Patch references to pseudo-allocations based on the root function's arguments.
    for(uint32_t i = 0, ilim = F.arg_size(); i != ilim; ++i) {

      Value* StoreI = getFunctionRoot()->argShadows[i].committedVal;
      if(!isa<Argument>(StoreI))
	continue;

      patchReferences(pass->argStores[i].PatchRefs, StoreI);
      forwardReferences(StoreI, F.getParent());

    }

  }

  // This should be the last reference to the failed block maps here: deallocate.
  finishFailedBlockCommit();

  commitState = COMMIT_DONE;

}

// Remove any references to BB's instructions as committed versions of heap objects
// or file descriptors.
static void unregisterCommittedAllocations(BasicBlock* BB) {

  for(BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {

    Instruction* I = &*BI;
    {
      DenseMap<Value*, uint32_t>::iterator findit = GlobalIHP->committedHeapAllocations.find(I);
      if(findit != GlobalIHP->committedHeapAllocations.end()) {

	GlobalIHP->heap[findit->second].committedVal = 0;
	GlobalIHP->committedHeapAllocations.erase(findit);

      }
    }

    {
      DenseMap<Value*, uint32_t>::iterator findit = GlobalIHP->committedFDs.find(I);
      if(findit != GlobalIHP->committedFDs.end()) {

	GlobalIHP->fds[findit->second].CommittedVal = 0;
	GlobalIHP->committedFDs.erase(findit);

      }
    }

  }

}

// Remove any references to F's instructions as committed versions of heap objects
// or file descriptors.
static void unregisterCommittedAllocations(Function* F) {

  for(Function::iterator it = F->begin(), itend = F->end(); it != itend; ++it)
    unregisterCommittedAllocations(&*it);

}

// Delete all BBs and committed functions from all arguments. Used when releasing a whole tree of contexts
// whose specialised code is no longer needed.
static void releaseCC(std::vector<Function*>& CommitFunctions, std::vector<BasicBlock*>& CommitBlocks, std::vector<BasicBlock*>& CommitFailedBlocks) {

  for(std::vector<Function*>::iterator it = CommitFunctions.begin(), 
	itend = CommitFunctions.end(); it != itend; ++it) {

    Function* CF = *it;

    // This (and children) already in a function: kill it.
    unregisterCommittedAllocations(CF);
    CF->dropAllReferences();
    CF->eraseFromParent();

  }

  CommitFunctions.clear();

  for(std::vector<BasicBlock*>::iterator it = CommitBlocks.begin(),
	itend = CommitBlocks.end(); it != itend; ++it) {

    unregisterCommittedAllocations(*it);
    (*it)->dropAllReferences();

  }

  for(std::vector<BasicBlock*>::iterator it = CommitBlocks.begin(),
	itend = CommitBlocks.end(); it != itend; ++it) {

    delete *it;
    
  }

  CommitBlocks.clear();

  for(std::vector<BasicBlock*>::iterator it = CommitFailedBlocks.begin(),
	itend = CommitFailedBlocks.end(); it != itend; ++it) {

    unregisterCommittedAllocations(*it);
    (*it)->dropAllReferences();
    
  }

  for(std::vector<BasicBlock*>::iterator it = CommitFailedBlocks.begin(),
	itend = CommitFailedBlocks.end(); it != itend; ++it) {
    
    delete *it;

  }

  CommitFailedBlocks.clear();

}

// Delete all BBs and committed functions from all arguments. Used when releasing a whole tree of contexts
// whose specialised code is no longer needed.
// Note there is no need to recurse into child contexts because they pass their committed code to their parents when their commit
// phase finishes and so they themselves can be deallocated.
void InlineAttempt::releaseCommittedChildren() {

  releaseCC(CommitFunctions, CommitBlocks, CommitFailedBlocks);

}

void PeelAttempt::releaseCommittedChildren() {

  releaseCC(CommitFunctions, CommitBlocks, CommitFailedBlocks);

}

// Note that any allocation instructions, open instructions etc that occur
// in this context and its children are now available to be referenced directly.
void IntegrationAttempt::markAllocationsAndFDsCommitted() {

  if(isCommitted())
    return;

  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i);
    ShadowBB* BB = getBB(*BBI);
    if(!BB)
      continue;

    if(BBI->naturalScope != L) {

      const ShadowLoopInvar* subL = immediateChildLoop(L, BBI->naturalScope);
      PeelAttempt* LPA;
      if((LPA = getPeelAttempt(subL)) && LPA->isTerminated()) {

	for(uint32_t j = 0, jlim = LPA->Iterations.size(); j != jlim; ++j)
	  LPA->Iterations[j]->markAllocationsAndFDsCommitted();

	while(i != ilim && subL->contains(getBBInvar(i)->naturalScope))
	  ++i;
	--i;
	continue;

      }

    }

    for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

      ShadowInstruction& SI = BB->insts[j];
      ShadowValue Base;
      if(InlineAttempt* IA = getInlineAttempt(&SI)) {

	IA->markAllocationsAndFDsCommitted();

      }
      else if(getBaseObject(ShadowValue(&SI), Base) && Base.isPtrIdx()) {

	AllocData* AD = getAllocData(Base);
	if((!AD->isCommitted) && AD->allocValue == ShadowValue(&SI)) {
	  AD->isCommitted = true;
	  AD->committedVal = 0;
	}
	
      }
      else if(SI.i.PB && isa<ImprovedValSetSingle>(SI.i.PB)) {

	ImprovedValSetSingle* IVS = cast<ImprovedValSetSingle>(SI.i.PB);
	if(IVS->Values.size() == 1 && IVS->SetType == ValSetTypeFD) {

	  int32_t FD = IVS->Values[0].V.getFd();
	  FDGlobalState& FDGS = pass->fds[FD];
	  if(FDGS.SI == &SI) {
	    FDGS.isCommitted = true;
	    FDGS.CommittedVal = 0;
	  }

	}

      }

    }

  }

}

// Release copies of the heap state that were taken in case this
// function needed to be re-analysed to find a general case solution
// in the context of some enclosing loop.
void InlineAttempt::releaseBackupStores() {

  release_assert(backupTlStore);
  backupTlStore->dropReference();
  backupTlStore = 0;
  release_assert(backupDSEStore);
  backupDSEStore->dropReference();
  backupDSEStore = 0;

}

// Release all memory relating to this context except this object,
// which our caller will delete.
void IntegrationAttempt::releaseMemoryPostCommit() {

  if(commitState == COMMIT_FREED)
    return;

  // For the time being, retain all data if the user will inspect it.
  if(IHPSaveDOTFiles) {
    commitState = COMMIT_FREED;
    return;
  }

  for(IAIterator it = child_calls_begin(this),
	itend = child_calls_end(this); it != itend; ++it) {

    it->second->releaseMemoryPostCommit();
    // IAs may only be referenced from us at present
    it->second->dropReferenceFrom(it->first);

  }

  for(DenseMap<const ShadowLoopInvar*, PeelAttempt*>::iterator it = peelChildren.begin(),
	itend = peelChildren.end(); it != itend; ++it) {

    for(uint32_t i = 0, ilim = it->second->Iterations.size(); i != ilim; ++i) {

      it->second->Iterations[i]->releaseMemoryPostCommit();

    }

    delete it->second;

  }

  peelChildren.clear();

  for(uint32_t i = BBsOffset, ilim = BBsOffset + nBBs; i != ilim; ++i) {

    ShadowBB* BB = getBB(i);

    if(BB) {

      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	ShadowInstruction* SI = &BB->insts[j];
	if(SI->i.PB)
	  deleteIV(SI->i.PB);

	{
	  DenseMap<ShadowInstruction*, TrackedStore*>::iterator findit = pass->trackedStores.find(SI);
	  if(findit != pass->trackedStores.end()) {
	    findit->second->isCommitted = true;
	    pass->trackedStores.erase(findit);
	  }
	}

	{
	  DenseMap<ShadowInstruction*, TrackedAlloc*>::iterator findit = pass->trackedAllocs.find(SI);
	  if(findit != pass->trackedAllocs.end()) {
	    findit->second->isCommitted = true;
	    pass->trackedAllocs.erase(findit);
	  }
	}

	pass->indirectDIEUsers.erase(SI);
	pass->memcpyValues.erase(SI);
	pass->forwardableOpenCalls.erase(SI);
	pass->resolvedReadCalls.erase(SI);
	pass->resolvedSeekCalls.erase(SI);

      }

      delete BB;
      
    }

  }

  delete[] BBs;
  BBs = 0;

  commitState = COMMIT_FREED;

}

// Master commit entry point. inLoopAnalyser indicates that we're
// committing in the context of some enclosing unbounded loop, so we have
// a general-case analysis for this function instead of a per-iteration one.
void InlineAttempt::finaliseAndCommit(bool inLoopAnalyser) {

  countTentativeInstructions();
  collectStats();
	
  // This call will disable the context if it's not a good idea.
  findProfitableIntegration();

  if(isEnabled()) {

    // The TL and DSE stores were backed up to deal with the possibility
    // that the context would not be committed: we don't need those after all.
    releaseBackupStores();

    // Create residual blocks for disabled loops
    prepareCommitCall();

    if(!pass->statsFile.empty())
      preCommitStats(true);

    // Note any tests that require failed blocks.
    addCheckpointFailedBlocks();

    // Decide whether to commit in or out of line:
    findSaveSplits();

    // Find dead instructions.
    runDIE();

    // Save a DOT representation if need be, for the GUI to use.
    saveDOT();

    // Finally, do it!
    commitCFG();
    commitArgsAndInstructions();

    postCommitOptimise();

  }
  else {

    // Save a DOT representation if need be, for the GUI to use.
    saveDOT();

    // Allocations and FD creations in this scope should be marked
    // committed without canonical value.
    markAllocationsAndFDsCommitted();

    commitState = COMMIT_DONE;

    // Child contexts may have generated code that we no longer care
    // to use. Delete it if so.
    releaseCommittedChildren();

    // Must rerun tentative load and DSE analyses accounting
    // for the fact that the stage will not be committed.
    rerunTentativeLoads(activeCaller, this, inLoopAnalyser);

    // For now this is simply a barrier to DSE.
    setAllNeededTop(backupDSEStore);
    backupDSEStore->dropReference();
    if(activeCaller->parent->dseStore) {
      activeCaller->parent->dseStore = activeCaller->parent->dseStore->getEmptyMap();
      activeCaller->parent->dseStore->allOthersClobbered = true;
    }

    if(!pass->statsFile.empty())
      preCommitStats(true);

  }

  // Free all ShadowBBs, ShadowInstructions and similar.
  releaseMemoryPostCommit();

}

// Root commit entry point.

void LLPEAnalysisPass::commit() {

  if(!(omitChecks || llioDependentFiles.empty())) {

    // Note files that were read by specialised code, and so which must be checked for modification
    // during specialisation.
    writeLliowdConfig();

    BasicBlock* preludeBlock = 0;

    // Maybe insert an init call to connect to the file-watcher daemon.
    // Find the committed function where the init call should go:
    if(llioPreludeStackIdx == -1) {

      Function* writePreludeFn = llioPreludeFn;
      if(llioPreludeFn == &RootIA->F)
	writePreludeFn = RootIA->CommitF;

      if(writePreludeFn)
	preludeBlock = &writePreludeFn->getEntryBlock();

    }

    // Add an lliowd_init() prelude to the beginning of the requested function:
    if(preludeBlock) {

      BasicBlock::iterator it = preludeBlock->begin();
      while(it != preludeBlock->end() && isa<AllocaInst>(it))
	++it;

      Type* Void = Type::getVoidTy(preludeBlock->getContext());
      Constant* WDInit = cast<Constant>(getGlobalModule()->getOrInsertFunction("lliowd_init", Void).getCallee());
      CallInst::Create(WDInit, ArrayRef<Value*>(), "", &*it);

    }

  }

  // If requested, write verbose stats about this specialisation attempt.
  if(!statsFile.empty()) {

    postCommitStats();
    
    std::error_code error;
    raw_fd_ostream RFO(statsFile.c_str(), error, sys::fs::F_None);
    if(error)
      errs() << "Failed to open " << statsFile << ": " << error.message() << "\n";
    else
      stats.print(RFO);
  }

  // Redirect internal callers to use the specialised fuction.
  RootIA->F.replaceAllUsesWith(RootIA->CommitF);

  // Also exchange names so that external users will use this new version:
  std::string oldFName;
  {
    raw_string_ostream RSO(oldFName);
    RSO << RootIA->F.getName() << ".old";
  }

  RootIA->CommitF->takeName(&(RootIA->F));
  RootIA->F.setName(oldFName);

  errs() << "\n";

}

