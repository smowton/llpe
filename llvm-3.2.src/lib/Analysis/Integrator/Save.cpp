
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"

#include "../../VMCore/LLVMContextImpl.h"

#include <unistd.h>
#include <stdlib.h>

using namespace llvm;

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

void IntegrationAttempt::prepareCommit() {
  
  localPrepareCommit();

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if(!it->second->isEnabled())
      continue;

    it->second->prepareCommit();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    unsigned iterCount = it->second->Iterations.size();
    unsigned iterLimit = (it->second->Iterations.back()->iterStatus == IterationStatusFinal) ? iterCount : iterCount - 1;

    if(!it->second->isEnabled()) {
    
      if(it->second->isTerminated()) {

	// Loop hasn't been analysed for the general case -- do a rough and ready approximation
	// that emits any edge that is alive in any iteration.
	

	ShadowLoopInvar* LInfo = it->second->invarInfo;
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

void IntegrationAttempt::localPrepareCommit() {

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      /*
      ShadowInstruction* SI = &(BB->insts[j]);
      if(mayBeReplaced(SI) && !willBeReplacedOrDeleted(ShadowValue(SI)))
	SI->i.PB = ImprovedValSetSingle();
      */

    }

  }

}

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
    RSO << F.getName() << "-L" << L->getHeader()->getName() << "-I" << iterationCount << "-" << SeqNumber << " ";
  }
  return ret;

}

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

  GlobalIHP->commitFunctions.push_back(NewF);

  Function::arg_iterator DestI = NewF->arg_begin();
  for (Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end();
       I != E; ++I, ++DestI)
    DestI->setName(I->getName());
  
  NewF->copyAttributesFrom(F);

  return NewF;

}

// Return true if it will be necessary to insert code on the path leading from specialised to unspecialised code.
bool IntegrationAttempt::requiresBreakCode(ShadowInstruction* SI) {

  return SI->needsRuntimeCheck == RUNTIME_CHECK_SPECIAL && 
    pass->resolvedReadCalls.count(SI);

}

void IntegrationAttempt::commitCFG() {

  SaveProgress();

  Function* CF = getFunctionRoot()->CommitF;
  const Loop* currentLoop = L;
  
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

	const Loop* skipL = BB->invar->naturalScope;

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
    
    bool isEntryBlock = (!L) && i == 0 && commitsOutOfLine();

    std::string Name;
    if(VerboseNames) {
      raw_string_ostream RSO(Name);
      RSO << getCommittedBlockPrefix() << BB->invar->BB->getName();
    }
    else if(isEntryBlock)
      Name = "entry";
    BasicBlock* firstNewBlock = BasicBlock::Create(F.getContext(), Name);

    BB->committedBlocks.push_back(CommittedBlock(firstNewBlock, firstNewBlock, 0));

    // The function entry block is just the first one listed: create at front if necessary.
    if(isEntryBlock)
      CF->getBasicBlockList().push_front(firstNewBlock);
    else
      CF->getBasicBlockList().push_back(firstNewBlock);
      
    // Create extra empty blocks for each path condition that's effective here:
    // If OmitChecks is specified, no tests are emitted and so no blocks are needed.
    uint32_t nCondsHere = pass->omitChecks ? 0 : pass->countPathConditionsAtBlockStart(BB->invar, BB->IA);

    for(uint32_t k = 0; k < nCondsHere; ++k) {

      if(pass->verbosePCs) {

	// The previous block will contain a path condition check: give it a break block that will
	// sit on the edge from specialised to unspecialised code.

	Twine BlockName;
	if(VerboseNames)
	  BlockName = BB->invar->BB->getName() + ".break";
	else
	  BlockName = "";
	BasicBlock* breakBlock = BasicBlock::Create(F.getContext(), BlockName, CF);
	BB->committedBlocks.back().breakBlock = breakBlock;

      }

      Twine CondName;
      if(VerboseNames)
	CondName = BB->invar->BB->getName() + ".pathcond";
      else
	CondName = "";

      BasicBlock* newBlock = 
	BasicBlock::Create(F.getContext(), CondName, CF);

      BB->committedBlocks.push_back(CommittedBlock(newBlock, newBlock, 0));

    }

    // Create one extra top block if there's a special check at the beginning
    if(BB->insts[0].needsRuntimeCheck == RUNTIME_CHECK_SPECIAL && !pass->omitChecks) {

      if(pass->verbosePCs || requiresBreakCode(&BB->insts[0])) {
	
	Twine BreakName;
	if(VerboseNames)
	  BreakName = BB->invar->BB->getName() + ".break";
	else
	  BreakName = "";

	BasicBlock* breakBlock = BasicBlock::Create(F.getContext(), BreakName, CF);
	BB->committedBlocks.back().breakBlock = breakBlock;

      }

      Twine CheckName;
      if(VerboseNames)
	CheckName = BB->invar->BB->getName() + ".vfscheck";
      else
	CheckName = "";

      BasicBlock* newBlock =
	BasicBlock::Create(F.getContext(), CheckName, CF);	

      BB->committedBlocks.push_back(CommittedBlock(newBlock, newBlock, 0));

    }
     
    // Determine if we need to create more BBs because of call inlining, instruction checks and so on.

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* SI = &(BB->insts[j]);
      if(inst_is<CallInst>(SI)) {
	
	if(InlineAttempt* IA = getInlineAttempt(SI)) {

	  if(IA->isEnabled()) {

	    std::string Pref;
	    if(VerboseNames)
	      Pref = IA->getCommittedBlockPrefix();

	    if(!IA->commitsOutOfLine()) {

	      // Split the specialised block:
	      
	      IA->returnBlock = 
		BasicBlock::Create(F.getContext(), VerboseNames ? (StringRef(Pref) + "callexit") : "", CF);
	      BB->committedBlocks.push_back(CommittedBlock(IA->returnBlock, IA->returnBlock, j+1));

	      // Direct the call to the appropriate fail block:
	      if(IA->hasFailedReturnPath()) {

		Twine PreName;
		if(VerboseNames)
		  PreName = "prereturn";
		else
		  PreName = "";

		BasicBlock* preReturn = BasicBlock::Create(CF->getContext(), PreName, CF);
		IA->failedReturnBlock = preReturn;
		BasicBlock* targetBlock = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, j + 1);
		BranchInst::Create(targetBlock, preReturn);

	      }
	      else {

		IA->failedReturnBlock = 0;

	      }

	    }
	    else {

	      // Out-of-line function (vararg, or shared).
	      IA->returnBlock = 0;
	      IA->failedReturnBlock = 0;

	      // Requires a break afterwards if the target function might branch onto a failed path.
	      if(IA->hasFailedReturnPath()) {

		BasicBlock* newBlock = BasicBlock::Create(F.getContext(), VerboseNames ? StringRef(Pref) + "OOL callexit" : "", CF);
		BB->committedBlocks.push_back(CommittedBlock(newBlock, newBlock, j+1));

	      }

	    }

	    IA->commitCFG();
	    continue;

	  }

	}

      }

      // If we need a check *before* this instruction (at the moment only true if it's a read 
      // call that will require an inline check) then add a break.
      if(SI->needsRuntimeCheck == RUNTIME_CHECK_SPECIAL && !GlobalIHP->omitChecks) {

	if(j != 0) {

	  if(pass->verbosePCs || requiresBreakCode(SI)) {

	    BasicBlock* breakBlock = BasicBlock::Create(F.getContext(), VerboseNames ? StringRef(Name) + ".vfsbreak" : "", CF);
	    BB->committedBlocks.back().breakBlock = breakBlock;

	  }

	  BasicBlock* newSpecBlock = BasicBlock::Create(F.getContext(), VerboseNames ? StringRef(Name) + ".vfspass" : "", CF);
	  BB->committedBlocks.push_back(CommittedBlock(newSpecBlock, newSpecBlock, j));

	}

      }

      // If we have a disabled call, exit phi for a disabled loop, or tentative load
      // then insert a break for a check.
      // This path also handles path conditions that are checked as they are defined,
      // rather than at the top of a block that may be remote from the definition site.
      if(requiresRuntimeCheck(SI, false)) {

	if(j + 1 != BB->insts.size() && inst_is<PHINode>(SI) && inst_is<PHINode>(&BB->insts[j+1]))
	  continue;

	if(pass->verbosePCs) {
	
	  // The previous block will break due to a tentative load. Give it a break block.
	  BasicBlock* breakBlock = BasicBlock::Create(F.getContext(), VerboseNames ? StringRef(Name) + ".tlbreak" : "", CF);
	  BB->committedBlocks.back().breakBlock = breakBlock;

	}

	BasicBlock* newSpecBlock = BasicBlock::Create(F.getContext(), VerboseNames ? StringRef(Name) + ".checkpass" : "", CF);
	BB->committedBlocks.push_back(CommittedBlock(newSpecBlock, newSpecBlock, j+1));

      }

    }

    // If the block has ignored edges outgoing, it will branch direct to unspecialised code.
    // Make a break block for that purpose.
    if(pass->verbosePCs && hasLiveIgnoredEdges(BB)) {

      BB->committedBlocks.back().breakBlock = 
	BasicBlock::Create(F.getContext(), VerboseNames ? StringRef(Name) + ".directbreak" : "", CF);

    }

  }

}

Value* llvm::getCommittedValue(ShadowValue SV) {

  switch(SV.t) {
  case SHADOWVAL_OTHER:
    return SV.u.V;
  case SHADOWVAL_GV:
    return SV.u.GV->G;
  default:
    break;
  }

  switch(SV.t) {
  case SHADOWVAL_INST: 
    {
      release_assert(SV.u.I->committedVal && "Instruction depends on uncommitted instruction");
      return SV.u.I->committedVal;
    }
  case SHADOWVAL_ARG:
    {
      release_assert(SV.u.A->committedVal && "Instruction depends on uncommitted instruction");
      return SV.u.A->committedVal;
    }
  default:
    release_assert(0 && "Bad SV type");
    llvm_unreachable();
  }
  
}

Value* InlineAttempt::getArgCommittedValue(ShadowArg* SA) {

  unsigned n = SA->invar->A->getArgNo();

  if(commitsOutOfLine() || (!Callers.size()) || !isEnabled()) {

    // Use corresponding argument:
    Function::arg_iterator it = CommitF->arg_begin();
    for(unsigned i = 0; i < n; ++i)
      ++it;

    return it;

  }
  else {

    // Inlined in place -- use the corresponding value of our call instruction.
    // For sharing to work all arg values must match, so just use caller #0.
    return getCommittedValue(Callers[0]->getCallArgOperand(n));

  }

}

BasicBlock* InlineAttempt::getCommittedEntryBlock() {

  return BBs[0]->committedBlocks.front().specBlock;

}

BasicBlock* PeelIteration::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  if(BB->invar->idx == parentPA->invarInfo->latchIdx && succIdx == parentPA->invarInfo->headerIdx) {

    if(PeelIteration* PI = getNextIteration())
      return PI->getBB(succIdx)->committedBlocks.front().specBlock;
    else {
      if(iterStatus == IterationStatusFinal) {
	release_assert(pass->assumeEndsAfter(&F, L->getHeader(), iterationCount)
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

BasicBlock* InlineAttempt::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  if(shouldIgnoreEdge(BB->invar, getBBInvar(succIdx))) {

    release_assert(failedBlocks[succIdx].size());
    return failedBlocks[succIdx].front().first;

  }

  return IntegrationAttempt::getSuccessorBB(BB, succIdx, markUnreachable);

}

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
    // This is a BB which is guaranteed not reachable,
    // but the loop which will never branch to it is not being committed.
    // Emit unreachable instead.
    // This is only excusable if the immediate child of BB (not the successor) is present but disabled,
    // otherwise we should have explored the loop properly in this scope.
    if(PeelAttempt* PA = getPeelAttempt(immediateChildLoop(L, BB->invar->naturalScope))) {
      if(!PA->isEnabled())
	markUnreachable = true;
    }
  }

  if(!SuccBB)
    return 0;
  else
    return SuccBB->committedBlocks.front().specBlock;

}

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

Constant* llvm::getConstAsType(Constant* C, Type* Ty) {

  release_assert(CastInst::isCastable(C->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(C, false, Ty, false);
  return ConstantExpr::getCast(Op, C, Ty);

}

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

PHINode* llvm::makePHI(Type* Ty, const Twine& Name, BasicBlock* emitBB) {

  // Manually check for existing non-PHI instructions because BB->getFirstNonPHI assumes a finished block

  BasicBlock::iterator it = emitBB->begin();
  while(it != emitBB->end() && isa<PHINode>(it))
    ++it;
  
  if(it != emitBB->end())
    return PHINode::Create(Ty, 0, Name, it);
  else
    return PHINode::Create(Ty, 0, Name, emitBB);

}

void PeelIteration::emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  // Special case: emitting own header PHI. Emit a unary PHI drawing on either the preheader
  // argument or the latch one.

  PHINode* PN = cast_inst<PHINode>(I);

  if(BB->invar->idx == parentPA->invarInfo->headerIdx) {
    
    ShadowValue SourceV = getLoopHeaderForwardedOperand(I);

    PHINode* NewPN;
    I->committedVal = NewPN = makePHI(I->invar->I->getType(), VerboseNames ? "header" : "", emitBB);
    ShadowBB* SourceBB;

    if(iterationCount == 0) {

      SourceBB = parent->getBB(parentPA->invarInfo->preheaderIdx);

    }
    else {

      PeelIteration* prevIter = parentPA->Iterations[iterationCount-1];
      SourceBB = prevIter->getBB(parentPA->invarInfo->latchIdx);

    }

    // Emit any necessary casts into the predecessor block.
    Value* PHIOp = getValAsType(getCommittedValue(SourceV), PN->getType(), SourceBB->committedBlocks.back().specBlock->getTerminator());
    NewPN->addIncoming(PHIOp, SourceBB->committedBlocks.back().specBlock);
    return;

  }

  IntegrationAttempt::emitPHINode(BB, I, emitBB);

}

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

  getExitPHIOperands(SI, valOpIdx, ops, BBs, false);


}

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

void IntegrationAttempt::emitPHINode(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  PHINode* NewPN;
  I->committedVal = NewPN = makePHI(I->invar->I->getType(), "", emitBB);

  // Special case: emitting the header PHI of a residualised loop.
  // Make an empty node for the time being; this will be revisted once the loop body is emitted
  if(BB->invar->naturalScope && BB->invar->naturalScope->getHeader() == BB->invar->BB)
    return;

  populatePHINode(BB, I, NewPN);

}

void IntegrationAttempt::fixupHeaderPHIs(ShadowBB* BB) {

  uint32_t i;
  for(i = 0; i < BB->insts.size() && inst_is<PHINode>(&(BB->insts[i])); ++i) {
    if((!BB->insts[i].committedVal) || !isa<PHINode>(BB->insts[i].committedVal))
      continue;
    populatePHINode(BB, &(BB->insts[i]), cast<PHINode>(BB->insts[i].committedVal));
  }

}

void IntegrationAttempt::emitTerminator(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  if(inst_is<UnreachableInst>(I)) {

    emitInst(BB, I, emitBB);
    return;
    
  }

  if(inst_is<ReturnInst>(I)) {

    InlineAttempt* IA = getFunctionRoot();

    if(!IA->returnBlock) {

      Value* retVal;
      if((!F.getFunctionType()->getReturnType()->isVoidTy()) && I->dieStatus != INSTSTATUS_ALIVE)
	retVal = UndefValue::get(F.getReturnType());
      else if(F.getFunctionType()->getReturnType()->isVoidTy())
	retVal = 0;
      else
	retVal = getCommittedValue(I->getOperand(0));

      if(IA->hasFailedReturnPath() && !IA->isRootMainCall()) {

	Value* retFlag = ConstantInt::getTrue(emitBB->getContext());	
	if(!retVal) {
	  
	  retVal = retFlag;
	  
	}
	else {

	  StructType* retType = cast<StructType>(getFunctionRoot()->CommitF->getFunctionType()->getReturnType());
	  Type* normalRet = retType->getElementType(0);
	  Constant* undefRet = UndefValue::get(normalRet);
	  Value* aggTemplate = ConstantStruct::get(retType, undefRet, retFlag, NULL);
	  retVal = InsertValueInst::Create(aggTemplate, retVal, 0, VerboseNames ? "success_ret" : "", emitBB);

	}

      }

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

      if(pass->omitChecks && shouldIgnoreEdge(BB->invar, getBBInvar(BB->invar->succIdxs[i])))
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

    bool isSwitch = isa<SwitchInst>(newTerm);
    BasicBlock* defaultSwitchTarget = 0;
    
    // Like emitInst, but can emit BBs.
    for(uint32_t i = 0; i < I->getNumOperands(); ++i) {

      if(I->invar->operandIdxs[i].instIdx == INVALID_INSTRUCTION_IDX && I->invar->operandIdxs[i].blockIdx != INVALID_BLOCK_IDX) {

	// Argument is a BB.
	bool markUnreachable = false;
	BasicBlock* SBB = getSuccessorBB(BB, I->invar->operandIdxs[i].blockIdx, markUnreachable);

	release_assert((SBB || markUnreachable) && "Failed to get successor BB (2)");

	if(markUnreachable) {

	  // Create an unreachable BB to branch to:
	  BasicBlock* UBB = BasicBlock::Create(emitBB->getContext(), VerboseNames ? "LoopAssumeSink" : "", emitBB->getParent());
	  new UnreachableInst(UBB->getContext(), UBB);
	  newTerm->setOperand(i, UBB);

	}
	else {
	  
	  if(pass->verbosePCs && shouldIgnoreEdge(BB->invar, getBBInvar(I->invar->operandIdxs[i].blockIdx))) {
	  
	    ConstantInt* switchVal;
	    if(isSwitch) {

	      if(i == 1) {
		// Default target
		switchVal = 0;
		defaultSwitchTarget = SBB;
	      }
	      else {
		// Switch value comes before this target block.
		switchVal = cast<ConstantInt>(newTerm->getOperand(i - 1));
	      }

	    }
	    else {

	      switchVal = 0;

	    }
	      
	    breakSuccessors.push_back(std::make_pair(switchVal, SBB));
	    BasicBlock* breakBlock = BB->committedBlocks.back().breakBlock;
	    release_assert(breakBlock && "Should have a break block");
	    newTerm->setOperand(i, breakBlock);

	  }
	  else {

	    newTerm->setOperand(i, SBB);

	  }

	}

      }
      else { 

	ShadowValue op = I->getOperand(i);
	Value* opV = getCommittedValue(op);
	newTerm->setOperand(i, opV);

      }

    }

    if(!breakSuccessors.empty()) {

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

	release_assert(isSwitch);
	
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

static void emitSeekTo(Value* FD, uint64_t Offset, BasicBlock* emitBB) {

  LLVMContext& Context = FD->getContext();

  Type* Int64Ty = IntegerType::get(Context, 64);
  Constant* NewOffset = ConstantInt::get(Int64Ty, Offset);
  Type* Int32Ty = IntegerType::get(Context, 32);
  Constant* SeekSet = ConstantInt::get(Int32Ty, SEEK_SET);

  Constant* SeekFn = emitBB->getParent()->getParent()->getOrInsertFunction("lseek64", Int64Ty /* ret */, Int32Ty, Int64Ty, Int32Ty, NULL);

  Value* CallArgs[] = { FD, NewOffset, SeekSet };

  CallInst::Create(SeekFn, ArrayRef<Value*>(CallArgs, 3), "", emitBB);

}

bool IntegrationAttempt::emitVFSCall(ShadowBB* BB, ShadowInstruction* I, SmallVector<CommittedBlock, 1>::iterator& emitBBIter) {

  BasicBlock* emitBB = emitBBIter->specBlock;

  CallInst* CI = cast_inst<CallInst>(I);

  {
    DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(I);
    if(it != pass->resolvedReadCalls.end()) {
      
      LLVMContext& Context = CI->getContext();

      if(!pass->omitChecks) {

	// Emit a check that file specialisations are still admissible:
	// (TODO: avoid these more often)
	Type* Int32Ty = IntegerType::get(Context, 32);
	Constant* CheckFn = F.getParent()->getOrInsertFunction("lliowd_ok", Int32Ty, NULL);
	Value* CheckResult = CallInst::Create(CheckFn, ArrayRef<Value*>(), "readcheck", emitBB);
      
	Constant* Zero32 = Constant::getNullValue(Int32Ty);
	Value* CheckTest = new ICmpInst(*emitBB, CmpInst::ICMP_EQ, CheckResult, Zero32);

	BasicBlock* breakBlock = emitBBIter->breakBlock;

	// Seek to the right position in the break block:
	emitSeekTo(getCommittedValue(I->getCallArgOperand(0)), 
		   it->second.incomingOffset, breakBlock);
      
	// Print failure notice if building a verbose specialisation:
	if(pass->verbosePCs) {
	
	  std::string message;
	  {
	    raw_string_ostream RSO(message);
	    RSO << "Denied permission to use specialised files reading " << it->second.openArg->Name << " in " << emitBB->getName() << "\n";
	  }
	
	  emitRuntimePrint(breakBlock, message, 0);
	
	}
      
	++emitBBIter;

	// Branch to the real read instruction on failure:
	BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, I->invar->idx);
	BasicBlock* successTarget = emitBBIter->specBlock;
      
	BranchInst::Create(breakBlock, successTarget, CheckTest, emitBB);
	BranchInst::Create(failTarget, breakBlock);
      
	// Emit the rest of the read implementation in the next specialised block:
	emitBB = successTarget;

      }

      // Insert a seek call if that turns out to be necessary (i.e. if that FD may be subsequently
      // used without an intervening SEEK_SET)
      if(it->second.needsSeek) {
	
	emitSeekTo(getCommittedValue(I->getCallArgOperand(0)), 
		   it->second.incomingOffset + it->second.readSize, emitBB);
	  
      }

      if(it->second.readSize > 0 && !(I->dieStatus & INSTSTATUS_UNUSED_WRITER)) {
	
	// Create a memcpy from a constant, since someone is still using the read data.
	std::vector<Constant*> constBytes;
	std::string errors;
	if(!getFileBytes(it->second.openArg->Name, it->second.incomingOffset, it->second.readSize, constBytes, Context,  errors)) {

	  errs() << "Failed to read file " << it->second.openArg->Name << " in commit\n";
	  exit(1);

	}
      
	ArrayType* ArrType = ArrayType::get(IntegerType::get(Context, 8), constBytes.size());
	Constant* ByteArray = ConstantArray::get(ArrType, constBytes);

	// Create a const global for the array:

	GlobalVariable *ArrayGlobal = new GlobalVariable(*(CI->getParent()->getParent()->getParent()), ArrType, true, GlobalValue::InternalLinkage, ByteArray, "");

	Type* Int64Ty = IntegerType::get(Context, 64);
	Type *VoidPtrTy = Type::getInt8PtrTy(Context);

	Constant* ZeroIdx = ConstantInt::get(Int64Ty, 0);
	Constant* Idxs[2] = {ZeroIdx, ZeroIdx};
	Constant* CopySource = ConstantExpr::getGetElementPtr(ArrayGlobal, Idxs, 2);
      
	Constant* MemcpySize = ConstantInt::get(Int64Ty, constBytes.size());

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
	
	CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", emitBB);
	
      }

      return true;

    }

  }

  {
    
    DenseMap<ShadowInstruction*, SeekFile>::iterator it = pass->resolvedSeekCalls.find(I);
    if(it != pass->resolvedSeekCalls.end()) {

      if(!it->second.MayDelete)
	emitInst(BB, I, emitBB);

      return true;

    }

  }

  {

    DenseMap<ShadowInstruction*, OpenStatus*>::iterator it = pass->forwardableOpenCalls.find(I);
    if(it != pass->forwardableOpenCalls.end()) {
      if(it->second->success && I->dieStatus == INSTSTATUS_ALIVE) {

	emitInst(BB, I, emitBB);

      }

      return true;
    }

  }

  {
    
    DenseMap<ShadowInstruction*, CloseFile>::iterator it = pass->resolvedCloseCalls.find(I);
    if(it != pass->resolvedCloseCalls.end()) {

      if(it->second.MayDelete && it->second.openArg->MayDelete) {
	if(it->second.openInst->dieStatus == INSTSTATUS_DEAD)
	  return true;
      }

      emitInst(BB, I, emitBB);

      return true;

    }

  }

  Function* CalledF = getCalledFunction(I);

  if((!pass->omitChecks) && I->needsRuntimeCheck == RUNTIME_CHECK_SPECIAL && 
     (CalledF->getName() == "stat" || CalledF->getName() == "fstat")) {

    LLVMContext& Context = emitBB->getContext();

    // Emit an lliowd_ok check, and if it fails branch to the real stat instruction.
    Type* Int32Ty = IntegerType::get(Context, 32);
    Constant* CheckFn = F.getParent()->getOrInsertFunction("lliowd_ok", Int32Ty, NULL);
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
    
    BranchInst::Create(failTarget, successTarget, CheckTest, emitBB);

    return true;
    
  }

  return false;

}

void IntegrationAttempt::emitCall(ShadowBB* BB, ShadowInstruction* I, SmallVector<CommittedBlock, 1>::iterator& emitBBIter) {

  BasicBlock* emitBB = emitBBIter->specBlock;

  if(InlineAttempt* IA = getInlineAttempt(I)) {

    if(IA->isEnabled()) {

      if(!IA->commitsOutOfLine()) {

	// Branch from the current write BB to the call's entry block:
	BranchInst::Create(IA->getCommittedEntryBlock(), emitBB);

	// Make a PHI node that will catch return values, and make it our committed
	// value so that users get that instead of the call.
	
	bool isNonVoid = !IA->F.getFunctionType()->getReturnType()->isVoidTy();
	bool createRetPHI = isNonVoid && !willBeReplacedOrDeleted(ShadowValue(I));
	
	if(createRetPHI) {
	  I->committedVal = IA->returnPHI = makePHI(IA->F.getFunctionType()->getReturnType(), 
						    VerboseNames ? "retval" : "", IA->returnBlock);
	}
	else {
	  I->committedVal = 0;
	  IA->returnPHI = 0;
	}

	if(IA->hasFailedReturnPath() && isNonVoid) {
	  IA->failedReturnPHI = makePHI(IA->F.getFunctionType()->getReturnType(), 
					VerboseNames ? "failedretval" : "", IA->failedReturnBlock);
	}
	else {
	  IA->failedReturnPHI = 0;
	}

	// Emit further instructions in this ShadowBB to the successor block:
	++emitBBIter;
	release_assert(emitBBIter->specBlock == IA->returnBlock);
	
      }
      else {

	FunctionType* FType = IA->F.getFunctionType();

	// Build a call to IA->CommitF with same attributes but perhaps less arguments.
	// Most of this code borrowed from Transforms/IPO/DeadArgumentElimination.cpp

	CallInst* OldCI = cast_inst<CallInst>(I);

	SmallVector<AttributeWithIndex, 8> AttributesVec;
	const AttrListPtr &CallPAL = OldCI->getAttributes();

	Attributes FnAttrs = CallPAL.getFnAttributes();
	  
	std::vector<Value*> Args;

	uint32_t ilim;
	if(FType->isVarArg())
	  ilim = OldCI->getNumArgOperands();
	else
	  ilim = FType->getNumParams();

	for(uint32_t i = 0; i != ilim; ++i) {
	    
	  Attributes Attrs = CallPAL.getParamAttributes(i + 1);
	  if(Attrs.hasAttributes())
	    AttributesVec.push_back(AttributeWithIndex::get(i + 1, Attrs));

	  // (Except this bit, a clone of emitInst)

	  Type* needTy;
	  if(i < FType->getNumParams()) {
	    // Normal argument: cast to target function type.
	    needTy = FType->getParamType(i);
	  }
	  else {
	    // Vararg: cast to old callinst arg type.
	    needTy = OldCI->getArgOperand(i)->getType();
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

	if (FnAttrs.hasAttributes())
	  AttributesVec.push_back(AttributeWithIndex::get(AttrListPtr::FunctionIndex,
							  FnAttrs));
	  
	AttrListPtr NewCallPAL = AttrListPtr::get(IA->CommitF->getContext(), AttributesVec);

	CallInst* NewCI = cast<CallInst>(CallInst::Create(IA->CommitF, Args, "", emitBB));
	NewCI->setCallingConv(OldCI->getCallingConv());
	NewCI->setAttributes(NewCallPAL);
	if(OldCI->isTailCall())
	  NewCI->setTailCall();
	NewCI->setDebugLoc(OldCI->getDebugLoc());
	  
	I->committedVal = NewCI;

	if(IA->hasFailedReturnPath()) {

	  // This out-of-line call might fail. If it did, branch to unspecialised code.

	  Value* CallFailed;
	  if(IA->F.getFunctionType()->getReturnType()->isVoidTy()) {

	    CallFailed = NewCI;

	  }
	  else {

	    CallFailed = ExtractValueInst::Create(NewCI, ArrayRef<unsigned>(1), VerboseNames ? "retfailflag" : "", emitBB);
	    I->committedVal = ExtractValueInst::Create(NewCI, ArrayRef<unsigned>(0), VerboseNames ? "ret" : "", emitBB);
	    
	  }

	  ++emitBBIter;
	  BasicBlock* successTarget = emitBBIter->specBlock;
	  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, I->invar->idx + 1);
	  BranchInst::Create(successTarget, failTarget, CallFailed, emitBB);

	}

      }

      if(!IA->instructionsCommitted) {
	IA->commitArgsAndInstructions();
	IA->instructionsCommitted = true;
      }
    
      if(!IA->commitsOutOfLine()) {

	if(IA->emittedAlloca) {

	  // If the residual, inline function allocates stack memory, bound its lifetime
	  // with stacksave/restore.

	  Module *M = emitBB->getParent()->getParent();

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

	if(IA->returnPHI && IA->returnPHI->getNumIncomingValues() == 0) {
	  IA->returnPHI->eraseFromParent();
	  IA->returnPHI = 0;
	  I->committedVal = UndefValue::get(IA->F.getFunctionType()->getReturnType());
	}

      }

      return;
    
    }

  }
  
  if(emitVFSCall(BB, I, emitBBIter))
    return;

  // Unexpanded call, emit it as a normal instruction.
  emitInst(BB, I, emitBB);

}

Instruction* IntegrationAttempt::emitInst(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  // Clone all attributes:
  Instruction* newI = I->invar->I->clone();
  I->committedVal = newI;
  emitBB->getInstList().push_back(cast<Instruction>(newI));

  if(isa<AllocaInst>(newI))
    getFunctionRoot()->emittedAlloca = true;

  if(isa<CallInst>(newI))
    cast<CallInst>(newI)->setTailCall(false);

  // Normal instruction: no BB arguments, and all args have been committed already.
  for(uint32_t i = 0; i < I->getNumOperands(); ++i) {

    ShadowValue op = I->getOperand(i);
    Value* opV = getCommittedValue(op);
    Type* needTy = newI->getOperand(i)->getType();
    newI->setOperand(i, getValAsType(opV, needTy, newI));

  }

  DenseMap<ShadowInstruction*, GlobalVariable*>::iterator findit = pass->globalisedAllocations.find(I);
  if(findit != pass->globalisedAllocations.end()) {

    // This allocation is used in other functions: store it to a corresponding global.
    // Cast to i8* if need be:
    Type* VoidPtr = Type::getInt8PtrTy(F.getContext());
    Instruction* StoreI;

    if(newI->getType() != VoidPtr)
      StoreI = new BitCastInst(newI, VoidPtr, "", emitBB);
    else
      StoreI = newI;

    new StoreInst(StoreI, findit->second, emitBB);

  }

  DenseMap<ShadowInstruction*, GlobalVariable*>::iterator findit2 = pass->globalisedFDs.find(I);
  if(findit2 != pass->globalisedFDs.end()) {

    new StoreInst(newI, findit2->second, emitBB);

  }

  if(isa<StoreInst>(newI)) {

    release_assert(newI->getOperand(0)->getType() == cast<PointerType>(newI->getOperand(1)->getType())->getElementType());

  }

  return newI;

}

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
    OffsetGV = ConstantExpr::getGetElementPtr(CastGV, OffC);
  }
    
  // Cast to proper type:
  if(targetType != OffsetGV->getType()) {
    return ConstantExpr::getBitCast(OffsetGV, targetType);
  }
  else {
    return OffsetGV;
  }

}

bool IntegrationAttempt::synthCommittedPointer(ShadowValue I, SmallVector<CommittedBlock, 1>::iterator emitBB) {

  Value* Result;
  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(I));
  if((!IVS) || IVS->SetType != ValSetTypePB || IVS->Values.size() != 1)
    return false;

  bool ret = synthCommittedPointer(&I, I.getType(), IVS->Values[0], emitBB->specBlock, Result);
  if(ret)
    I.setCommittedVal(Result);
  return ret;
  
}

bool IntegrationAttempt::canSynthPointer(ShadowValue* I, ImprovedVal IV) {

  ShadowValue Base = IV.V;
  int64_t Offset = IV.Offset;

  if(Offset == LLONG_MAX)
    return false;
  
  if(I && Base == *I)
    return false;

  if(!Base.objectAvailable())
    return false;

  return true;

}

namespace llvm {

  Type* FindElementAtOffset(Type *Ty, int64_t Offset,
			    SmallVectorImpl<Value*> &NewIndices,
			    DataLayout* TD);

}

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

    Value* BaseI;
    if(Base.isVal() || Base.getCtx()->getFunctionRoot()->CommitF == getFunctionRoot()->CommitF)
      BaseI = getCommittedValue(Base);
    else {
      GlobalVariable* FwdGlobal;
      if(Base.isInst())
	FwdGlobal = pass->globalisedAllocations[Base.u.I];
      else
	FwdGlobal = pass->argStores[Base.u.A->invar->A->getArgNo()].fwdGV;
      release_assert(FwdGlobal && "Used out of function but not forwarded?");
      BaseI = new LoadInst(FwdGlobal, "getfwdg", emitBB);
    }
    release_assert(BaseI && "Synthing pointer atop uncommitted allocation");

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
    if(Type* ElTy = FindElementAtOffset(InTy, Offset, GEPIdxs, GlobalTD)) {

      Result = GetElementPtrInst::Create(BaseI, GEPIdxs, VerboseNames ? "synthgep" : "", emitBB);
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
    Value* OffsetI = GetElementPtrInst::Create(CastI, OffsetC, VerboseNames ? "synthgep" : "", emitBB);

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

bool IntegrationAttempt::canSynthVal(ShadowInstruction* I, ValSetType Ty, ImprovedVal& IV) {

  if(Ty == ValSetTypeScalar)
    return true;
  else if(Ty == ValSetTypeFD)
    return (I != IV.V.getInst() && IV.V.objectAvailable());
  else if(Ty == ValSetTypePB) {
    ShadowValue SV;
    if(I)
      SV = ShadowValue(I);
    return canSynthPointer(I ? &SV : 0, IV);
  }

  return false;

}

Value* IntegrationAttempt::trySynthVal(ShadowInstruction* I, Type* targetType, ValSetType Ty, ImprovedVal& IV, BasicBlock* emitBB) {

  if(Ty == ValSetTypeScalar)
    return IV.V.getVal();
  else if(Ty == ValSetTypeFD) {
    
    if(I != IV.V.getInst() && 
       IV.V.objectAvailable()) {
      
      DenseMap<ShadowInstruction*, GlobalVariable*>::iterator findit = pass->globalisedFDs.find(IV.V.u.I);
      if(findit != pass->globalisedFDs.end()) {
	return new LoadInst(findit->second, "fwdfd", emitBB);
      }
      else {
	return IV.V.getInst()->committedVal;
      }

    }
    
  }
  else if(Ty == ValSetTypePB) {

    Value* V;
    ShadowValue SV;
    if(I)
      SV = ShadowValue(I);
    if(synthCommittedPointer(I ? &SV : 0, targetType, IV, emitBB, V))
      return V;

  }

  return 0;

}

static void emitMemcpyInst(Value* To, Value* From, uint64_t Size, BasicBlock* emitBB) {

  Type* BytePtr = Type::getInt8PtrTy(emitBB->getContext());
  Type* Int64Ty = Type::getInt64Ty(emitBB->getContext());
  Constant* MemcpySize = ConstantInt::get(Int64Ty, Size);

  Type *Tys[3] = {BytePtr, BytePtr, Int64Ty};
  Function *MemCpyFn = Intrinsic::getDeclaration(emitBB->getParent()->getParent(),
						 Intrinsic::memcpy, 
						 ArrayRef<Type*>(Tys, 3));

  Value *CallArgs[] = {
    To, From, MemcpySize,
    ConstantInt::get(Type::getInt32Ty(emitBB->getContext()), 1),
    ConstantInt::get(Type::getInt1Ty(emitBB->getContext()), 0)
  };
	
  CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", emitBB);

}

void IntegrationAttempt::emitChunk(ShadowInstruction* I, BasicBlock* emitBB, SmallVector<IVSRange, 4>::iterator chunkBegin, SmallVector<IVSRange, 4>::iterator chunkEnd) {

  uint32_t chunkSize = std::distance(chunkBegin, chunkEnd);
  if(chunkSize == 0)
    return;

  Type* BytePtr = Type::getInt8PtrTy(emitBB->getContext());

  // Create pointer that should be written through:
  Type* targetType;
  if(chunkSize == 1 && GlobalAA->getTypeStoreSize(chunkBegin->second.Values[0].V.getType()) <= 8)
    targetType = PointerType::getUnqual(chunkBegin->second.Values[0].V.getType());
  else
    targetType = BytePtr;

  // We have already checked that the target is visible, so this must succeed:
  Value* targetPtrSynth;
  ImprovedVal targetPtr;
  ShadowValue targetPtrOp = I->getCallArgOperand(0);
  getBaseObject(targetPtrOp, targetPtr.V);
  targetPtr.Offset = chunkBegin->first.first;
  synthCommittedPointer(0, targetType, targetPtr, emitBB, targetPtrSynth);
  
  if(chunkSize == 1) {

    ImprovedVal& IV = chunkBegin->second.Values[0];
    Value* newVal = trySynthVal(I, IV.V.getType(), chunkBegin->second.SetType, IV, emitBB);
    uint64_t elSize = GlobalAA->getTypeStoreSize(newVal->getType());

    if(elSize > 8) {

      release_assert(isa<Constant>(newVal));

      // Emit memcpy from single constant.
      GlobalVariable* CopyFrom = new GlobalVariable(*(emitBB->getParent()->getParent()), newVal->getType(), 
						    true, GlobalValue::InternalLinkage, cast<Constant>(newVal));
      Constant* CopyFromPtr = ConstantExpr::getBitCast(CopyFrom, BytePtr);
      emitMemcpyInst(targetPtrSynth, CopyFromPtr, elSize, emitBB);

    }
    else {

      // Emit as simple store.
      release_assert(newVal->getType() == cast<PointerType>(targetPtrSynth->getType())->getElementType());
      new StoreInst(newVal, targetPtrSynth, emitBB);

    }
      
  }
  else {

    // Emit as memcpy-from-packed-struct.
    SmallVector<Type*, 4> Types;
    SmallVector<Constant*, 4> Copy;
    uint64_t lastOffset = 0;
    for(SmallVector<IVSRange, 4>::iterator it = chunkBegin; it != chunkEnd; ++it) {

      ImprovedVal& IV = it->second.Values[0];
      Value* newVal = trySynthVal(I, IV.V.getType(), it->second.SetType, IV, emitBB);
      release_assert(!isa<Instruction>(newVal));
      Types.push_back(newVal->getType());
      Copy.push_back(cast<Constant>(newVal));
      lastOffset = it->first.second;

    }

    StructType* SType = StructType::get(emitBB->getContext(), Types, /*isPacked=*/true);
    Constant* CS = ConstantStruct::get(SType, Copy);
    GlobalVariable* GCS = new GlobalVariable(*(emitBB->getParent()->getParent()), SType, 
					     true, GlobalValue::InternalLinkage, CS);
    Constant* GCSPtr = ConstantExpr::getBitCast(GCS, BytePtr);

    emitMemcpyInst(targetPtrSynth, GCSPtr, lastOffset - chunkBegin->first.first, emitBB);

  }

}

bool IntegrationAttempt::canSynthMTI(ShadowInstruction* I) {

  if(!GlobalIHP->memcpyValues.count(I))
    return false;

  // Can we describe the target?
  ShadowValue TargetPtr = I->getCallArgOperand(0);
  {
    ImprovedVal Test;
    if(!getBaseAndConstantOffset(TargetPtr, Test.V, Test.Offset))
      return false;
    if(!canSynthVal(I, ValSetTypePB, Test))
      return false;
  }
  
  SmallVector<IVSRange, 4>& Vals = GlobalIHP->memcpyValues[I];

  // Can we describe all the copied values?
  for(SmallVector<IVSRange, 4>::iterator it = Vals.begin(),
	itend = Vals.end(); it != itend; ++it) {

    if(it->second.isWhollyUnknown() || it->second.Values.size() != 1)
      return false;

    if(!canSynthVal(I, it->second.SetType, it->second.Values[0]))
      return false;

  }

  return true;

}

bool IntegrationAttempt::trySynthMTI(ShadowInstruction* I, BasicBlock* emitBB) {

  if(!canSynthMTI(I))
    return false;

  // OK, the entire memcpy is made of things we can synthesise -- do it!
  // The method: for consecutive scalars or pointers-to-globals, synthesise a packed struct and
  // memcpy from it. For non-constant pointers and FDs, produce stores.

  SmallVector<IVSRange, 4>& Vals = GlobalIHP->memcpyValues[I];

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
      emitChunk(I, emitBB, chunkBegin, it);

      // Emit this item (simple store, same as a singleton chunk).
      SmallVector<IVSRange, 4>::iterator nextit = it;
      ++nextit;
      emitChunk(I, emitBB, it, nextit);

      // Next chunk starts /after/ this.
      chunkBegin = nextit;

    }

  }

  // Emit the rest if any.
  emitChunk(I, emitBB, chunkBegin, Vals.end());

  return true;

}

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

  Result = trySynthVal(I, I->getType(), IVS->SetType, IVS->Values[0], emitBB);
  return !!Result;
  
}

void IntegrationAttempt::emitOrSynthInst(ShadowInstruction* I, ShadowBB* BB, SmallVector<CommittedBlock, 1>::iterator& emitBB) {

  if(inst_is<CallInst>(I) && !inst_is<MemIntrinsic>(I)) {
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
     && (!inst_is<TerminatorInst>(I)) 
     && (!pass->resolvedReadCalls.count(I)))
    return;

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
  if(inst_is<CallInst>(I) && !inst_is<MemIntrinsic>(I))
    return;

  // We'll emit an instruction. Is it special?
  if(inst_is<PHINode>(I))
    emitPHINode(BB, I, emitBB->specBlock);
  else if(inst_is<TerminatorInst>(I))
    emitTerminator(BB, I, emitBB->specBlock);
  else
    emitInst(BB, I, emitBB->specBlock);

}

void IntegrationAttempt::commitLoopInstructions(const Loop* ScopeL, uint32_t& i) {

  uint32_t thisLoopHeaderIdx = i;

  for(; i < nBBs; ++i) {

    ShadowBBInvar* BBI = getBBInvar(i + BBsOffset);

    if(ScopeL && !ScopeL->contains(BBI->naturalScope))
      break;

    if(BBI->naturalScope != ScopeL) {

      // Entering a loop. First write the blocks for each iteration that's being unrolled:
      PeelAttempt* PA = getPeelAttempt(BBI->naturalScope);
      if(PA && PA->isEnabled() && PA->isTerminated()) {

	for(unsigned j = 0; j < PA->Iterations.size(); ++j)
	  PA->Iterations[j]->commitInstructions();

	SmallVector<const Loop*, 4> loopStack;
	loopStack.push_back(ScopeL);

	// If the loop has terminated, skip populating the blocks in this context.
	const Loop* skipL = BBI->naturalScope;
	while(i < nBBs && skipL->contains(getBBInvar(i + BBsOffset)->naturalScope)) {

	  const Loop* ThisL = getBBInvar(i + BBsOffset)->naturalScope;
	  const Loop* TopL = loopStack.back();
	  if(ThisL != loopStack.back()) {

	    if((!TopL) || TopL->contains(ThisL))
	      loopStack.push_back(ThisL);
	    else {

	      // Exiting subloops, finish failed header PHIs off:
	      while(ThisL != loopStack.back()) {
		
		const Loop* ExitL = loopStack.back();
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

	// Emit blocks for the residualised loop
	// (also has the side effect of winding us past the loop)
	commitLoopInstructions(BBI->naturalScope, i);

      }

      --i;
      continue;

    }

    ShadowBB* BB = BBs[i];
    if(!BB) {
      commitSimpleFailedBlock(BBsOffset + i);
      continue;
    }

    uint32_t j;
    SmallVector<CommittedBlock, 1>::iterator emitPHIsTo = BB->committedBlocks.begin();
      
    // Even if there are path conditions, emit specialised PHIs into the first block.
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

    populateFailedBlock(i + BBsOffset);

  }

  if(ScopeL != L) {
    populateFailedHeaderPHIs(ScopeL);
    if(BBs[thisLoopHeaderIdx])
      fixupHeaderPHIs(BBs[thisLoopHeaderIdx]);
  }

}

void InlineAttempt::commitArgsAndInstructions() {
  
  SmallVector<CommittedBlock, 1>::iterator emitBB = BBs[0]->committedBlocks.begin();
  for(uint32_t i = 0; i < F.arg_size(); ++i) {

    ShadowArg* SA = &(argShadows[i]);
    if(SA->dieStatus != INSTSTATUS_ALIVE)
      continue;

    if(Constant* C = getConstReplacement(SA)) {
      SA->committedVal = C;
      continue;
    }
    
    if(synthCommittedPointer(ShadowValue(SA), emitBB))
      continue;

    // Finally just proxy whatever literal argument we're passed:
    SA->committedVal = getArgCommittedValue(SA);

  }

  commitInstructions();

}

void IntegrationAttempt::commitInstructions() {

  SaveProgress();
  
  if(this == getFunctionRoot() && getFunctionRoot()->isRootMainCall()) {

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

    // Emit a store to forwarding global for any arg-stores that are needed in other functions.
    for(uint32_t i = 0, ilim = F.arg_size(); i != ilim; ++i) {

      if(pass->argStores[i].fwdGV) {

	Type* VoidPtr = Type::getInt8PtrTy(F.getContext());
	Value* StoreI = getFunctionRoot()->argShadows[i].committedVal;
	
	if(StoreI->getType() != VoidPtr)
	  StoreI = new BitCastInst(StoreI, VoidPtr, "", emitBB);

	new StoreInst(StoreI, pass->argStores[i].fwdGV, emitBB);

      }

    }

  }

  uint32_t i = 0;
  commitLoopInstructions(L, i);

  // This should be the last reference to the failed block maps here: deallocate.
  finishFailedBlockCommit();

}

