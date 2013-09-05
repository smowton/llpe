
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Support/Debug.h"

#include "../../VMCore/LLVMContextImpl.h"

#include <unistd.h>
#include <stdlib.h>

using namespace llvm;

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

    if(ignoreIAs.count(cast_inst<CallInst>(it->first)))
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

  Function::arg_iterator DestI = NewF->arg_begin();
  for (Function::const_arg_iterator I = F->arg_begin(), E = F->arg_end();
       I != E; ++I, ++DestI)
    DestI->setName(I->getName());
  
  NewF->copyAttributesFrom(F);

  return NewF;

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
    
    // Skip loop-entry processing unitl we're back in local scope.
    // Can't go direct from one loop to another due to preheader.
    currentLoop = BB->invar->naturalScope;
    
    std::string Name;
    {
      raw_string_ostream RSO(Name);
      RSO << getCommittedBlockPrefix() << BB->invar->BB->getName();
    }
    BasicBlock* firstNewBlock = BasicBlock::Create(F.getContext(), Name);
    BB->committedBlocks.push_back(std::make_pair(firstNewBlock, 0));

    // The function entry block is just the first one listed: create at front if necessary.
    if((!L) && i == 0 && commitsOutOfLine())
      CF->getBasicBlockList().push_front(firstNewBlock);
    else
      CF->getBasicBlockList().push_back(firstNewBlock);
      
    // Create extra empty blocks for each path condition that's effective here:
    uint32_t nCondsHere = pass->countPathConditionsForBlock(BB);
    for(uint32_t k = 0; k < nCondsHere; ++k) {

      BasicBlock* newBlock = 
	BasicBlock::Create(F.getContext(), BB->invar->BB->getName() + ".pathcond", CF);

      BB->committedBlocks.push_back(std::make_pair(newBlock, 0));

    }

    // Determine if we need to create more BBs because of call inlining:

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* SI = &(BB->insts[j]);
      if(inst_is<CallInst>(SI)) {
	
	if(InlineAttempt* IA = getInlineAttempt(SI)) {

	  if(IA->isEnabled()) {

	    std::string Pref = IA->getCommittedBlockPrefix();

	    if(!IA->commitsOutOfLine()) {

	      // Split the specialised block:

	      IA->returnBlock = 
		BasicBlock::Create(F.getContext(), StringRef(Pref) + "callexit", CF);
	      BB->committedBlocks.push_back(std::make_pair(IA->returnBlock, j+1));
	      IA->CommitF = CF;

	      // Direct the call to the appropriate fail block:
	      if(IA->hasFailedReturnPath()) {
		
		BasicBlock* preReturn = BasicBlock::Create(CF->getContext(), "prereturn", CF);
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
	      std::string Name;
	      {
		raw_string_ostream RSO(Name);
		RSO << IA->getCommittedBlockPrefix() << "clone";
	      }

	      // Only create each shared function once.
	      if(IA->CommitF)
		continue;

	      IA->CommitF = cloneEmptyFunction(&(IA->F), GlobalValue::InternalLinkage, Name, IA->hasFailedReturnPath());
	      IA->returnBlock = 0;
	      IA->failedReturnBlock = 0;

	      // Requires a break afterwards if the target function might branch onto a failed path.
	      if(IA->hasFailedReturnPath()) {

		BasicBlock* newBlock = BasicBlock::Create(F.getContext(), StringRef(Pref) + "OOL callexit", CF);
		BB->committedBlocks.push_back(std::make_pair(newBlock, j+1));

	      }

	    }

	    IA->commitCFG();
	    continue;

	  }

	}

      }

      // If we have a disabled call, exit phi for a disabled loop, or tentative load
      // then insert a break for a check.
      if(requiresRuntimeCheck(SI)) {

	if(j + 1 != BB->insts.size() && inst_is<PHINode>(SI) && inst_is<PHINode>(&BB->insts[j+1]))
	  continue;

	BasicBlock* newSpecBlock = BasicBlock::Create(F.getContext(), StringRef(Name) + ".checkpass", CF);
	BB->committedBlocks.push_back(std::make_pair(newSpecBlock, j+1));

      }

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

  release_assert((!willBeDeleted(SV)) && "Instruction depends on deleted value");

  switch(SV.t) {
  case SHADOWVAL_INST:
    return SV.u.I->committedVal;
  case SHADOWVAL_ARG:
    return SV.u.A->committedVal;
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

  return BBs[0]->committedBlocks.front().first;

}

BasicBlock* PeelIteration::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  if(BB->invar->idx == parentPA->invarInfo->latchIdx && succIdx == parentPA->invarInfo->headerIdx) {

    if(PeelIteration* PI = getNextIteration())
      return PI->getBB(succIdx)->committedBlocks.front().first;
    else {
      if(iterStatus == IterationStatusFinal) {
	release_assert(pass->assumeEndsAfter(&F, L->getHeader(), iterationCount)
		       && "Branch to header in final iteration?");
	markUnreachable = true;
	return 0;
      }
      else
	return parent->getBB(succIdx)->committedBlocks.front().first;
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
	return PA->Iterations[0]->getBB(*SuccBBI)->committedBlocks.front().first;
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
    return SuccBB->committedBlocks.front().first;

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

Value* llvm::getValAsType(Value* V, Type* Ty, Instruction* insertBefore) {

  if(Ty == V->getType())
    return V;

  release_assert(CastInst::isCastable(V->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(V, false, Ty, false);
  return CastInst::Create(Op, V, Ty, "speccast", insertBefore);

}

Value* llvm::getValAsType(Value* V, Type* Ty, BasicBlock* insertAtEnd) {

  if(Ty == V->getType())
    return V;

  release_assert(CastInst::isCastable(V->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(V, false, Ty, false);
  return CastInst::Create(Op, V, Ty, "speccast", insertAtEnd);

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
    I->committedVal = NewPN = makePHI(I->invar->I->getType(), "header", emitBB);
    ShadowBB* SourceBB;

    if(iterationCount == 0) {

      SourceBB = parent->getBB(parentPA->invarInfo->preheaderIdx);

    }
    else {

      PeelIteration* prevIter = parentPA->Iterations[iterationCount-1];
      SourceBB = prevIter->getBB(parentPA->invarInfo->latchIdx);

    }

    // Emit any necessary casts into the predecessor block.
    Value* PHIOp = getValAsType(getCommittedValue(SourceV), PN->getType(), SourceBB->committedBlocks.back().first->getTerminator());
    NewPN->addIncoming(PHIOp, SourceBB->committedBlocks.back().first);
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
      Value* PHIOp = getValAsType(getCommittedValue(predValues[j]), NewPN->getType(), predBBs[j]->committedBlocks.back().first->getTerminator());
      NewPN->addIncoming(PHIOp, predBBs[j]->committedBlocks.back().first);
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
      if((!F.getFunctionType()->getReturnType()->isVoidTy()) && I->i.dieStatus != INSTSTATUS_ALIVE)
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
	  retVal = InsertValueInst::Create(aggTemplate, retVal, 0, "success_ret", emitBB);

	}

      }

      ReturnInst::Create(emitBB->getContext(), retVal, emitBB);

    }
    else {

      // Branch to the exit block
      Instruction* BI = BranchInst::Create(IA->returnBlock, emitBB);

      if(IA->returnPHI && I->i.dieStatus == INSTSTATUS_ALIVE) {
	Value* PHIVal = getValAsType(getCommittedValue(I->getOperand(0)), F.getFunctionType()->getReturnType(), BI);
	IA->returnPHI->addIncoming(PHIVal, BB->committedBlocks.back().first);
      }

    }

    return;

  }

  // Do we know where this terminator will go?
  uint32_t knownSucc = 0xffffffff;
  for(uint32_t i = 0; i < BB->invar->succIdxs.size(); ++i) {

    if(BB->succsAlive[i]) {

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
    Instruction* newTerm = I->invar->I->clone();
    emitBB->getInstList().push_back(newTerm);
    
    // Like emitInst, but can emit BBs.
    for(uint32_t i = 0; i < I->getNumOperands(); ++i) {

      if(I->invar->operandIdxs[i].instIdx == INVALID_INSTRUCTION_IDX && I->invar->operandIdxs[i].blockIdx != INVALID_BLOCK_IDX) {

	// Argument is a BB.
	bool markUnreachable = false;
	BasicBlock* SBB = getSuccessorBB(BB, I->invar->operandIdxs[i].blockIdx, markUnreachable);
	release_assert((SBB || markUnreachable) && "Failed to get successor BB (2)");
	if(markUnreachable) {
	  // Create an unreachable BB to branch to:
	  BasicBlock* UBB = BasicBlock::Create(emitBB->getContext(), "LoopAssumeSink", emitBB->getParent());
	  new UnreachableInst(UBB->getContext(), UBB);
	  newTerm->setOperand(i, UBB);
	}
	else
	  newTerm->setOperand(i, SBB);

      }
      else { 

	ShadowValue op = I->getOperand(i);
	Value* opV = getCommittedValue(op);
	newTerm->setOperand(i, opV);

      }

    }
    
  }

}

bool IntegrationAttempt::emitVFSCall(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  CallInst* CI = cast_inst<CallInst>(I);

  {
    DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
    if(it != resolvedReadCalls.end()) {
      
      if(it->second.readSize > 0 && !(I->i.dieStatus & INSTSTATUS_UNUSED_WRITER)) {

	LLVMContext& Context = CI->getContext();

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
	Value *DestCast = new BitCastInst(getCommittedValue(I->getCallArgOperand(1)), VoidPtrTy, "readcast", emitBB);

	Value *CallArgs[] = {
	  DestCast, CopySource, MemcpySize,
	  ConstantInt::get(Type::getInt32Ty(Context), 1),
	  ConstantInt::get(Type::getInt1Ty(Context), 0)
	};
	
	CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", emitBB);

	// Insert a seek call if that turns out to be necessary (i.e. if that FD may be subsequently
	// used without an intervening SEEK_SET)
	if(it->second.needsSeek) {

	  Type* Int64Ty = IntegerType::get(Context, 64);
	  Constant* NewOffset = ConstantInt::get(Int64Ty, it->second.incomingOffset + it->second.readSize);
	  Type* Int32Ty = IntegerType::get(Context, 32);
	  Constant* SeekSet = ConstantInt::get(Int32Ty, SEEK_SET);

	  Constant* SeekFn = F.getParent()->getOrInsertFunction("lseek64", Int64Ty /* ret */, Int32Ty, Int64Ty, Int32Ty, NULL);

	  Value* CallArgs[] = {getCommittedValue(I->getCallArgOperand(0)) /* The FD */, NewOffset, SeekSet};

	  CallInst::Create(SeekFn, ArrayRef<Value*>(CallArgs, 3), "", emitBB);
	  
	}
	
      }

      return true;

    }

  }

  {
    
    DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
    if(it != resolvedSeekCalls.end()) {

      if(!it->second.MayDelete)
	emitInst(BB, I, emitBB);

      return true;

    }

  }

  {

    DenseMap<CallInst*, OpenStatus*>::iterator it = forwardableOpenCalls.find(CI);
    if(it != forwardableOpenCalls.end()) {
      if(it->second->success && I->i.dieStatus == INSTSTATUS_ALIVE) {

	emitInst(BB, I, emitBB);

      }

      return true;
    }

  }

  {
    
    DenseMap<CallInst*, CloseFile>::iterator it = resolvedCloseCalls.find(CI);
    if(it != resolvedCloseCalls.end()) {

      if(it->second.MayDelete && it->second.openArg->MayDelete) {
	if(it->second.openInst->i.dieStatus == INSTSTATUS_DEAD)
	  return true;
      }

      emitInst(BB, I, emitBB);

      return true;

    }

  }

  return false;

}

void IntegrationAttempt::emitCall(ShadowBB* BB, ShadowInstruction* I, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator& emitBBIter) {

  BasicBlock* emitBB = emitBBIter->first;

  if(InlineAttempt* IA = getInlineAttempt(I)) {

    if(IA->isEnabled()) {

      CallInst* SavedPtr = 0;

      if(!IA->commitsOutOfLine()) {

	// Save the current stack pointer (for scoped allocas)
	Module *M = emitBB->getParent()->getParent();
	Function *StackSave = Intrinsic::getDeclaration(M, Intrinsic::stacksave);
	SavedPtr = CallInst::Create(StackSave, "savedstack", emitBB);		

	// Branch from the current write BB to the call's entry block:
	BranchInst::Create(IA->getCommittedEntryBlock(), emitBB);

	// Make a PHI node that will catch return values, and make it our committed
	// value so that users get that instead of the call.
	
	bool isNonVoid = !IA->F.getFunctionType()->getReturnType()->isVoidTy();
	bool createRetPHI = isNonVoid && !willBeReplacedOrDeleted(ShadowValue(I));
	
	if(createRetPHI) {
	  I->committedVal = IA->returnPHI = makePHI(IA->F.getFunctionType()->getReturnType(), 
						    "retval", IA->returnBlock);
	}
	else {
	  I->committedVal = 0;
	  IA->returnPHI = 0;
	}

	if(IA->hasFailedReturnPath() && isNonVoid) {
	  IA->failedReturnPHI = makePHI(IA->F.getFunctionType()->getReturnType(), 
					"failedretval", IA->failedReturnBlock);
	}
	else {
	  IA->failedReturnPHI = 0;
	}

	// Emit further instructions in this ShadowBB to the successor block:
	++emitBBIter;
	release_assert(emitBBIter->first == IA->returnBlock);
	
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
	  ShadowValue op = I->getCallArgOperand(i);
	  Value* opV = getCommittedValue(op);
	  Type* needTy;
	  if(i < FType->getNumParams()) {
	    // Normal argument: cast to target function type.
	    needTy = FType->getParamType(i);
	  }
	  else {
	    // Vararg: cast to old callinst arg type.
	    needTy = OldCI->getArgOperand(i)->getType();
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

	    CallFailed = ExtractValueInst::Create(NewCI, ArrayRef<unsigned>(1), "retfailflag", emitBB);
	    I->committedVal = ExtractValueInst::Create(NewCI, ArrayRef<unsigned>(0), "ret", emitBB);
	    
	  }

	  ++emitBBIter;
	  BasicBlock* successTarget = emitBBIter->first;
	  BasicBlock* failTarget = getFunctionRoot()->getSubBlockForInst(BB->invar->idx, I->invar->idx + 1);
	  BranchInst::Create(successTarget, failTarget, CallFailed, emitBB);

	}

      }

      if(!IA->instructionsCommitted) {
	IA->commitArgsAndInstructions();
	IA->instructionsCommitted = true;
      }
    
      if(!IA->commitsOutOfLine()) {

	Module *M = emitBB->getParent()->getParent();
	Function *StackRestore=Intrinsic::getDeclaration(M,Intrinsic::stackrestore);

	CallInst::Create(StackRestore, SavedPtr, "", IA->returnBlock);

	if(IA->failedReturnBlock) {
	  CallInst::Create(StackRestore, SavedPtr, "", IA->failedReturnBlock->getFirstNonPHI());
	  (*getFunctionRoot()->failedBlockMap)[SavedPtr] = SavedPtr;

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
  
  if(emitVFSCall(BB, I, emitBB))
    return;

  // Unexpanded call, emit it as a normal instruction.
  emitInst(BB, I, emitBB);

}

Instruction* IntegrationAttempt::emitInst(ShadowBB* BB, ShadowInstruction* I, BasicBlock* emitBB) {

  // Clone all attributes:
  Instruction* newI = I->invar->I->clone();
  I->committedVal = newI;
  emitBB->getInstList().push_back(cast<Instruction>(newI));

  // Normal instruction: no BB arguments, and all args have been committed already.
  for(uint32_t i = 0; i < I->getNumOperands(); ++i) {

    ShadowValue op = I->getOperand(i);
    Value* opV = getCommittedValue(op);
    Type* needTy = newI->getOperand(i)->getType();
    newI->setOperand(i, getValAsType(opV, needTy, newI));

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

bool IntegrationAttempt::synthCommittedPointer(ShadowValue I, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator emitBB) {

  Value* Result;
  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(getIVSRef(I));
  if((!IVS) || IVS->SetType != ValSetTypePB || IVS->Values.size() != 1)
    return false;

  bool ret = synthCommittedPointer(&I, I.getType(), IVS->Values[0], emitBB->first, Result);
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

  if(!Base.objectAvailableFrom(this))
    return false;

  return true;

}

bool IntegrationAttempt::synthCommittedPointer(ShadowValue* I, Type* targetType, ImprovedVal IV, BasicBlock* emitBB, Value*& Result) {

  if(!canSynthPointer(I, IV))
    return false;

  ShadowValue Base = IV.V;
  int64_t Offset = IV.Offset;

  Type* Int8Ptr = Type::getInt8PtrTy(emitBB->getContext());

  if(GlobalVariable* GV = cast_or_null<GlobalVariable>(Base.getVal())) {

    // Rep as a constant expression:
    Result = (getGVOffset(GV, Offset, targetType));

  }
  else {

    Value* BaseI = getCommittedValue(Base);
    release_assert(BaseI && "Synthing pointer atop uncommitted allocation");

    // Get byte ptr:
    Value* CastI;
    if(BaseI->getType() != Int8Ptr)
      CastI = new BitCastInst(BaseI, Int8Ptr, "synthcast", emitBB);
    else
      CastI = BaseI;

    // Offset:
    Value* OffsetI;
    if(Offset == 0)
      OffsetI = CastI;
    else {
      Constant* OffsetC = ConstantInt::get(Type::getInt64Ty(emitBB->getContext()), (uint64_t)Offset, true);
      OffsetI = GetElementPtrInst::Create(CastI, OffsetC, "synthgep", emitBB);
    }

    // Cast back:
    if(targetType == Int8Ptr) {
      Result = (OffsetI);
    }
    else {
      Result = (CastInst::CreatePointerCast(OffsetI, targetType, "synthcastback", emitBB));
    }

  }

  return true;

}

bool IntegrationAttempt::canSynthVal(ShadowInstruction* I, ValSetType Ty, ImprovedVal& IV) {

  if(Ty == ValSetTypeScalar)
    return true;
  else if(Ty == ValSetTypeFD)
    return (I != IV.V.getInst() && IV.V.objectAvailableFrom(this));
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
       IV.V.objectAvailableFrom(this)) {
    
      return IV.V.getInst()->committedVal;

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

void IntegrationAttempt::emitChunk(ShadowInstruction* I, BasicBlock* emitBB, SmallVector<IVSRange, 4>::iterator chunkBegin, SmallVector<IVSRange, 4>::iterator chunkEnd) {

  uint32_t chunkSize = std::distance(chunkBegin, chunkEnd);
  if(chunkSize == 0)
    return;

  Type* BytePtr = Type::getInt8PtrTy(emitBB->getContext());

  // Create pointer that should be written through:
  Type* targetType;
  if(chunkSize == 1)
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

    // Emit as simple store.
    ImprovedVal& IV = chunkBegin->second.Values[0];
    Value* newVal = trySynthVal(I, IV.V.getType(), chunkBegin->second.SetType, IV, emitBB);
    new StoreInst(newVal, targetPtrSynth, emitBB);

  }
  else {

    // Emit as memcpy-from-packed-struct.
    SmallVector<Type*, 4> Types;
    SmallVector<Constant*, 4> Copy;
    uint64_t lastOffset = 0;
    for(SmallVector<IVSRange, 4>::iterator it = chunkBegin; it != chunkEnd; ++it) {

      ImprovedVal& IV = it->second.Values[0];
      Value* newVal = trySynthVal(I, IV.V.getType(), it->second.SetType, IV, emitBB);
      Types.push_back(newVal->getType());
      Copy.push_back(cast<Constant>(newVal));
      lastOffset = it->first.second;

    }

    StructType* SType = StructType::get(emitBB->getContext(), Types, /*isPacked=*/true);
    Constant* CS = ConstantStruct::get(SType, Copy);
    GlobalVariable* GCS = new GlobalVariable(*(emitBB->getParent()->getParent()), SType, 
					     true, GlobalValue::InternalLinkage, CS);
    Constant* GCSPtr = ConstantExpr::getBitCast(GCS, BytePtr);

    Type* Int64Ty = Type::getInt64Ty(emitBB->getContext());
    Constant* MemcpySize = ConstantInt::get(Int64Ty, lastOffset - chunkBegin->first.first);

    Type *Tys[3] = {BytePtr, BytePtr, Int64Ty};
    Function *MemCpyFn = Intrinsic::getDeclaration(F.getParent(),
						   Intrinsic::memcpy, 
						   ArrayRef<Type*>(Tys, 3));

    Value *CallArgs[] = {
      targetPtrSynth, GCSPtr, MemcpySize,
      ConstantInt::get(Type::getInt32Ty(emitBB->getContext()), 1),
      ConstantInt::get(Type::getInt1Ty(emitBB->getContext()), 0)
    };
	
    CallInst::Create(MemCpyFn, ArrayRef<Value*>(CallArgs, 5), "", emitBB);

  }

}

bool IntegrationAttempt::canSynthMTI(ShadowInstruction* I) {

  if(!I->memcpyValues)
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
  
  // Can we describe all the copied values?
  for(SmallVector<IVSRange, 4>::iterator it = I->memcpyValues->begin(),
	itend = I->memcpyValues->end(); it != itend; ++it) {

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

  SmallVector<IVSRange, 4>::iterator chunkBegin = I->memcpyValues->begin();

  for(SmallVector<IVSRange, 4>::iterator it = I->memcpyValues->begin(),
	itend = I->memcpyValues->end(); it != itend; ++it) {

    if(it->second.SetType == ValSetTypeScalar || 
       (it->second.SetType == ValSetTypePB && it->second.Values[0].V.isGV())) {

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
  emitChunk(I, emitBB, chunkBegin, I->memcpyValues->end());

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

void IntegrationAttempt::emitOrSynthInst(ShadowInstruction* I, ShadowBB* BB, SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator& emitBB) {

  if(inst_is<CallInst>(I) && !inst_is<MemIntrinsic>(I)) {
    emitCall(BB, I, emitBB);
    if(I->committedVal)
      return;
    // Else fall through to fill in a committed value:
  }

  if(willBeDeleted(ShadowValue(I)) && !inst_is<TerminatorInst>(I))
    return;

  if(!requiresRuntimeCheck(I)) {

    Value* V;
    if(trySynthInst(I, emitBB->first, V)) {
      I->committedVal = V;
      return;
    }

  }

  // Already emitted calls above:
  if(inst_is<CallInst>(I) && !inst_is<MemIntrinsic>(I))
    return;

  // We'll emit an instruction. Is it special?
  if(inst_is<PHINode>(I))
    emitPHINode(BB, I, emitBB->first);
  else if(inst_is<TerminatorInst>(I))
    emitTerminator(BB, I, emitBB->first);
  else
    emitInst(BB, I, emitBB->first);

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

	SmallVector<std::pair<BasicBlock*, uint32_t>, 1> emptyVec;
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

	  populateFailedBlock(i + BBsOffset, emptyVec.begin(), emptyVec.end());
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
    SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator emitPHIsTo = BB->committedBlocks.begin();
      
    // Even if there are path conditions, emit specialised PHIs into the first block.
    for(j = 0; j < BB->insts.size() && inst_is<PHINode>(&(BB->insts[j])); ++j) {
      
      ShadowInstruction* I = &(BB->insts[j]);
      I->committedVal = 0;
      emitOrSynthInst(I, BB, emitPHIsTo);

    }

    release_assert(emitPHIsTo == BB->committedBlocks.begin() && "PHI emission should not move the emit pointer");

    // Synthesise path condition checks, using a successive emitBB for each one:
    SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator emitBlockIt = emitPathConditionChecks(BB);
    SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator pathConditionLimit = emitBlockIt;

    // If the PHI nodes are loop exit PHIs that need their values checking, emit the check.
    if(j != 0) {

      ShadowInstruction* prevSI = &BB->insts[j-1];
      if(inst_is<PHINode>(prevSI) && requiresRuntimeCheck(ShadowValue(prevSI)))
	emitBlockIt = emitExitPHIChecks(emitBlockIt, BB);

    }

    // Emit instructions for this block (using the same j index as before)
    for(; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);
      I->committedVal = 0;
      emitOrSynthInst(I, BB, emitBlockIt);

      if(requiresRuntimeCheck(ShadowValue(I)))
	emitBlockIt = emitOrdinaryInstCheck(emitBlockIt, I);

    }

    populateFailedBlock(i + BBsOffset, BB->committedBlocks.begin(), pathConditionLimit);

  }

  if(ScopeL != L) {
    populateFailedHeaderPHIs(ScopeL);
    if(BBs[thisLoopHeaderIdx])
      fixupHeaderPHIs(BBs[thisLoopHeaderIdx]);
  }

}

void InlineAttempt::commitArgsAndInstructions() {
  
  SmallVector<std::pair<BasicBlock*, uint32_t>, 1>::iterator emitBB = BBs[0]->committedBlocks.begin();
  for(uint32_t i = 0; i < F.arg_size(); ++i) {

    ShadowArg* SA = &(argShadows[i]);
    if(SA->i.dieStatus != INSTSTATUS_ALIVE)
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

  uint32_t i = 0;
  commitLoopInstructions(L, i);

}
