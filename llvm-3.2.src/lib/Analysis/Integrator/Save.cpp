
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

Function* llvm::cloneEmptyFunction(Function* F, GlobalValue::LinkageTypes LT, const Twine& Name) {

  Function* NewF = Function::Create(F->getFunctionType(), LT, Name, F->getParent());

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

  for(uint32_t i = 0; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    if(currentLoop == L && BB->invar->naturalScope != L) {

      // Entering a loop. First write the blocks for each iteration that's being unrolled:
      PeelAttempt* PA = getPeelAttempt(BB->invar->naturalScope);
      if(PA && PA->isEnabled()) {
	for(unsigned i = 0; i < PA->Iterations.size(); ++i)
	  PA->Iterations[i]->commitCFG();
      }
      
      // If the loop has terminated, skip emitting the blocks in this context.
      if(PA && PA->isEnabled() && PA->isTerminated()) {
	const Loop* skipL = BB->invar->naturalScope;
	while(i < nBBs && ((!BBs[i]) || skipL->contains(BBs[i]->invar->naturalScope)))
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
    BB->committedTail = BB->committedHead = BasicBlock::Create(F.getContext(), Name, CF);

    // Determine if we need to create more BBs because of call inlining:

    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* SI = &(BB->insts[j]);
      if(inst_is<CallInst>(SI)) {
	
	if(InlineAttempt* IA = getInlineAttempt(SI)) {

	  if(IA->isEnabled()) {

	    if(!IA->commitsOutOfLine()) {

	      std::string Name;
	      {
		raw_string_ostream RSO(Name);
		RSO << IA->getCommittedBlockPrefix() << "callexit";
	      }
	      BB->committedTail = IA->returnBlock = BasicBlock::Create(F.getContext(), Name, CF);
	      IA->CommitF = CF;

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

	      IA->CommitF = cloneEmptyFunction(&(IA->F), GlobalValue::InternalLinkage, Name);
	      IA->returnBlock = 0;

	    }

	    IA->commitCFG();

	  }

	}

      }

    }

  }

}

static Value* getCommittedValue(ShadowValue SV) {

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

  return BBs[0]->committedHead;

}

ShadowBB* PeelIteration::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  if(BB->invar->idx == parentPA->invarInfo->latchIdx && succIdx == parentPA->invarInfo->headerIdx) {

    if(PeelIteration* PI = getNextIteration())
      return PI->getBB(succIdx);
    else {
      if(iterStatus == IterationStatusFinal) {
	release_assert(pass->assumeEndsAfter(&F, L->getHeader(), iterationCount)
		       && "Branch to header in final iteration?");
	markUnreachable = true;
	return 0;
      }
      else
	return parent->getBB(succIdx);
    }

  }

  return IntegrationAttempt::getSuccessorBB(BB, succIdx, markUnreachable);

}

ShadowBB* IntegrationAttempt::getSuccessorBB(ShadowBB* BB, uint32_t succIdx, bool& markUnreachable) {

  ShadowBBInvar* SuccBBI = getBBInvar(succIdx);

  ShadowBB* SuccBB;
  if((!SuccBBI->naturalScope) || SuccBBI->naturalScope->contains(L))
    SuccBB = getBBFalling(SuccBBI);
  else {

    // Else, BBI is further in than this block: we must be entering exactly one loop.
    // Only enter if we're emitting the loop in its proper scope: otherwise we're
    // writing the residual version of a loop.
    if(BB->invar->outerScope == L) {
      if(PeelAttempt* PA = getPeelAttempt(SuccBBI->naturalScope)) {
	if(PA->isEnabled())
	  return PA->Iterations[0]->getBB(*SuccBBI);
      }
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
  return SuccBB;

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

static Value* getValAsType(Value* V, Type* Ty, Instruction* insertBefore) {

  if(Ty == V->getType())
    return V;

  release_assert(CastInst::isCastable(V->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(V, false, Ty, false);
  return CastInst::Create(Op, V, Ty, "speccast", insertBefore);

}

static Value* getValAsType(Value* V, Type* Ty, BasicBlock* insertAtEnd) {

  if(Ty == V->getType())
    return V;

  release_assert(CastInst::isCastable(V->getType(), Ty) && "Bad cast in commit stage");
  Instruction::CastOps Op = CastInst::getCastOpcode(V, false, Ty, false);
  return CastInst::Create(Op, V, Ty, "speccast", insertAtEnd);

}

static PHINode* makePHI(Type* Ty, const Twine& Name, BasicBlock* emitBB) {

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
    Value* PHIOp = getValAsType(getCommittedValue(SourceV), PN->getType(), SourceBB->committedTail->getTerminator());
    NewPN->addIncoming(PHIOp, SourceBB->committedTail);
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

  getExitPHIOperands(SI, valOpIdx, ops, BBs, true);


}

void IntegrationAttempt::populatePHINode(ShadowBB* BB, ShadowInstruction* I, PHINode* NewPN) {

  // Special case: populating the header PHI of a residualised loop that has some specialised iterations.
  // Populate with PHI([latch_value, last_spec_latch], [latch_value, general_latch])
  // This can't be a header of an terminated loop or that of a specialised iteration since populate
  // is not called for those.

  if(BB->invar->naturalScope && BB->invar->BB == BB->invar->naturalScope->getHeader()) {
    if(PeelAttempt* PA = getPeelAttempt(BB->invar->naturalScope)) {
      if(PA->isEnabled()) {

	// Find the latch arg:
	uint32_t latchIdx = PA->invarInfo->latchIdx;
	int latchOperand = cast<PHINode>(I->invar->I)->
	  getBasicBlockIndex(BB->invar->naturalScope->getLoopLatch());
	release_assert(latchOperand >= 0);

	ShadowValue lastLatchOperand, generalLatchOperand;
	
	ShadowInstIdx& valIdx = I->invar->operandIdxs[latchOperand];
	if(valIdx.blockIdx == INVALID_BLOCK_IDX || valIdx.instIdx == INVALID_INSTRUCTION_IDX) {
	  lastLatchOperand = I->getOperand(latchOperand);
	  generalLatchOperand = lastLatchOperand;
	}
	else {
	  lastLatchOperand = ShadowValue(PA->Iterations.back()->getInst(valIdx.blockIdx, valIdx.instIdx));
	  generalLatchOperand = ShadowValue(getInst(valIdx.blockIdx, valIdx.instIdx));
	}

	// Right, build the PHI:
	BasicBlock* lastLatchBlock = PA->Iterations.back()->getBB(latchIdx)->committedTail;
	BasicBlock* generalLatchBlock = getBB(latchIdx)->committedTail;

	Value* lastLatchVal = getValAsType(getCommittedValue(lastLatchOperand), NewPN->getType(), lastLatchBlock->getTerminator());
	Value* generalLatchVal = getValAsType(getCommittedValue(generalLatchOperand), NewPN->getType(), lastLatchBlock->getTerminator());

	NewPN->addIncoming(lastLatchVal, lastLatchBlock);
	NewPN->addIncoming(generalLatchVal, generalLatchBlock);

	return;

      }
    }
  }

  // Emit a normal PHI; all arguments have already been prepared.
  for(uint32_t i = 0, ilim = I->invar->operandIdxs.size(); i != ilim; i++) {
      
    SmallVector<ShadowValue, 1> predValues;
    SmallVector<ShadowBB*, 1> predBBs;
    getCommittedExitPHIOperands(I, i, predValues, &predBBs);

    for(uint32_t j = 0; j < predValues.size(); ++j) {
      Value* PHIOp = getValAsType(getCommittedValue(predValues[j]), NewPN->getType(), predBBs[j]->committedTail->getTerminator());
      NewPN->addIncoming(PHIOp, predBBs[j]->committedTail);
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

      if((!F.getReturnType()->isVoidTy()) && I->i.dieStatus != INSTSTATUS_ALIVE) {
	// Return a null value, since this isn't used:
	Constant* retVal = Constant::getNullValue(F.getReturnType());
	ReturnInst::Create(emitBB->getContext(), retVal, emitBB);
      }
      else {
	// Normal return (vararg function or root function)
	emitInst(BB, I, emitBB);
      }

    }
    else {

      // Branch to the exit block
      Instruction* BI = BranchInst::Create(IA->returnBlock, emitBB);

      if(IA->returnPHI && I->i.dieStatus == INSTSTATUS_ALIVE) {
	Value* PHIVal = getValAsType(getCommittedValue(I->getOperand(0)), F.getFunctionType()->getReturnType(), BI);
	IA->returnPHI->addIncoming(PHIVal, BB->committedTail);
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
    ShadowBB* SBB = getSuccessorBB(BB, knownSucc, markUnreachable);
    release_assert((SBB || markUnreachable) && "Failed to get successor BB");
    if(markUnreachable)
      new UnreachableInst(emitBB->getContext(), emitBB);
    else
      BranchInst::Create(SBB->committedHead, emitBB);

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
	ShadowBB* SBB = getSuccessorBB(BB, I->invar->operandIdxs[i].blockIdx, markUnreachable);
	release_assert((SBB || markUnreachable) && "Failed to get successor BB (2)");
	if(markUnreachable) {
	  // Create an unreachable BB to branch to:
	  BasicBlock* UBB = BasicBlock::Create(emitBB->getContext(), "LoopAssumeSink", emitBB->getParent());
	  new UnreachableInst(UBB->getContext(), UBB);
	  newTerm->setOperand(i, UBB);
	}
	else
	  newTerm->setOperand(i, SBB->committedHead);

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

void IntegrationAttempt::emitCall(ShadowBB* BB, ShadowInstruction* I, BasicBlock*& emitBB) {

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

	bool createRetPHI = !IA->F.getFunctionType()->getReturnType()->isVoidTy();
	if(createRetPHI && willBeReplacedOrDeleted(ShadowValue(I)))
	  createRetPHI = false;
	
	if(createRetPHI)
	  I->committedVal = IA->returnPHI = makePHI(IA->F.getFunctionType()->getReturnType(), "retval", IA->returnBlock);
	else {
	  I->committedVal = 0;
	  IA->returnPHI = 0;
	}

	// Emit further instructions in this ShadowBB to the successor block:
	emitBB = IA->returnBlock;
	
      }
      else {

	FunctionType* FType = IA->CommitF->getFunctionType();
	bool mustReconstruct = false;

	// Resolved calls through a function pointer might produce a type mismatch.
	// Only allow shortening the argument list at the moment.
	  
	if(!FType->isVarArg()) {
	  
	  unsigned FParams = FType->getNumParams();
	  unsigned CIParams = cast_inst<CallInst>(I)->getNumArgOperands();

	  if(FParams < CIParams) {
	    mustReconstruct = true;
	  }
	  else if(FParams > CIParams) {
	    release_assert(0 && "Function has higher arity than call");
	  }

	  FunctionType* CIFType = cast<FunctionType>(cast<PointerType>(cast_inst<CallInst>(I)->getCalledValue()->getType())->getElementType());
	  if(CIFType->getReturnType()->isVoidTy() && !FType->getReturnType()->isVoidTy())
	    mustReconstruct = true;

	}

	if(!mustReconstruct) {

	  CallInst* CI = cast<CallInst>(I->invar->I->clone());
	  I->committedVal = CI;
	  emitBB->getInstList().push_back(CI);

	  for(uint32_t i = 0, ilim = CI->getNumArgOperands(); i != ilim; ++i) {

	    ShadowValue op = I->getCallArgOperand(i);
	    Value* opV = getCommittedValue(op);
	    Type* needTy;
	    if(i < FType->getNumParams()) {
	      // Normal argument: cast to target function type.
	      needTy = FType->getParamType(i);
	    }
	    else {
	      // Vararg: cast to old callinst arg type.
	      needTy = CI->getArgOperand(i)->getType();
	    }
	    CI->setArgOperand(i, getValAsType(opV, needTy, CI));

	  }

	  CI->setCalledFunction(IA->CommitF);

	}
	else {

	  // Build a call to IA->CommitF with same attributes but less arguments.
	  // Most of this code borrowed from Transforms/IPO/DeadArgumentElimination.cpp

	  errs() << "Rebuilt call\n";

	  CallInst* OldCI = cast_inst<CallInst>(I);

	  SmallVector<AttributeWithIndex, 8> AttributesVec;
	  const AttrListPtr &CallPAL = OldCI->getAttributes();

	  Attributes FnAttrs = CallPAL.getFnAttributes();
	  
	  std::vector<Value*> Args;
	  for(uint32_t i = 0, ilim = FType->getNumParams(); i != ilim; ++i) {
	    
	    Attributes Attrs = CallPAL.getParamAttributes(i + 1);
	    if(Attrs.hasAttributes())
	      AttributesVec.push_back(AttributeWithIndex::get(Args.size(), Attrs));

	    // (Except this bit, a clone of emitInst)
	    ShadowValue op = I->getCallArgOperand(i);
	    Value* opV = getCommittedValue(op);
	    Type* needTy = FType->getParamType(i);
	    Args.push_back(getValAsType(opV, needTy, emitBB));

	  }

	  if (FnAttrs.hasAttributes())
	    AttributesVec.push_back(AttributeWithIndex::get(AttrListPtr::FunctionIndex,
							    FnAttrs));
	  
	  AttrListPtr NewCallPAL = AttrListPtr::get(IA->CommitF->getContext(), AttributesVec);

	  CallInst* newI = cast<CallInst>(CallInst::Create(IA->CommitF, Args, "", emitBB));
	  newI->setCallingConv(OldCI->getCallingConv());
	  newI->setAttributes(NewCallPAL);
	  if(OldCI->isTailCall())
	    newI->setTailCall();
	  newI->setDebugLoc(OldCI->getDebugLoc());
	  
	  I->committedVal = newI;

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

bool IntegrationAttempt::synthCommittedPointer(ShadowValue I, BasicBlock* emitBB) {

  ShadowValue Base;
  int64_t Offset;
  if(!getBaseAndConstantOffset(I, Base, Offset))
    return false;
  
  if(Base == I)
    return false;

  if(!Base.objectAvailableFrom(this))
    return false;

  Type* Int8Ptr = Type::getInt8PtrTy(I.getLLVMContext());

  if(GlobalVariable* GV = cast_or_null<GlobalVariable>(Base.getVal())) {

    // Rep as a constant expression:
    I.setCommittedVal(getGVOffset(GV, Offset, I.getType()));

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
      Constant* OffsetC = ConstantInt::get(Type::getInt64Ty(I.getLLVMContext()), (uint64_t)Offset, true);
      OffsetI = GetElementPtrInst::Create(CastI, OffsetC, "synthgep", emitBB);
    }

    // Cast back:
    if(I.getType() == Int8Ptr) {
      I.setCommittedVal(OffsetI);
    }
    else {
      I.setCommittedVal(CastInst::CreatePointerCast(OffsetI, I.getType(), "synthcastback", emitBB));
    }

  }

  return true;

}

void IntegrationAttempt::emitOrSynthInst(ShadowInstruction* I, ShadowBB* BB, BasicBlock*& emitBB) {

  if(inst_is<CallInst>(I) && !inst_is<MemIntrinsic>(I)) {
    emitCall(BB, I, emitBB);
    if(I->committedVal)
      return;
    // Else fall through to fill in a committed value:
  }

  if(willBeDeleted(ShadowValue(I)) && !inst_is<TerminatorInst>(I))
    return;

  if(Constant* C = getConstReplacement(ShadowValue(I))) {
    I->committedVal = C;
    return;
  }

  ImprovedValSetSingle* IVS = dyn_cast_or_null<ImprovedValSetSingle>(I->i.PB);

  if(IVS && 
     IVS->SetType == ValSetTypeFD && 
     IVS->Values.size() == 1 && 
     I != IVS->Values[0].V.getInst() && 
     IVS->Values[0].V.objectAvailableFrom(this)) {

    I->committedVal = IVS->Values[0].V.getInst()->committedVal;
    return;

  }
      
  if(synthCommittedPointer(ShadowValue(I), emitBB))
    return;

  // Already emitted calls above:
  if(inst_is<CallInst>(I) && !inst_is<MemIntrinsic>(I))
    return;

  // We'll emit an instruction. Is it special?
  if(inst_is<PHINode>(I))
    emitPHINode(BB, I, emitBB);
  else if(inst_is<TerminatorInst>(I))
    emitTerminator(BB, I, emitBB);
  else
    emitInst(BB, I, emitBB);

}

void IntegrationAttempt::commitLoopInstructions(const Loop* ScopeL, uint32_t& i) {

  uint32_t thisLoopHeaderIdx = i;

  for(; i < nBBs; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    if(ScopeL && !ScopeL->contains(BB->invar->naturalScope))
      break;

    if(BB->invar->naturalScope != ScopeL) {

      // Entering a loop. First write the blocks for each iteration that's being unrolled:
      PeelAttempt* PA = getPeelAttempt(BB->invar->naturalScope);
      if(PA && PA->isEnabled()) {

	for(unsigned j = 0; j < PA->Iterations.size(); ++j)
	  PA->Iterations[j]->commitInstructions();

      }
      
      // If the loop has terminated, skip populating the blocks in this context.
      if(PA && PA->isEnabled() && PA->isTerminated()) {
	const Loop* skipL = BB->invar->naturalScope;
	while(i < nBBs && ((!BBs[i]) || skipL->contains(BBs[i]->invar->naturalScope)))
	  ++i;
      }
      else {
	// Emit blocks for the residualised loop
	// (also has the side effect of winding us past the loop)
	commitLoopInstructions(BB->invar->naturalScope, i);
      }

      --i;
      continue;

    }

    BasicBlock* emitBB = BB->committedHead;

    // Emit instructions for this block:
    for(uint32_t j = 0; j < BB->insts.size(); ++j) {

      ShadowInstruction* I = &(BB->insts[j]);
      I->committedVal = 0;
      emitOrSynthInst(I, BB, emitBB);

    }    

  }
  
  if(ScopeL != L)
    fixupHeaderPHIs(BBs[thisLoopHeaderIdx]);

}

void InlineAttempt::commitArgsAndInstructions() {
  
  BasicBlock* emitBB = BBs[0]->committedHead;
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
