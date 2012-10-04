
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

using namespace llvm;

// Root entry point for saving our results:
void IntegrationAttempt::commit() {

  ValueMap<const Value*, Value*> rootValMap;

  // Assemble an identity map for the first integration:
  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    rootValMap[FI] = FI;

    for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; ++BI) {

      rootValMap[BI] = BI;

    }

  }

  prepareCommit();

  commitInContext(LI[&F], rootValMap);

  commitPointers();

}

// Prepare for the commit: remove instruction mappings that are (a) invalid to write to the final program
// and (b) difficult to reason about once the loop structures start to be modified by unrolling and so on.

void IntegrationAttempt::prepareCommit() {
  
  localPrepareCommit();

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if(ignoreIAs.count(it->first))
      continue;

    it->second->prepareCommit();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    if(ignorePAs.count(it->first))
      continue;

    unsigned iterCount = it->second->Iterations.size();
    unsigned iterLimit = (it->second->Iterations.back()->iterStatus == IterationStatusFinal) ? iterCount : iterCount - 1;

    for(unsigned i = 0; i < iterLimit; ++i) {

      it->second->Iterations[i]->prepareCommit();

    }

  }  

}

void IntegrationAttempt::removeBlockFromLoops(BasicBlock* BB) {

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    std::vector<BasicBlock*>& Blocks = it->second->LoopBlocks;
    std::vector<BasicBlock*>::iterator Found = std::find(Blocks.begin(), Blocks.end(), BB);
    if(Found != Blocks.end()) {
      Blocks.erase(Found);
      it->second->removeBlockFromLoops(BB);
    }

  }

}

void PeelAttempt::removeBlockFromLoops(BasicBlock* BB) {

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->removeBlockFromLoops(BB);

  }

}

void IntegrationAttempt::localPrepareCommit() {

  // Remove loop header values, since these are removed by the loop unroller and are realised
  // by RAUW'ing the PHI node with one of its arguments rather than by directly replacing it.
  if(const Loop* L = getLoopContext()) {

    BasicBlock* H = L->getHeader();
    for(BasicBlock::iterator it = H->begin(), it2 = H->end(); it != it2 && isa<PHINode>(it); ++it) {

      Value* V = it;
      deadValues.erase(V);
      improvedValues.erase(V);

    }

  }

  // Remove any return instructions from consideration, since the inliner will take care of them for us
  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    TerminatorInst* TI = FI->getTerminator();
    if(isa<ReturnInst>(TI)) {

      deadValues.erase(TI);

    }

  }

  // Remove loop blocks which are invariant dead from the list of blocks belonging to that loop
  // This will stop the integration within that loop from considering it.

  for(DenseMap<BasicBlock*, const Loop*>::iterator BI = invariantBlocks.begin(), BE = invariantBlocks.end(); BI != BE; ++BI) {

    if(BI->second == getLoopContext()) {

      if(deadBlocks.count(BI->first)) {

	LPDEBUG("Removing invariant block " << BI->first->getName() << " from child contexts\n");
	removeBlockFromLoops(BI->first);

      }

    }

  }
  
}

void IntegrationAttempt::commitInContext(LoopInfo* MasterLI, ValueMap<const Value*, Value*>& valMap) {

  // First apply all local definitions and kills. Store the map from the Values we know to
  // Values as integrated into the program for the second phase when we resolve pointers,
  // and resolve constants / dead code now.

  this->MasterLI = MasterLI;
  CommittedValues.insert(valMap.begin(), valMap.end());

  // Step 1: perform local integration that doesn't use outside pointers.
  // This includes establishing any loop invariants, which will be caught up
  // in the loop peeling section below, as well as replacing users of calls
  // with the values they return, if we know them.

  commitLocalConstants(CommittedValues);

  // Step 2: inline each child call

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if(ignoreIAs.count(it->first))
      continue;

    // Find the call instruction we're actually inlining:

    CallInst* CI = cast<CallInst>(CommittedValues[it->first]);

    ValueMap<const Value*, Value*> childMap;
    // This both inputs argument values and returns a map from instructions
    // as we know them to instructions in the inlined function body.

    Function* Called = getCalledFunction(it->first);
    assert(Called && "Unresolved call inlined?!");

    // As we have already RAUW'd constants, a constant argument will be picked up by the inliner
    // if appropriate. Otherwise it will get caught up in the phase 2 pointer resolution.

    InlineFunctionInfo IFI(0, TD);

    // Get my loop context as it will be written:

    const Loop* MyL = getLoopContext();
    if(MyL) {

      MyL = MasterLI->getLoopFor(cast<BasicBlock>(CommittedValues[MyL->getHeader()]));

    }

    if(!InlineFunction(CI, IFI, &childMap, MasterLI, const_cast<Loop*>(MyL), LI[Called]))
      assert(0 && "Inlining failed!\n");

    // childMap is now a map from the instructions' "real" names to those inlined.
    // Use it to commit changes known about that context:
    it->second->commitInContext(MasterLI, childMap);

  }

  // Step 3: peel each child loop
  
  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    if(ignorePAs.count(it->first))
      continue;

    // Get the loop we're actually dealing with, since we're probably dealing with a loop whose blocks have
    // been renamed many times.

    Loop* L = MasterLI->getLoopFor(cast<BasicBlock>(CommittedValues[it->first->getHeader()]));

    bool completelyUnrollLoop = it->second->Iterations.back()->iterStatus == IterationStatusFinal;
    unsigned unrollCount = it->second->Iterations.size();

    // Take a copy of the block list before we clone them:
    std::vector<BasicBlock*> LBlocks = L->getBlocks();

    std::vector<ValueMap<const Value*, Value*>* > iterValues;

    if(!UnrollLoop(L, unrollCount, LI[&F], 0, !completelyUnrollLoop, completelyUnrollLoop, &iterValues)) {

      assert(0 && "Unrolling failed");

    }

    // The vector now contains ValueMaps which map from the instructions we just cloned to those which represent
    // each peeled iteration, starting from iteration 2 (iteration 1 retains the existing instructions).
    // However, the instructions we're operating on right now aren't necessarily the originals as we have
    // likely been inlined and peeled a few levels deep.

    // For example, suppose this context is an inlined function -- then the instruction we called %2 is probably
    // %__2 because we've been inlined into some context. Then we cloned %__2 to make %__2-1, %__2-2, etc.
    // The loop iterations still expect the instruction to be named "%2", however.
    // Therefore we must compose the two maps.

    int iterLimit = completelyUnrollLoop ? unrollCount : unrollCount - 1;

    // Process the loop iterations backwards to avoid altering the original blocks

    for(int i = iterLimit - 1; i >= 0; --i) {

      ValueMap<const Value*, Value*>* childValues;
      ValueMap<const Value*, Value*> composedValues;
      
      if(i == 0) {
	childValues = &CommittedValues;
      }
      else {

	ValueMap<const Value*, Value*>& thisIterValues = *(iterValues[i-1]);

	DenseSet<Value*> loopValues;
	childValues = &composedValues;

	for(std::vector<BasicBlock*>::iterator BI = LBlocks.begin(), BE = LBlocks.end(); BI != BE; ++BI) {

	  loopValues.insert(*BI);

	  for(BasicBlock::iterator II = (*BI)->begin(), IE = (*BI)->end(); II != IE; ++II) {

	    loopValues.insert(II);

	  }

	}

	// Now write the value side of the composed map:

	for(ValueMap<const Value*, Value*>::iterator VI = CommittedValues.begin(), VE = CommittedValues.end(); VI != VE; ++VI) {

	  if(loopValues.count(VI->second)) {

	    composedValues[VI->first] = thisIterValues[VI->second];

	  }

	}
	
      }

      // Commit constant results to this iteration:

      it->second->Iterations[i]->commitInContext(MasterLI, *childValues);

    }

    for(std::vector<ValueMap<const Value*, Value*>* >::iterator it = iterValues.begin(), it2 = iterValues.end(); it != it2; ++it) {

      delete (*it);

    }

  }

}

void IntegrationAttempt::commitPointers() {

  commitLocalPointers();

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if(ignoreIAs.count(it->first))
      continue;

    it->second->commitPointers();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    if(ignorePAs.count(it->first))
      continue;

    unsigned iterCount = it->second->Iterations.size();
    unsigned iterLimit = (it->second->Iterations.back()->iterStatus == IterationStatusFinal) ? iterCount : iterCount - 1;

    for(int i = (iterLimit - 1); i >= 0; --i) {

      it->second->Iterations[i]->commitPointers();

    }

  }

}

void IntegrationAttempt::deleteInstruction(Instruction* I) {

  if(!I->use_empty())
    I->replaceAllUsesWith(UndefValue::get(I->getType()));
  I->getParent()->getInstList().erase(I);

}

void IntegrationAttempt::tryDeleteDeadBlock(BasicBlock* BB) {

  if(!deadBlocks.count(BB))
    return;

  ValueMap<const Value*, Value*>::iterator it = CommittedValues.find(BB);

  // Check if the BB was not cloned to begin with (indicating it's invariant dead)
  if(it == CommittedValues.end())
    return;

  // Get the copy of the block we should actually operate on:
  BB = cast<BasicBlock>(it->second);

  LPDEBUG("Deleting block " << BB->getName() << "\n");

  MasterLI->removeBlock(BB);
  
  // Remove all instructions in the block first:
  while(!(BB->begin() == BB->end())) {

    deleteInstruction(--BasicBlock::iterator(BB->end()));

  }

  BB->eraseFromParent();

}

void IntegrationAttempt::replaceKnownBranch(BasicBlock* FromBB, TerminatorInst* TI) {

  bool isDead = deadBlocks.count(FromBB);
  BasicBlock* Target = 0;

  // Return instructions have been replaced already by the inliner!
  if(isa<ReturnInst>(TI))
    return;

  TerminatorInst* ReplaceTI = cast_or_null<TerminatorInst>(CommittedValues[TI]);
  // Terminators might not exist if this is an invariant branch which was replaced outside.
  if(!ReplaceTI)
    return;

  BasicBlock* ReplaceTarget = 0;

  if(!isDead) {

    // Careful: using ReplaceTI not TI because TI probably still belongs to a version of the blocks
    // which is still rolled (e.g. loop 1 contains loop 2; loop 1 was unrolled to two iterations
    // creating 2.1 and 2.2; we're now unrolling 2.2 but the original blocks reside in 2.1 and are
    // rolled) I think all branches that aren't the loop latch will look the same as the rolled version.
    const unsigned NumSucc = ReplaceTI->getNumSuccessors();

    // Loop unrolling replaces loop latch branches with unconditionals, so this skips them too.
    if(NumSucc <= 1)
      return;

    for (unsigned I = 0; I != NumSucc; ++I) {

      // Back to using the original blocks here since our results are calculated in their terms
      BasicBlock* thisTarget = TI->getSuccessor(I);
      if(!deadEdges.count(std::make_pair(FromBB, thisTarget))) {

	if(Target)
	  return;
	else
	  Target = thisTarget;

      }

    }

    if(!Target)
      return;

    // If the target isn't in the map then it's from outside this context, leave it alone.
    ValueMap<const Value*, Value*>::iterator it = CommittedValues.find(Target);
    if(it == CommittedValues.end())
      ReplaceTarget = Target;
    else
      ReplaceTarget = cast<BasicBlock>(it->second);

  }

  if(!isDead)
    LPDEBUG("Replace terminator " << *ReplaceTI << " with branch to " << ReplaceTarget->getName() << "\n");
  else
    LPDEBUG("Replace terminator " << *ReplaceTI << " with unreachable\n");

  BasicBlock* ReplaceSource = ReplaceTI->getParent();

  for(unsigned i = 0; i < ReplaceTI->getNumSuccessors(); ++i) {
    
    BasicBlock* Succ = ReplaceTI->getSuccessor(i);
    if(Succ != ReplaceTarget)
      Succ->removePredecessor(ReplaceSource, true /* Don't delete 1-arg PHI nodes */);

  }

  CommittedValues.erase(TI);
  ReplaceTI->eraseFromParent();

  if(ReplaceTarget)
    BranchInst::Create(ReplaceTarget, ReplaceSource);
  else
    new UnreachableInst(ReplaceSource->getParent()->getContext(), ReplaceSource);

}

void InlineAttempt::replaceKnownBranches() {

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    // This should be ok because loop unrolling never replaces branch instructions, whenever
    // it modifies one it does so in place.
    replaceKnownBranch(FI, FI->getTerminator());

  }

}

void PeelIteration::replaceKnownBranches() {

  for(std::vector<BasicBlock*>::iterator it = parentPA->LoopBlocks.begin(), it2 = parentPA->LoopBlocks.end(); it != it2; ++it) {

    replaceKnownBranch(*it, (*it)->getTerminator());

  }

}

void InlineAttempt::deleteDeadBlocks() {

  std::vector<BasicBlock*> FBlocks(F.size());
  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI)
    FBlocks.push_back(FI);

  for(std::vector<BasicBlock*>::iterator FI = FBlocks.begin(), FE = FBlocks.end(); FI != FE; ++FI) {

    tryDeleteDeadBlock(*FI);

  }

}

void PeelIteration::deleteDeadBlocks() {

  for(std::vector<BasicBlock*>::iterator it = parentPA->LoopBlocks.begin(), it2 = parentPA->LoopBlocks.end(); it != it2; ++it) {

    tryDeleteDeadBlock(*it);

  }  

}

void IntegrationAttempt::markOrDeleteCloseCall(CallInst* CI, IntegrationAttempt* OpenCtx) {

  if(commitStarted && OpenCtx != this) {

    // We've already committed our local constants: zap it.
    CI->eraseFromParent();

  }
  else {

    // Mark it to be collected later:
    resolvedCloseCalls[CI].canRemove = true;

  }

}

void IntegrationAttempt::foldVFSCalls() {

  for(DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.begin(), it2 = resolvedReadCalls.end(); it != it2; ++it) {

    CallInst* CI = it->first;
    CallInst* ReplaceCI = cast<CallInst>(CommittedValues[CI]);
    
    LLVMContext& Context = ReplaceCI->getContext();

    if(it->second.readSize > 0 && !unusedWriters.count(CI)) {

      // Create a memcpy from a constant, since someone is still using the read data.
      std::vector<Constant*> constBytes;
      std::string errors;
      assert(getFileBytes(it->second.openArg->Name, it->second.incomingOffset, it->second.readSize, constBytes, Context,  errors));
      
      const ArrayType* ArrType = ArrayType::get(IntegerType::get(Context, 8), constBytes.size());
      Constant* ByteArray = ConstantArray::get(ArrType, constBytes);

      // Create a const global for the array:

      GlobalVariable *ArrayGlobal = new GlobalVariable(*(ReplaceCI->getParent()->getParent()->getParent()), ArrType, true, GlobalValue::PrivateLinkage, ByteArray, "");

      const Type* Int64Ty = IntegerType::get(Context, 64);
      const Type *VoidPtrTy = Type::getInt8PtrTy(Context);

      Constant* ZeroIdx = ConstantInt::get(Int64Ty, 0);
      Constant* Idxs[2] = {ZeroIdx, ZeroIdx};
      Constant* CopySource = ConstantExpr::getGetElementPtr(ArrayGlobal, Idxs, 2);
      
      Constant* MemcpySize = ConstantInt::get(Int64Ty, constBytes.size());

      const Type *Tys[3] = {VoidPtrTy, VoidPtrTy, Int64Ty};
      Function *MemCpyFn = Intrinsic::getDeclaration(F.getParent(),
						     Intrinsic::memcpy, 
						     Tys, 3);
      Value *DestCast = new BitCastInst(ReplaceCI->getArgOperand(1), VoidPtrTy, "tmp", ReplaceCI);

      Value *CallArgs[] = {
	DestCast, CopySource, MemcpySize,
	ConstantInt::get(Type::getInt32Ty(Context), 1),
	ConstantInt::get(Type::getInt1Ty(Context), 0)
      };

      CallInst::Create(MemCpyFn, CallArgs, CallArgs+5, "", ReplaceCI);

    }

    // Insert a seek call if the next user isn't resolved:
    if(it->second.NextUser == VCNull || !it->second.NextUser.second->isAvailable()) {

      const Type* Int64Ty = IntegerType::get(Context, 64);
      Constant* NewOffset = ConstantInt::get(Int64Ty, it->second.incomingOffset + it->second.readSize);
      const Type* Int32Ty = IntegerType::get(Context, 32);
      Constant* SeekSet = ConstantInt::get(Int32Ty, SEEK_SET);

      Constant* SeekFn = F.getParent()->getOrInsertFunction("lseek64", Int64Ty /* ret */, Int32Ty, Int64Ty, Int32Ty, NULL);

      Value* CallArgs[] = {ReplaceCI->getArgOperand(0) /* The FD */, NewOffset, SeekSet};

      CallInst::Create(SeekFn, CallArgs, CallArgs+3, "", ReplaceCI);

    }

    // Uses of the read have been replaced already.
    ReplaceCI->eraseFromParent();

  }

  for(DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.begin(), it2 = resolvedSeekCalls.end(); it != it2; ++it) {

    // Delete the seek call if the next user is known.
    if(it->second.NextUser != VCNull && it->second.NextUser.second->isAvailable()) {
      cast<Instruction>(CommittedValues[it->first])->eraseFromParent();
    }

  }

  for(DenseMap<CallInst*, OpenStatus>::iterator it = forwardableOpenCalls.begin(), it2 = forwardableOpenCalls.end(); it != it2; ++it) {
    
    // Can't delete open if it has direct users still!
    if(!deadValues.count(it->first))
      continue;

    ValCtx closeCall = VCNull;

    // Delete an open call if its chain is entirely available and the open is dead (not directly used).
    for(ValCtx NextUser = it->second.FirstUser; NextUser != VCNull;) {

      if(!NextUser.second->isAvailable())
	break;
      if(NextUser.second->isCloseCall(cast<CallInst>(NextUser.first))) {
	closeCall = NextUser;
	break;
      }

      NextUser = NextUser.second->getNextVFSUser(cast<CallInst>(NextUser.first));

    }

    if(closeCall != VCNull) {

      deleteInstruction(it->first);
      closeCall.second->markOrDeleteCloseCall(cast<CallInst>(closeCall.first), this);

    }

  }

  for(DenseMap<CallInst*, CloseFile>::iterator it = resolvedCloseCalls.begin(), it2 = resolvedCloseCalls.end(); it != it2; ++it) {

    if(it->second.canRemove)
      it->first->eraseFromParent();

  }

}

void IntegrationAttempt::commitLocalConstants(ValueMap<const Value*, Value*>& VM) {

  // Commit anything that's simple: commit simple constants, dead blocks and edges.

  // Delete instructions that are certainly no longer needed:
  for(DenseSet<Value*>::iterator it = deadValues.begin(), it2 = deadValues.end(); it != it2; ++it) {

    Instruction* I = dyn_cast<Instruction>(*it);
    if(!I)
      continue;

    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    // Dead calls might have side-effects. Most side-effect-causing instructions are never tested
    // for liveness, but (at the time of writing) open() calls are, since this informs whether
    // foldVFSCalls() can eliminate them.
    if(isa<CallInst>(I))
      continue;

    LPDEBUG("Delete instruction " << *(VI->second) << "\n");

    deleteInstruction(cast<Instruction>(VI->second));

  }

  for(DenseSet<Value*>::iterator it = unusedWriters.begin(), it2 = unusedWriters.end(); it != it2; ++it) {

    Instruction* I = cast<Instruction>(*it);
    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    // Skip deleting VFS calls for now.
    if(isa<CallInst>(I) && !isa<MemIntrinsic>(I))
      continue;

    LPDEBUG("Delete unused memop " << *(VI->second) << "\n");
    
    deleteInstruction(cast<Instruction>(VI->second));

  }

  // Replace instructions that are needed with their constant results:
  for(DenseMap<Value*, ValCtx>::iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {

    Instruction* I = dyn_cast<Instruction>(it->first);
    if(!I)
      continue;

    if(!isa<Constant>(it->second.first))
      continue;

    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    LPDEBUG("Original instruction " << *I << " -> " << *(VI->second) << "\n");
    LPDEBUG("Replace instruction " << *(VI->second) << " with " << *(it->second.first) << "\n");

    I = cast<Instruction>(VI->second);

    Value* oldMapping;
    if(isa<CallInst>(I))
      oldMapping = VM[I];

    I->replaceAllUsesWith(it->second.first);

    // Keep call instructions since they might have useful side-effects.
    if(!isa<CallInst>(I))
      I->eraseFromParent();
    else {
      // Restore mapping for future use by the inliner:
      VM[I] = oldMapping;
    }

  }

  foldVFSCalls();

  // Since we delete dead blocks here, we must ensure that improvedValues does not contain
  // any keys which refer to instructions that will be deleted. This is handled in 
  // the checkBlock function.
  replaceKnownBranches();
  deleteDeadBlocks();

}

Instruction* IntegrationAttempt::getCommittedValue(Value* V) {

  ValueMap<const Value*, Value*>::iterator it = CommittedValues.find(V);
  if(it == CommittedValues.end())
    return 0;
  else
    return cast<Instruction>(it->second);

}

void IntegrationAttempt::commitLocalPointers() {

  for(DenseMap<Value*, ValCtx>::iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {

    Instruction* I = dyn_cast<Instruction>(it->first);
    if(!I)
      continue;

    if(isa<Constant>(it->second.first))
      continue;

    if(!it->second.second->isAvailable())
      continue;

    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    LPDEBUG("Replace instruction " << *(VI->second) << " with " << *(it->second.first));

    Instruction* replaceWith = it->second.second->getCommittedValue(it->second.first);
    assert(replaceWith && "Couldn't get a replacement for a resolved pointer!");

    I = cast<Instruction>(VI->second);

    I->replaceAllUsesWith(replaceWith);
    I->eraseFromParent();

  }

}

namespace llvm {

  void dumpValueMap(LLVMContext* Ctx, bool verbose);

}

void llvm::dumpValueMap(LLVMContext* Ctx, bool verbose) {

  DenseMap<Value*, ValueHandleBase*>& Map = Ctx->pImpl->ValueHandles;
  errs() << "Map contains " << Map.size() << " entries\n";
  for(DenseMap<Value*, ValueHandleBase*>::iterator it = Map.begin(), it2 = Map.end(); it != it2; ++it) {

    if(!verbose) {
      errs() << it->first->getName() << "\n";
    }
    else {
      if(isa<BasicBlock>(it->first)) {
	errs() << "Block " << it->first->getName() << "\n";
      }
      else {
	errs() << "Value " << *(it->first) << "\n";
      }
    }

  }

  errs() << "End dump\n";

}
