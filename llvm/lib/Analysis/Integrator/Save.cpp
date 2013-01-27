
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

void IntegrationAttempt::removeBlockFromLoops(BasicBlock* BB, const Loop* BBL) {

  const Loop* NextL = immediateChildLoop(getLoopContext(), BBL);

  if(PeelAttempt* PA = getPeelAttempt(NextL)) {

    PA->removeBlockFromLoops(BB, BBL);

  }

}

void PeelAttempt::removeBlockFromLoops(BasicBlock* BB, const Loop* BBL) {

  std::vector<BasicBlock*>::iterator removeit = std::find(LoopBlocks.begin(), LoopBlocks.end(), BB);
  release_assert(removeit != LoopBlocks.end());

  LoopBlocks.erase(removeit);

  if(BBL == L)
    return;

  for(std::vector<PeelIteration*>::iterator it = Iterations.begin(), it2 = Iterations.end(); it != it2; ++it) {

    (*it)->removeBlockFromLoops(BB, BBL);

  }

}

void IntegrationAttempt::replaceDeadValue(Value* V, ValCtx VC) {

  deadValues.erase(V);
  setReplacement(V, VC);

}

void InlineAttempt::localPrepareCommit() {

  IntegrationAttempt::localPrepareCommit();

}

void PeelIteration::localPrepareCommit() {

  // Remove loop header values, since these are removed by the loop unroller and are realised
  // by RAUW'ing the PHI node with one of its arguments rather than by directly replacing it.
    
  LHeader = L->getHeader();
  LLatch = L->getLoopLatch();

  BasicBlock* H = L->getHeader();
  for(BasicBlock::iterator it = H->begin(), it2 = H->end(); it != it2 && isa<PHINode>(it); ++it) {

    PHINode* V = cast<PHINode>(it);

    deadValues.erase(V);
    improvedValues.erase(V);

  }

  IntegrationAttempt::localPrepareCommit();

}

void IntegrationAttempt::localPrepareCommit() {

  // Remove any return instructions from consideration, since the inliner will take care of them for us
  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    TerminatorInst* TI = FI->getTerminator();
    if(isa<ReturnInst>(TI)) {

      deadValues.erase(TI);

    }

  }

  // Remove loop blocks which are invariant dead from the list of blocks belonging to that loop
  // This will stop the integration within that loop from considering it.

  for(DenseSet<BasicBlock*>::iterator BI = deadBlocks.begin(), BE = deadBlocks.end(); BI != BE; ++BI) {

    const Loop* BlockL = LI[&F]->getLoopFor(*BI);
    const Loop* MyL = getLoopContext();

    if(BlockL == MyL)
      continue;

    release_assert((!MyL) || MyL->contains(BlockL));

    removeBlockFromLoops(*BI, BlockL);

  }

  SmallVector<Value*, 4> toRemove;

  // Anywhere we would replace a value with a pointer that has been found dead, delete it instead.
  for(DenseMap<Value*, ValCtx>::iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {

    if(it->second.second) {

      if(it->second.second->valueWillBeDeleted(it->second.first)) {

	toRemove.push_back(it->first);

      }

    }

  }

  for(SmallVector<Value*, 4>::iterator it = toRemove.begin(), it2 = toRemove.end(); it != it2; ++it) {
    
    improvedValues.erase(*it);
    deadValues.insert(*it);

  }
  
}

void IntegrationAttempt::commitInContext(LoopInfo* MasterLI, ValueMap<const Value*, Value*>& valMap) {

  // First apply all local definitions and kills. Store the map from the Values we know to
  // Values as integrated into the program for the second phase when we resolve pointers,
  // and resolve constants / dead code now.

  errs() << "Commit phase 1: " << HeaderStr << "\n";

  this->MasterLI = MasterLI;
  CommittedValues.insert(valMap.begin(), valMap.end());

  // Step 1: perform local integration that doesn't use outside pointers.
  // This includes establishing any loop invariants, which will be caught up
  // in the loop peeling section below, as well as replacing users of calls
  // with the values they return, if we know them.

  commitLocalConstants(CommittedValues);

  // Delete dead blocks that fall lexically in inner loops, to avoid their getting duplicated
  // by the loop unroller.
  deleteDeadBlocks(true);

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

    if(!Called->isVarArg()) {

      // As we have already RAUW'd constants, a constant argument will be picked up by the inliner
      // if appropriate. Otherwise it will get caught up in the phase 2 pointer resolution.

      InlineFunctionInfo IFI(0, TD);

      // Get my loop context as it will be written:

      const Loop* MyL = getLoopContext();
      if(MyL) {

	MyL = MasterLI->getLoopFor(cast<BasicBlock>(CommittedValues[MyL->getHeader()]));

      }

      if(!InlineFunction(CI, IFI, &childMap, MasterLI, const_cast<Loop*>(MyL), LI[Called], this))
	assert(0 && "Inlining failed!\n");

      CommittedValues.erase(it->first);

      // childMap is now a map from the instructions' "real" names to those inlined.
      // Use it to commit changes known about that context:
      it->second->commitInContext(MasterLI, childMap);

    }
    else {

      // For varargs functions we must keep the original function.
      ValueMap<const Value*, Value*> NewFnMap;
      Function* Clone = CloneFunction(Called, NewFnMap, true);
      Clone->setLinkage(GlobalValue::InternalLinkage);
      Called->getParent()->getFunctionList().push_back(Clone);

      CI->setCalledFunction(Clone);

      DominatorTree* CloneDT = new DominatorTree();
      CloneDT->runOnFunction(*Clone);
      LoopInfo* CloneLI = new LoopInfo();
      CloneLI->runOnFunction(*Clone, CloneDT);      

      it->second->commitInContext(CloneLI, NewFnMap);

    }

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

    // No change?
    if((!completelyUnrollLoop) && unrollCount == 1)
      continue;

    // Take a copy of the block list before we clone them:
    std::vector<BasicBlock*> LBlocks = L->getBlocks();

    std::vector<ValueMap<const Value*, Value*>* > iterValues;

    if(!UnrollLoop(L, unrollCount, MasterLI, 0, !completelyUnrollLoop, completelyUnrollLoop, true /* Allow unusual exit branches*/, true /* Assume all iterations might exit */, &iterValues)) {

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
  
  // Delete blocks dead at our scope.
  // Do this last because the loop unroller will try to add edges towards them (and then, if they're
  // dead, commitLocalConstants->replaceKnownBranches will remove them again)
  deleteDeadBlocks(false);

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

void IntegrationAttempt::tryDeleteDeadBlock(BasicBlock* BB, bool innerScopesOnly) {

  if(!deadBlocks.count(BB))
    return;

  bool blockIsInvar = false;

  const Loop* BlockL = LI[&F]->getLoopFor(BB);
  if(BlockL != getLoopContext()) {

    // Blocks belonging to inner scopes must be removed before the loop unroller acts,
    // otherwise it'll duplicate them and the child contexts won't know to kill it again.
    blockIsInvar = true;

  }

  if(blockIsInvar != innerScopesOnly)
    return;

  ValueMap<const Value*, Value*>::iterator it = CommittedValues.find(BB);

  // Check if the BB was not cloned to begin with (indicating it's invariant dead)
  if(it == CommittedValues.end())
    return;

  // Get the copy of the block we should actually operate on:
  BB = cast<BasicBlock>(it->second);

  MasterLI->removeBlock(BB);
  
  // Remove all instructions in the block first:
  while(!(BB->begin() == BB->end())) {

    deleteInstruction(--BasicBlock::iterator(BB->end()));

  }

  BB->eraseFromParent();

}

bool InlineAttempt::getLoopBranchTarget(BasicBlock* FromBB, TerminatorInst* TI, TerminatorInst* ReplaceTI, BasicBlock*& Target) {
  return false;
}

bool PeelIteration::getLoopBranchTarget(BasicBlock* FromBB, TerminatorInst* TI, TerminatorInst* ReplaceTI, BasicBlock*& Target) {
  
  if(FromBB != LLatch)
    return false;
  
  if(iterStatus != IterationStatusFinal)
    return false;

  Target = 0;

  unsigned J = 0;
  for (unsigned I = 0; I != TI->getNumSuccessors(); ++I, ++J) {

    BasicBlock* thisTarget = TI->getSuccessor(I);
    if(thisTarget == LHeader) {
      // This target will have been deleted by the unroller.
      --J;
      continue;
    }
      
    if(!deadEdges.count(std::make_pair(FromBB, thisTarget))) {

      // Watch out -- switch blocks can have many outgoing edges aimed at the same target,
      // which is fine!
      BasicBlock* thisRealTarget = ReplaceTI->getSuccessor(J);
      if(Target && (Target != thisRealTarget)) {
	Target = 0;
	break;
      }
      else
	Target = thisRealTarget;

    }

  }

  return true;

}

void IntegrationAttempt::replaceKnownBranch(BasicBlock* FromBB, TerminatorInst* TI) {

  bool isDead = deadBlocks.count(FromBB);
  BasicBlock* Target = 0;
  
  const Loop* TIScope = 0;
  DenseMap<Instruction*, const Loop*>::iterator it = invariantInsts.find(TI);

  if(it != invariantInsts.end())
    TIScope = it->second;
  else {
    for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

      if(std::find(it->second->LoopBlocks.begin(), it->second->LoopBlocks.end(), FromBB) != it->second->LoopBlocks.end()) {
	TIScope = it->first;
	break;
      }
    }
    if(!TIScope)
      TIScope = getLoopContext();
  }

  if((!isDead) && TIScope != getLoopContext())
    return;

  // Return instructions have been replaced already by the inliner!
  if(isa<ReturnInst>(TI))
    return;

  TerminatorInst* ReplaceTI = cast<BasicBlock>(CommittedValues[FromBB])->getTerminator();
  if(isa<UnreachableInst>(ReplaceTI)) {

    // The loop unroller has already handled this branch!
    return;

  }

  if(!isDead) {

    // Careful: using ReplaceTI not TI because TI probably still belongs to a version of the blocks
    // which is still rolled (e.g. loop 1 contains loop 2; loop 1 was unrolled to two iterations
    // creating 2.1 and 2.2; we're now unrolling 2.2 but the original blocks reside in 2.1 and are
    // rolled) I think all branches that aren't the loop latch will look the same as the rolled version.
    const unsigned NumSucc = ReplaceTI->getNumSuccessors();

    if(NumSucc <= 1)
      return;

    // For loop latches this is a bit complicated: at this point their exit branches pointing at the
    // loop header have been appropriately redirected, or removed if this is the final iteration.
    // The redirected case is fine, as ReplaceTI->getSuccessor(...) picks it up. If it's been removed,
    // we need the following special case:

    if(!getLoopBranchTarget(FromBB, TI, ReplaceTI, Target)) {

      for (unsigned I = 0; I != NumSucc; ++I) {

	// Back to using the original blocks here since our results are calculated in their terms
	BasicBlock* thisTarget = TI->getSuccessor(I);
	if(!deadEdges.count(std::make_pair(FromBB, thisTarget))) {

	  // Watch out -- switch blocks can have many outgoing edges aimed at the same target,
	  // which is fine!
	  BasicBlock* thisRealTarget = ReplaceTI->getSuccessor(I);
	  if(Target && (Target != thisRealTarget))
	    return;
	  else
	    Target = thisRealTarget;

	}

      }

    }

    if(!Target)
      return;

  }

  if(!isDead)
    LPDEBUG("Replace terminator " << *ReplaceTI << " with branch to " << Target->getName() << "\n");
  else
    LPDEBUG("Replace terminator " << *ReplaceTI << " with unreachable\n");

  BasicBlock* ReplaceSource = ReplaceTI->getParent();

  std::vector<BasicBlock*> Succs;
  Succs.reserve(ReplaceTI->getNumSuccessors());
	       
  for(unsigned i = 0; i < ReplaceTI->getNumSuccessors(); ++i) {
    
    Succs.push_back(ReplaceTI->getSuccessor(i));

  }

  std::sort(Succs.begin(), Succs.end());
  std::vector<BasicBlock*>::iterator SuccEnd = std::unique(Succs.begin(), Succs.end());

  // Gah... BBs with multiple edges from a single block seem sometimes to have multiple
  // PHI entries for that block, sometimes just one. Unique the successors first, then remove
  // ourselves from their PHIs until we can't anymore.
  
  for(std::vector<BasicBlock*>::iterator SuccIt = Succs.begin(); SuccIt != SuccEnd; ++SuccIt) {

    BasicBlock* Succ = *SuccIt;
    if(Succ != Target) {

      for(BasicBlock::iterator BI = Succ->begin(), BE = Succ->end(); BI != BE && isa<PHINode>(BI); ++BI) {

	int idx;
	PHINode* PN = cast<PHINode>(BI);
	while((idx = PN->getBasicBlockIndex(ReplaceTI->getParent())) != -1) {

	  PN->removeIncomingValue(idx, false);

	}

      }

    }

  }

  CommittedValues.erase(TI);
  ReplaceTI->eraseFromParent();

  if(Target)
    BranchInst::Create(Target, ReplaceSource);
  else
    new UnreachableInst(ReplaceSource->getParent()->getContext(), ReplaceSource);

}

void InlineAttempt::replaceKnownBranches() {

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    replaceKnownBranch(FI, FI->getTerminator());

  }

}

void PeelIteration::replaceKnownBranches() {

  for(std::vector<BasicBlock*>::iterator it = parentPA->LoopBlocks.begin(), it2 = parentPA->LoopBlocks.end(); it != it2; ++it) {

    replaceKnownBranch(*it, (*it)->getTerminator());

  }

}

void InlineAttempt::deleteDeadBlocks(bool innerScopesOnly) {

  // Avoid iterator invalidation
  std::vector<BasicBlock*> FBlocks(F.size());
  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI)
    FBlocks.push_back(FI);

  for(std::vector<BasicBlock*>::iterator FI = FBlocks.begin(), FE = FBlocks.end(); FI != FE; ++FI) {

    tryDeleteDeadBlock(*FI, innerScopesOnly);

  }

}

void PeelIteration::deleteDeadBlocks(bool innerScopesOnly) {

  for(std::vector<BasicBlock*>::iterator it = parentPA->LoopBlocks.begin(), it2 = parentPA->LoopBlocks.end(); it != it2; ++it) {

    tryDeleteDeadBlock(*it, innerScopesOnly);

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

    // Insert a seek call if that turns out to be necessary (i.e. if that FD may be subsequently
    // used without an intervening SEEK_SET)
    // No need for isAvailableFromCtx here and several more times in the VFS resolution
    // code because we just want to know if the next user will be folded, we don't need to
    // actually forward values there.
    if(it->second.needsSeek) {

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

    if(it->second.MayDelete) {
      cast<Instruction>(CommittedValues[it->first])->eraseFromParent();
    }

  }

  for(DenseMap<CallInst*, OpenStatus*>::iterator it = forwardableOpenCalls.begin(), it2 = forwardableOpenCalls.end(); it != it2; ++it) {
    
    if(!it->second->success) {
      // It's ok to delete the open in this case, as it will be replaced by -1.
      deleteInstruction(cast<Instruction>(CommittedValues[it->first]));
    }
    else {

      // Can't delete open if it has direct users still!
      // This could be done much better if we could retain the original open for later reference.
      // Do this soon by cloning everything before manipulating it, meaning pointers to values will
      // remain live throughout the commit process.
      if(!deadValues.count(it->first))
	continue;

      if(it->second->MayDelete)
	deleteInstruction(cast<Instruction>(CommittedValues[it->first]));

    }

  }

  for(DenseMap<CallInst*, CloseFile>::iterator it = resolvedCloseCalls.begin(), it2 = resolvedCloseCalls.end(); it != it2; ++it) {

    if(it->second.MayDelete && it->second.openArg->MayDelete) {
      if(it->second.openVC.second->inDeadValues(it->second.openVC.first))
	deleteInstruction(cast<Instruction>(CommittedValues[it->first]));
    }
    
  }

}

void IntegrationAttempt::commitLocalConstants(ValueMap<const Value*, Value*>& VM) {

  // Commit anything that's simple: commit simple constants, known jump targets.

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

    if(it->second.isPtrAsInt())
      continue;

    if(it->second.isVaArg())
      continue;

    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    LPDEBUG("Original instruction " << *I << " -> " << *(VI->second) << "\n");
    LPDEBUG("Replace instruction " << *(VI->second) << " with " << *(it->second.first) << "\n");

    I = cast<Instruction>(VI->second);

    Value* oldMapping = 0;
    if(isa<CallInst>(I))
      oldMapping = VM[I];

    Constant* TargetC = cast<Constant>(it->second.first);
    if(I->getType() != it->second.first->getType()) {
      assert(isa<CallInst>(I) && "Non-call instruction replaced with wrong type?");
      if(I->getType()->isVoidTy()) {
	TargetC = 0;
      }
      else if(I->getType()->isIntegerTy()) {
	TargetC = ConstantExpr::getIntegerCast(TargetC, I->getType(), false);
      }
      else if(I->getType()->isPointerTy()) {
	TargetC = ConstantExpr::getPointerCast(TargetC, I->getType());
      }
      else if(I->getType()->isFloatingPointTy()) {
	TargetC = ConstantExpr::getFPCast(TargetC, I->getType());
      }
      else {
	assert(0 && "Type mismatch not handled");
      }
    }

    if(TargetC)
      I->replaceAllUsesWith(TargetC);

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

}

Instruction* IntegrationAttempt::getCommittedValue(Value* V) {

  ValueMap<const Value*, Value*>::iterator it = CommittedValues.find(V);
  if(it == CommittedValues.end())
    return 0;
  else
    return cast<Instruction>(it->second);

}

void IntegrationAttempt::commitLocalPointers() {

  errs() << "Commit phase 2: " << HeaderStr <<  "\n";

  for(DenseMap<Value*, ValCtx>::iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {

    Instruction* I = dyn_cast<Instruction>(it->first);
    if(!I)
      continue;

    if(isa<Constant>(it->second.first))
      continue;

    if(!it->second.second->isAvailableFromCtx(this))
      continue;

    if(it->second.isPtrAsInt())
      continue;

    if(it->second.isVaArg())
      continue;

    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    LPDEBUG("Replace instruction " << *(VI->second) << " with " << *(it->second.first));

    Instruction* replaceWith = it->second.second->getCommittedValue(it->second.first);
    if(!replaceWith)
      continue;
    // This is occasionally legitimate: noalias results and parameters are id'd objects.
    //assert(replaceWith && "Couldn't get a replacement for a resolved pointer!");

    I = cast<Instruction>(VI->second);

    if(I->getType() != replaceWith->getType()) {

      assert(I->getType()->isPointerTy() && replaceWith->getType()->isPointerTy());
      replaceWith = new BitCastInst(replaceWith, I->getType(), "speccast", I);

    }

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
