
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Support/Debug.h"

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

  commitInContext(LI[&F], rootValMap);

}

void IntegrationAttempt::commitInContext(LoopInfo* MasterLI, ValueMap<const Value*, Value*>& valMap) {

  // First apply all local definitions and kills. Store the map from the Values we know to
  // Values as integrated into the program for the second phase when we resolve pointers,
  // and resolve constants / dead code now.

  CommittedValues.insert(valMap.begin(), valMap.end());

  // Step 1: perform local integration that doesn't use outside pointers.
  // This includes establishing any loop invariants, which will be caught up
  // in the loop peeling section below, as well as replacing users of calls
  // with the values they return, if we know them.

  commitLocalConstants();

  // Step 2: inline each child call

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    if(ignoreIAs.count(it->first))
      continue;

    // Find the call instruction we're actually inlining:

    CallInst* CI = cast<CallInst>(valMap[it->first]);

    ValueMap<const Value*, Value*> childMap;
    // This both inputs argument values and returns a map from instructions
    // as we know them to instructions in the inlined function body.

    Function* Called = it->first->getCalledFunction();
    assert(Called && "Indirect call inlined?!");

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

    Loop* L = MasterLI->getLoopFor(cast<BasicBlock>(valMap[it->first->getHeader()]));

    bool completelyUnrollLoop = it->second->Iterations.back()->iterStatus == IterationStatusFinal;
    unsigned unrollCount = it->second->Iterations.size();

    // Take a copy of the block list before we clone them:
    std::vector<BasicBlock*> LBlocks = L->getBlocks();

    std::vector<ValueMap<const Value*, Value*> > iterValues;

    if(!UnrollLoop(L, unrollCount, LI[&F], 0, true, completelyUnrollLoop, &iterValues)) {

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
      
      if(i == 0) {
	childValues = &valMap;
      }
      else {

	ValueMap<const Value*, Value*>& thisIterValues = iterValues[i-1];

	DenseSet<Value*> loopValues;
	ValueMap<const Value*, Value*> composedValues;
	childValues = &composedValues;

	for(std::vector<BasicBlock*>::iterator BI = LBlocks.begin(), BE = LBlocks.end(); BI != BE; ++BI) {

	  for(BasicBlock::iterator II = (*BI)->begin(), IE = (*BI)->end(); II != IE; ++II) {

	    loopValues.insert(II);

	  }

	}

	// Now write the value side of the composed map:

	for(ValueMap<const Value*, Value*>::iterator VI = valMap.begin(), VE = valMap.end(); VI != VE; ++VI) {

	  if(loopValues.count(VI->second)) {

	    composedValues[VI->first] = thisIterValues[VI->second];

	  }

	}
	
      }

      // Commit constant results to this iteration:

      it->second->Iterations[i]->commitInContext(MasterLI, *childValues);

    }

  }

}

void IntegrationAttempt::commitPointers() {

  commitLocalPointers();

  for(DenseMap<CallInst*, InlineAttempt*>::iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {

    it->second->commitPointers();

  }

  for(DenseMap<const Loop*, PeelAttempt*>::iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {

    unsigned iterCount = it->second->Iterations.size();
    unsigned iterLimit = (it->second->Iterations.back()->iterStatus == IterationStatusFinal) ? iterCount : iterCount - 1;

    for(unsigned i = 0; i < iterLimit; ++i) {

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
  
  // Remove all instructions in the block first:
  while(!isa<TerminatorInst>(BB->begin())) {

    deleteInstruction(--BasicBlock::iterator(BB->getTerminator()));

  }

  TerminatorInst* TI = BB->getTerminator();

  for(unsigned i = 0; i < TI->getNumSuccessors(); ++i) {
    
    BasicBlock* Succ = TI->getSuccessor(i);
    Succ->removePredecessor(BB);

  }

  deleteInstruction(TI);

  // Branches aimed at this block will necessarily get simplified.
  BB->eraseFromParent();

}

void InlineAttempt::deleteDeadBlocks() {

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    tryDeleteDeadBlock(FI);

  }

}

void PeelIteration::deleteDeadBlocks() {

  for(std::vector<BasicBlock*>::iterator it = parentPA->LoopBlocks.begin(), it2 = parentPA->LoopBlocks.end(); it != it2; ++it) {

    tryDeleteDeadBlock(*it);

  }  

}

void IntegrationAttempt::commitLocalConstants() {

  // Commit anything that's simple: commit simple constants, dead blocks and edges.

  // Delete instructions that are certainly no longer needed:
  for(DenseSet<Value*>::iterator it = deadValues.begin(), it2 = deadValues.end(); it != it2; ++it) {

    Instruction* I = dyn_cast<Instruction>(*it);
    if(!I)
      continue;

    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    LPDEBUG("Delete instruction " << *(VI->second) << "\n");

    deleteInstruction(cast<Instruction>(VI->second));

  }

  // Replace instructions that are needed with their constant results:
  for(DenseMap<Value*, ValCtx>::iterator it = improvedValues.begin(), it2 = improvedValues.end(); it != it2; ++it) {

    if(deadValues.count(it->first))
      continue;

    Instruction* I = dyn_cast<Instruction>(it->first);
    if(!I)
      continue;

    if(!isa<Constant>(it->second.first))
      continue;

    ValueMap<const Value*, Value*>::iterator VI = CommittedValues.find(I);
    if(VI == CommittedValues.end())
      continue;

    LPDEBUG("Replace instruction " << *(VI->second) << " with " << *(it->second.first));

    I = cast<Instruction>(VI->second);

    I->replaceAllUsesWith(it->second.first);
    I->eraseFromParent();

  }

  // Since we delete dead blocks here, we must ensure that improvedValues does not contain
  // any keys which refer to instructions that will be deleted. This is handled in 
  // the checkBlock function.
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

    if(deadValues.count(it->first))
      continue;

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

    LPDEBUG("Replace instruction " << *(VI->second) << " with " << it->second);

    Instruction* replaceWith = it->second.second->getCommittedValue(it->second.first);
    assert(replaceWith && "Couldn't get a replacement for a resolved pointer!");

    I = cast<Instruction>(VI->second);

    I->replaceAllUsesWith(replaceWith);
    I->eraseFromParent();

  }

}
