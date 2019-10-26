//===- PostCommit.cpp -----------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"

#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<bool> SkipPostCommit("int-skip-post-commit");

// These optimisations fold a committed residual-code function into a neater form.
// We do this as we go because in certain cases it can dramatically reduce the amount
// of useless code emitted and thus improve the size of program we can deal with.

// TODO at some point: fold this stuff into the save procedure.

static BasicBlock* getUniqueSuccessor(BasicBlock* BB) {

  // We might run on blocks without a terminator when contexts are not yet committed.
  Instruction* TI = BB->getTerminator();
  if(!TI)
    return 0;

  if(TI->getNumSuccessors() != 1)
    return 0;

  return TI->getSuccessor(0);

}

// Walk a chain of basic blocks with only one predecessor or successor.
static BasicBlock* getChainPrev(BasicBlock* BB) {

  BasicBlock* pred = BB->getSinglePredecessor();
  if((!pred) || pred == BB)
    return 0;

  if(getUniqueSuccessor(pred) != BB)
    return 0;

  return pred;

}

static BasicBlock* getChainNext(BasicBlock* BB) {

  BasicBlock* next = getUniqueSuccessor(BB);
  if((!next) || next == BB)
    return 0;

  if(next->getSinglePredecessor() != BB)
    return 0;

  return next;

}

template<class T, class Callback> void postCommitOptimiseBlocks(T itstart, T itend, Callback& CB, Function::iterator& firstFailedBlock) {

  // Zap any instructions we've created that are trivially dead.
  // TODO: improve DIE to catch more cases like this before synthesis, or adopt
  // on-demand synthesis to similar effect.

  std::vector<Instruction*> Del;

  for(T it = itstart; it != itend; ++it) {

    BasicBlock* BB = &*it;
    for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II) {

      if(isInstructionTriviallyDead(&*II, GlobalTLI))
	Del.push_back(&*II);

    }

  }

  for(std::vector<Instruction*>::iterator Delit = Del.begin(), Delend = Del.end(); Delit != Delend; ++Delit)
    DeleteDeadInstruction(*Delit);

  Del.clear();

  // Now coalesce any long chains of BBs.

  std::vector<std::vector<BasicBlock*> > Chains;

  DenseSet<BasicBlock*> Seen;

  for(T it = itstart; it != itend; ++it) {

    BasicBlock* BB = &*it;
    if(!Seen.insert(BB).second)
      continue;

    // Find chain start:
    while(BasicBlock* PrevBB = getChainPrev(BB))
      BB = PrevBB;

    Seen.insert(BB);

    Chains.resize(Chains.size() + 1);
    std::vector<BasicBlock*>& Chain = Chains.back();
    Chain.push_back(BB);

    while(BasicBlock* NextBB = getChainNext(BB)) {
      Chain.push_back(NextBB);
      Seen.insert(NextBB);
      BB = NextBB;
    }

    if(Chain.size() == 1)
      Chains.pop_back();
    else {

      /*
      errs() << "Chain: ";

      for(std::vector<BasicBlock*>::iterator it = Chain.begin(), 
	    itend = Chain.end(); it != itend; ++it) {

	if(it != Chain.begin())
	  errs() << ", ";
	
	errs() << (*it)->getName();

      }
      
      errs() << "\n";
      */

    }

  }

  // Merge each chain found

  for(std::vector<std::vector<BasicBlock*> >::iterator chainit = Chains.begin(),
	itend = Chains.end(); chainit != itend; ++chainit) {

    std::vector<BasicBlock*>& Chain = *chainit;

    BasicBlock* Start = Chain[0];
    CB.willReplace(Start);

    for(unsigned i = 1, ilim = Chain.size(); i != ilim; ++i) {

      if(i != 0 && (i % 10000 == 0)) 
	errs() << ".";

      BasicBlock* PBB = Chain.back()->getSinglePredecessor();

      // First failed block goes away; next one takes its place.
      if(Function::iterator(PBB) == firstFailedBlock)
	++firstFailedBlock;

      MergeBasicBlockIntoOnlyPred(Chain.back());

    }

    CB.replaced(Start, Chain.back());

  }

}

// Helpers that keep either a committed function or basic block list that hasn't
// yet been inserted into a function having the right entry block.

struct PCOFunctionCB {

  bool isEntryBlock;

  void willReplace(BasicBlock* Old) {

    isEntryBlock = Old == &Old->getParent()->getEntryBlock();

  }

  void replaced(BasicBlock* Old, BasicBlock* New) {

    if(isEntryBlock && New != &New->getParent()->getEntryBlock())
      New->moveBefore(&New->getParent()->getEntryBlock());

  }

};

struct PCOBBsCB {

  InlineAttempt* IA;
  bool isEntryBlock;

  PCOBBsCB(InlineAttempt* _IA) : IA(_IA) {} 

  void willReplace(BasicBlock* Old) {

    isEntryBlock = Old == IA->entryBlock;

  }

  void replaced(BasicBlock* Old, BasicBlock* New) {

    if(isEntryBlock)
      IA->entryBlock = New;

  }

};

struct DerefAdaptor {

  std::vector<BasicBlock*>::iterator inner;
  
  DerefAdaptor(std::vector<BasicBlock*>::iterator _inner) : inner(_inner) {}
  DerefAdaptor(const DerefAdaptor& Other) : inner(Other.inner) {}

  DerefAdaptor& operator++() {
    ++inner;
    return *this;
  }

  bool operator==(const DerefAdaptor& Other) { return inner == Other.inner; }
  bool operator!=(const DerefAdaptor& Other) { return inner != Other.inner; }

  operator BasicBlock*() {
    return *inner;
  }

};

// Main post-commit optimisation entry point. I'm not totally certain, but I think optimising a basic-block list that
// hasn't been inserted into a residual function yet has been disabled because some LLVM core functions fail if
// BB->getParent() is null. Such blocks will be treated once they've been assigned a final function; trying to do them
// ahead of time was just to limit transient memory consumption anyhow.

void InlineAttempt::postCommitOptimise() {

  if(SkipPostCommit)
    return;

  if(CommitF) {
    
    PCOFunctionCB CB;
    postCommitOptimiseBlocks(CommitF->begin(), CommitF->end(), CB, firstFailedBlock);

    // Now top-sort the blocks, excluding the failed blocks by annotating them 'visited' to start with.
    {

      SmallSet<BasicBlock*, 8> Visited;
      for(Function::iterator it = firstFailedBlock, itend = CommitF->end(); it != itend; ++it)
	Visited.insert(&*it);

      BasicBlock* firstBlock = &CommitF->getEntryBlock();
      std::vector<BasicBlock*> Ordered;
      createTopOrderingFrom(firstBlock, Ordered, Visited, 0, 0);
      std::reverse(Ordered.begin(), Ordered.end());

      Function::BasicBlockListType& BBL = CommitF->getBasicBlockList();

      Function::iterator fit = CommitF->begin();
      for(std::vector<BasicBlock*>::iterator it = Ordered.begin(), itend = Ordered.end(); it != itend; ++it) {

	// Splice this block before fit, fit moves forwards and continue,
	// or else fit is already in the right place, leave it and insert before its successor.

	if(fit == CommitF->end() || (&*fit) != (*it))
	  BBL.splice(fit, BBL, *it);
	else
	  ++fit;

      }

    }

  }
  else {

    //    PCOBBsCB CB(this);
    //    postCommitOptimiseBlocks(DerefAdaptor(CommitBlocks.begin()), DerefAdaptor(CommitBlocks.end()), CB);

  }
   
}
