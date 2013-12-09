

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/BasicBlock.h"
#include "llvm/Function.h"

#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

using namespace llvm;

static cl::opt<bool> SkipPostCommit("int-skip-post-commit");

// TODO at some point: fold this stuff into the save procedure.

static BasicBlock* getUniqueSuccessor(BasicBlock* BB) {

  // We might run on blocks without a terminator when contexts are not yet committed.
  TerminatorInst* TI = BB->getTerminator();
  if(!TI)
    return 0;

  if(TI->getNumSuccessors() != 1)
    return 0;

  return TI->getSuccessor(0);

}

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

template<class T, class Callback> void postCommitOptimiseBlocks(T itstart, T itend, Callback& CB) {

  // Zap any instructions we've created that are trivially dead.
  // TODO: improve DIE to catch more cases like this before synthesis, or adopt
  // on-demand synthesis to similar effect.

  std::vector<Instruction*> Del;

  for(T it = itstart; it != itend; ++it) {

    BasicBlock* BB = it;
    for(BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II) {

      if(isInstructionTriviallyDead(II, GlobalTLI))
	Del.push_back(II);

    }

  }

  for(std::vector<Instruction*>::iterator Delit = Del.begin(), Delend = Del.end(); Delit != Delend; ++Delit)
    DeleteDeadInstruction(*Delit);

  Del.clear();

  // Now coalesce any long chains of BBs.

  std::vector<std::vector<BasicBlock*> > Chains;

  DenseSet<BasicBlock*> Seen;

  for(T it = itstart; it != itend; ++it) {

    BasicBlock* BB = it;
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
      MergeBasicBlockIntoOnlyPred(Chain.back());
    }

    CB.replaced(Start, Chain.back());

  }

}

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

void InlineAttempt::postCommitOptimise() {

  if(SkipPostCommit)
    return;

  if(CommitF) {
    
    PCOFunctionCB CB;
    postCommitOptimiseBlocks(CommitF->begin(), CommitF->end(), CB);

  }
  else {

    //    PCOBBsCB CB(this);
    //    postCommitOptimiseBlocks(DerefAdaptor(CommitBlocks.begin()), DerefAdaptor(CommitBlocks.end()), CB);

  }
   
}
