

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/BasicBlock.h"
#include "llvm/Function.h"

#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

// TODO at some point: fold this stuff into the save procedure.

static BasicBlock* getUniqueSuccessor(BasicBlock* BB) {

  if(BB->getTerminator()->getNumSuccessors() != 1)
    return 0;

  return BB->getTerminator()->getSuccessor(0);

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

void IntegrationHeuristicsPass::postCommitOptimiseF(Function* F) {

  errs() << "Post-processing " << F->getName() << "\n";

  std::vector<std::vector<BasicBlock*> > Chains;

  DenseSet<BasicBlock*> Seen;

  for(Function::iterator it = F->begin(), itend = F->end(); it != itend; ++it) {

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

    bool isEntry = Chain[0] == &Chain[0]->getParent()->getEntryBlock();
    
    for(unsigned i = 1, ilim = Chain.size(); i != ilim; ++i)
      MergeBasicBlockIntoOnlyPred(Chain[i]);

    if(isEntry && Chain.back() != &Chain.back()->getParent()->getEntryBlock())
      Chain.back()->moveBefore(&Chain.back()->getParent()->getEntryBlock());

  }

}

void IntegrationHeuristicsPass::postCommitOptimise() {

  // Just one post-save optimisation at the moment: specialisation commonly produces
  // long chains of blocks with a single predecessor and a unique successor.
  // For each such chain, merge into a single large block.

  for(SmallVector<Function*, 4>::iterator it = commitFunctions.begin(),
	itend = commitFunctions.end(); it != itend; ++it) {

    postCommitOptimiseF(*it);

  }

}
