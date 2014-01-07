
#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/CommandLine.h"

#include <vector>

using namespace llvm;

static cl::list<std::string> ProcessFunctionsCL("fnl-function", cl::ZeroOrMore);
static DenseSet<Function*> ProcessFunctions;

namespace {

  class ForceNaturalLoopFormPass : public FunctionPass {

  public:

    DominatorTree* DT;
    LoopInfo* LI;
    Function* F;

    static char ID; // Pass identification
    ForceNaturalLoopFormPass() : FunctionPass(ID) {}
    bool runOnFunction(Function &F);

    bool forceOneBackedge();
    bool makeDominateFrom(BasicBlock* Header, BasicBlock* Target);
    bool makeDominate(BasicBlock* Header, BasicBlock* Target);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<DominatorTree>();
      AU.addRequired<LoopInfo>();
    }
  };
  char ForceNaturalLoopFormPass::ID = 0;

} // end anonymous namespace.

static RegisterPass<ForceNaturalLoopFormPass> X("force-loops", "Force natural loop form",
						false /* Only looks at CFG */,
						false /* Analysis Pass */);

namespace llvm {

  FunctionPass* createForceNaturalLoopFormPass() {
    return new ForceNaturalLoopFormPass();
  }
  
  // Borrowed from IHP for a quick prototype.
  void createTopOrderingFrom(BasicBlock* BB, std::vector<BasicBlock*>& Result, SmallSet<BasicBlock*, 8>& Visited, LoopInfo* LI, const Loop* MyL);

}

#define release_assert(x) do { if(!(x)) { errs() << "Release-assertion failed: " #x "\n"; abort(); } } while(0);

static void gatherPreds(BasicBlock* BB, DenseSet<BasicBlock*>& Preds) {

  if(!Preds.insert(BB).second)
    return;

  for(pred_iterator PI = pred_begin(BB), PE = pred_end(BB); PI != PE; ++PI)
    gatherPreds(*PI, Preds);

}

bool ForceNaturalLoopFormPass::makeDominateFrom(BasicBlock* Header, BasicBlock* SBB) {

  // Firstly, introduce a simplifying assumption: whenever a predecessor can already reach both
  // this block (SBB) and the Header, reroute those branches which point here via a temporary.
  // Thus the source block will be enough to disambiguate ways of entering the loop.

  {

    SmallVector<BasicBlock*, 4> RerouteBBs;

    for(pred_iterator PI = pred_begin(SBB), PE = pred_end(SBB); PI != PE; ++PI) {
	  
      BasicBlock* PBB = *PI;

      if(DT->dominates(Header, PBB))
	continue;
      
      if(std::count(succ_begin(PBB), succ_end(PBB), Header))
	RerouteBBs.push_back(PBB);

    }

    for(SmallVector<BasicBlock*, 4>::iterator it = RerouteBBs.begin(), itend = RerouteBBs.end();
	it != itend; ++it) {

      BasicBlock* PBB = *it;
      BasicBlock* Temp = BasicBlock::Create(SBB->getContext(), "nlf.route", SBB->getParent(), SBB);
      BranchInst::Create(SBB, Temp);

      errs() << "Rerouting branches from " << PBB->getName() << " to " << SBB->getName() << " via a temporary because it also branches to the header\n";

      // Direct PBB -> SBB branches via Temp
      TerminatorInst* Term = PBB->getTerminator();
      for(uint32_t i = 0, ilim = Term->getNumSuccessors(); i != ilim; ++i) {

	if(Term->getSuccessor(i) == SBB)
	  Term->setSuccessor(i, Temp);

      }

      // Draw PBB -> SBB PHIs from Temp instead
      for(BasicBlock::iterator BI = SBB->begin(), BE = SBB->end(); BI != BE && isa<PHINode>(BI); ++BI) {
	    
	PHINode* PN = cast<PHINode>(BI);
	int BBIndex = PN->getBasicBlockIndex(PBB);
	release_assert(BBIndex != -1);
	PN->setIncomingBlock(BBIndex, Temp);

      }

    }

    // Return to recalculate dominators. TODO: learn how to fix up the DT from here.
    if(RerouteBBs.size())
      return true;

  }

  // Find those preds which are not already dominated by Header, and which will be rerouted.

  SmallPtrSet<BasicBlock*, 4> nonLoopPreds;

  for(pred_iterator PI = pred_begin(SBB), PE = pred_end(SBB); PI != PE; ++PI) {

    if(!DT->dominates(Header, *PI)) {

      // Walk the list out of line, since we'll break iterators by adjusting branch targets
      nonLoopPreds.insert(*PI);

    }

  }

  if(nonLoopPreds.empty())
    return false;

  // Amend Header's branch structure: if this is the first time this header has been so amended
  // it will end with an unconditional branch; replace that with a switch on a PHI that indicates
  // the incoming path taken.

  IntegerType* I32 = Type::getInt32Ty(Header->getContext());
      
  TerminatorInst* HeaderTI = Header->getTerminator();
  if(BranchInst* HeaderBI = dyn_cast<BranchInst>(HeaderTI)) {

    release_assert(!HeaderBI->isConditional());

    BasicBlock* OldHeader = HeaderBI->getSuccessor(0);

    PHINode* PredPN = PHINode::Create(I32, 0, "nlf.predidx", Header->begin());
    HeaderBI->eraseFromParent();
    SwitchInst::Create(PredPN, OldHeader, 0, Header);

    Constant* OldHeaderID = Constant::getNullValue(I32);

    for(pred_iterator PI = pred_begin(Header), PE = pred_end(Header); PI != PE; ++PI)
      PredPN->addIncoming(OldHeaderID, *PI);

  }

  PHINode* HeaderDestPHI = cast<PHINode>(Header->begin());
  release_assert(HeaderDestPHI->getName() == "nlf.predidx");
  SwitchInst* HeaderSwitch = cast<SwitchInst>(Header->getTerminator());

  // Allocate a new number representing blocks that should target SBB:
  ConstantInt* SBBID = ConstantInt::get(I32, HeaderSwitch->getNumSuccessors());

  uint32_t NewPHISize = std::distance(pred_begin(Header), pred_end(Header));

  for(SmallPtrSet<BasicBlock*, 4>::iterator PI = nonLoopPreds.begin(), PE = nonLoopPreds.end(); PI != PE; ++PI) {

    // Adjust branch targets:
    TerminatorInst* TI = (*PI)->getTerminator();
    for(uint32_t i = 0, ilim = TI->getNumSuccessors(); i != ilim; ++i) {

      if(TI->getSuccessor(i) == SBB)
	TI->setSuccessor(i, Header);

    }

    for(BasicBlock::iterator BI = Header->begin(), 
	  BE = Header->end(); BI != BE && isa<PHINode>(BI); ++BI) {

      // If this is the first PHI, it should be the predecessor index PHI.
      // Add our number.
      // Other header PHIs are undef coming from this new edge.
	    
      PHINode* PN = cast<PHINode>(BI);
      if(BI != Header->begin()) {
	Value* UD = UndefValue::get(PN->getType());
	PN->addIncoming(UD, *PI);
      }
      else {
	release_assert(PN == HeaderDestPHI);
	HeaderDestPHI->addIncoming(SBBID, *PI);
      }

    }

  }

  NewPHISize += nonLoopPreds.size();

  // PHIs: for each PHI node in SBB, create a corresponding node in Header that is undef for
  // other preds, and uses the same values as the existing PHIs for the other preds.

  for(BasicBlock::iterator BI = SBB->begin(), BE = SBB->end(); BI != BE && isa<PHINode>(BI); ++BI) {

    PHINode* OldPN = cast<PHINode>(BI);
    PHINode* NewPN = PHINode::Create(OldPN->getType(), NewPHISize, "nlf.fwd", Header->getFirstNonPHI());

    // Copy incoming values for edges just redirected:
    for(uint32_t i = 0, ilim = OldPN->getNumIncomingValues(); i != ilim; ++i) {
      if(nonLoopPreds.count(OldPN->getIncomingBlock(i)))
	NewPN->addIncoming(OldPN->getIncomingValue(i), OldPN->getIncomingBlock(i));
    }

    Value* UD = UndefValue::get(OldPN->getType());

    // Take undef for existing edges
    for(pred_iterator PI2 = pred_begin(Header), PE2 = pred_end(Header); PI2 != PE2; ++PI2) {

      if(!nonLoopPreds.count(*PI2))
	NewPN->addIncoming(UD, *PI2);

    }

    // Remove redirected edges from OldPN:
    for(uint32_t i = OldPN->getNumIncomingValues(); i > 0; --i) {

      uint32_t idx = i - 1;
      if(nonLoopPreds.count(OldPN->getIncomingBlock(idx)))
	OldPN->removeIncomingValue(idx, /* remove if empty = */ false);

    }

    // Replace with NewPN:
    OldPN->addIncoming(NewPN, Header);

  }

  // Add a switch case: when entered with nlf.predidx == SBBID, branch to SBB.
  HeaderSwitch->addCase(SBBID, SBB);



  return true;

}

bool ForceNaturalLoopFormPass::makeDominate(BasicBlock* Header, BasicBlock* Target) {

  bool ret;

  if((ret = makeDominateFrom(Header, Target))) {
    
    // Check that this step didn't break the function:
    verifyFunction(*F, AbortProcessAction);
    
    // Something changed; recalculate analyses!
    DT->getBase().recalculate(*F);
    LI->releaseMemory();
    LI->runOnFunction(*F);    

  }

  return ret;

}

static bool alreadyMangled(BasicBlock* BB) {

  if(!isa<SwitchInst>(BB->getTerminator()))
    return false;
  if(!isa<PHINode>(BB->begin()))
    return false;
  if(BB->begin()->getName() != "nlf.predidx")
    return false;

  return true;

}

bool ForceNaturalLoopFormPass::forceOneBackedge() {

  BasicBlock* Entry = &F->getEntryBlock();
  
  std::vector<BasicBlock*> TopOrder;

  {
    SmallSet<BasicBlock*, 8> Visited;
    createTopOrderingFrom(Entry, TopOrder, Visited, LI, /* initial loop = */ 0);
  }

  DenseMap<BasicBlock*, uint32_t> ReverseTopOrder;
  uint32_t i = 0;
  for(std::vector<BasicBlock*>::iterator it = TopOrder.begin(), itend = TopOrder.end(); it != itend; ++it, ++i)
    ReverseTopOrder[*it] = i;

  for(Function::iterator it = F->begin(), itend = F->end(); it != itend; ++it) {

    for(succ_iterator SI = succ_begin(it), SE = succ_end(it); SI != SE; ++SI) {

      if(ReverseTopOrder[*SI] > ReverseTopOrder[it]) {

	// The edge it -> *SI should be a loop backedge. Make it so.
	BasicBlock* Header = *SI;
	BasicBlock* BE = it;

	if(!DT->dominates(Header, BE)) {

	  if(!alreadyMangled(Header))
	    SplitBlock(Header, Header->begin(), this);

	  errs() << F->getName() << ": Forcing " << BE->getName() << " -> " << Header->getName() << " to become a backedge\n";
	  while(makeDominate(Header, BE)) {  }
	  return true;

	}
	
      }

    }

  }

  return false;

}

bool ForceNaturalLoopFormPass::runOnFunction(Function& F) {

  bool Changed = false;
  DT = &getAnalysis<DominatorTree>();
  LI = &getAnalysis<LoopInfo>();
  this->F = &F;

  if((!ProcessFunctionsCL.empty()) && ProcessFunctions.empty()) {

    for(cl::list<std::string>::iterator it = ProcessFunctionsCL.begin(), itend = ProcessFunctionsCL.end();
	it != itend; ++it) {

      Function* ThisF = F.getParent()->getFunction(*it);
      if(!ThisF) {

	errs() << "No such function: " << *it << "\n";
	exit(1);

      }

      ProcessFunctions.insert(ThisF);

    }

  }

  if(ProcessFunctions.size() && !ProcessFunctions.count(&F))
    return false;

  // Find an improvement candidate: look for a cycle that is not already a natural
  // loop using post-order numbering.

  while(forceOneBackedge())
    Changed = true;

  return Changed;

}
