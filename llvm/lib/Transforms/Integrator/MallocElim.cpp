// A pass that uses the GlobalOpt is-used analysis to eliminate malloc calls that are not used.
// These commonly end up hanging around after a round of integration.

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/IPO/GlobalOpt.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Pass.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

namespace {

  class MallocElimPass : public FunctionPass {

  public:
    static char ID; // Pass identification
    MallocElimPass() : FunctionPass(ID) {}
    bool runOnFunction(Function &F);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    }
  };
  char MallocElimPass::ID = 0;

} // end anonymous namespace.

INITIALIZE_PASS(MallocElimPass, "malloc-elim",
                "Remove unused malloc calls", false, false);

FunctionPass *llvm::createMallocElimPass() {
  return new MallocElimPass();
}

bool MallocElimPass::runOnFunction(Function& F) {

  bool Changed = false;

  for(Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI) {

    SmallVector<CallInst*, 4> eraseCIs;

    for(BasicBlock::iterator BI = FI->begin(), BE = FI->end(); BI != BE; ++BI) {

      if(CallInst* CI = extractMallocCall(BI, /* allow internal calls = */ true)) {

	DEBUG(dbgs() << "Consider malloc " << (*CI) << "\n");

	GlobalStatus GS;
	SmallPtrSet<const PHINode*, 16> PHIUsers;
	if(!AnalyzeGlobal(CI, GS, PHIUsers)) {

	  if(!GS.isLoaded) {

	    DEBUG(dbgs() << "Try-elim malloc " << (*CI) << "\n");
	
	    Changed |= CleanupConstantGlobalUsers(CI, 0);
	    if (CI->use_empty()) {
	      DEBUG(dbgs() << "Delete malloc " << (*CI) << "\n");
	      Changed = true;
	      eraseCIs.push_back(CI);
	    }

	  }

	}

      }

    }

    for(SmallVector<CallInst*, 4>::iterator it = eraseCIs.begin(), endit = eraseCIs.end(); it != endit; ++it) {

      (*it)->eraseFromParent();

    }

  }

  return Changed;

}
