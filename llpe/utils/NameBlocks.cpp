// Name anonymous basic blocks with integer names, as GCC does per default. Makes them easier to describe.

#define DEBUG_TYPE "nameblocks"

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"

#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

  class NameBlocksPass : public ModulePass {
  public:

    static char ID;
    NameBlocksPass() : ModulePass(ID) {}

    bool runOnModule(Module& M);
    void runOnFunction(Function* F);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const { };

  };

}

char NameBlocksPass::ID = 0;
static RegisterPass<NameBlocksPass> X("nameblocks", "Name anonymous blocks with integers (i.e. <label>:%0 -> \"0\" or some other int)",
				      false /* CFG only? */,
				      false /* Is analysis? */);

namespace llvm {

  Pass* createNameBlocksPass() { return new NameBlocksPass(); }

}

void NameBlocksPass::runOnFunction(Function* F) {

  uint64_t NameInt = 0;
  std::string Name;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    if(!FI->hasName()) {

      Name.clear();
      {
	raw_string_ostream RSO(Name);
	RSO << (++NameInt);
      }
      FI->setName(Name);

    }

  }

}

bool NameBlocksPass::runOnModule(Module& M) {

  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI)
    runOnFunction(&*MI);

  return true;

}
