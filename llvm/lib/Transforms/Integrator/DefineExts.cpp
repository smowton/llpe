// This pass takes a list of symbols on the command-line and defines them to null.
// In the future it will probably do more. This is to permit specialisation based on whether a weak symbol will be defined or not.

#define DEBUG_TYPE "define-exts"

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Function.h"
#include "llvm/Value.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

#include <string>

using namespace llvm;

static cl::list<std::string> NullSymbols("null-symbol", cl::ZeroOrMore);

namespace {

  class DefineExtsPass : public ModulePass {
  public:

    static char ID;
    DefineExtsPass() : ModulePass(ID) {}

    bool runOnModule(Module& M);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const;

  };

}

char DefineExtsPass::ID = 0;
INITIALIZE_PASS(DefineExtsPass, "define-exts", "Define external symbols", false, false);

Pass* llvm::createDefineExtsPass() { return new DefineExtsPass(); }

bool DefineExtsPass::runOnModule(Module& M) {

  bool modified = false;

  for(cl::list<std::string>::iterator it = NullSymbols.begin(), it2 = NullSymbols.end(); it != it2; ++it) {

    GlobalValue* GV = M.getNamedValue(*it);
    if(!GV) {

      errs() << "Warning: skipped value " << *it << " (symbol not found)\n";
      continue;

    }
    
    if(Function* F = dyn_cast<Function>(GV)) {
      if(!F->isDeclaration()) {

	errs() << "Warning: skipped function " << *it << " because it has a definition\n";
	continue;

      }
    }

    GV->replaceAllUsesWith(Constant::getNullValue(GV->getType()));
    modified = true;

  }

  return modified;

}

void DefineExtsPass::getAnalysisUsage(AnalysisUsage& AU) const {
}


