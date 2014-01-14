// This pass takes a list of symbols on the command-line and defines them to null.
// Externalizes a list of symbols. For libraries that have been analysed in-module but should be ultimately imported at runtime.

#define DEBUG_TYPE "delink"

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Value.h"
#include "llvm/DerivedTypes.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"

#include <string>
#include <algorithm> 
#include <functional> 
#include <cctype>
#include <locale>
#include <fstream>

using namespace llvm;

static cl::opt<std::string> DelinkSymbols("delink-symbols");
static cl::opt<std::string> DelinkExcept("delink-except");

namespace {

  class DelinkPass : public ModulePass {
  public:

    static char ID;
    DelinkPass() : ModulePass(ID) {}

    bool runOnModule(Module& M);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {};

  };

}

char DelinkPass::ID = 0;
static RegisterPass<DelinkPass> X("delink", "De-link",
				  false /* Only looks at CFG */,
				  false /* Analysis Pass */);

namespace llvm {

  Pass* createDelinkPass() { return new DelinkPass(); }

}

// trim from start
static inline std::string &ltrim(std::string &s) {
        s.erase(s.begin(), std::find_if(s.begin(), s.end(), std::not1(std::ptr_fun<int, int>(std::isspace))));
        return s;
}

// trim from end
static inline std::string &rtrim(std::string &s) {
        s.erase(std::find_if(s.rbegin(), s.rend(), std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
        return s;
}

// trim from both ends
static inline std::string &trim(std::string &s) {
        return ltrim(rtrim(s));
}

bool DelinkPass::runOnModule(Module& M) {

  if(DelinkExcept.size()) {

    std::ifstream RFI(DelinkExcept.c_str());

    DenseSet<GlobalValue*> Keep;
  
    while(!RFI.eof()) {

      std::string line;
      std::getline(RFI, line);

      trim(line);

      if(line.empty())
	continue;

      GlobalValue* GV = M.getNamedValue(line);
      if(!GV) {
	
	errs() << "Warning: Skipped " << line << "\n";
	continue;

      }

      Keep.insert(GV);
  
    }

    for(Module::iterator it = M.begin(), itend = M.end(); it != itend; ++it) {

      if(!Keep.count(it))
	it->deleteBody();

    }

  }
  else {

    std::ifstream RFI(DelinkSymbols.c_str());
  
    while(!RFI.eof()) {

      std::string line;
      std::getline(RFI, line);

      trim(line);

      if(line.empty())
	continue;

      if(line == "__uClibc_main" || line == "__uClibc_main_spec")
	continue;
    
      GlobalValue* GV = M.getNamedValue(line);
      if(!GV) {

	errs() << "Warning: Skipped " << line << "\n";
	continue;

      }
    
      if(Function* F = dyn_cast<Function>(GV))
	F->deleteBody();

    }

  }

  return true;

}
