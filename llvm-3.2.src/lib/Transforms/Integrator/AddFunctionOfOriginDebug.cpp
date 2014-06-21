// A pass to help a profiler: this tags all instructions with fake filenames indicating their function of origin: thus we can see where a particular instruction originated in the source code, even through inlining.

// Note it appears that DWARF supports describing this sort of information, but some element in the pipeline Dragonegg -> llvm-opt -> GOLD-plugin-linker is not recording or preserving it (or perhaps LLVM's debug info just doesn't match DWARF well enough)

#define DEBUG_TYPE "delink"

#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Value.h"
#include "llvm/DerivedTypes.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/DebugInfo.h"
#include "llvm/Support/Dwarf.h"
#include "llvm/DIBuilder.h"

#include <string>
#include <algorithm> 
#include <functional> 
#include <cctype>
#include <locale>
#include <fstream>

using namespace llvm;

namespace {

  class AddFOODebugPass : public ModulePass {

    DIType fakeDebugType;

  public:

    static char ID;
    AddFOODebugPass() : ModulePass(ID) {}

    bool runOnModule(Module& M);
    bool hasDebugInfo(Function&);
    void addDebugInfo(Function&);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {};

  };

}

char AddFOODebugPass::ID = 0;
static RegisterPass<AddFOODebugPass> X("add-foo-debug", "Add function-of-origin debug tags",
				       false /* Only looks at CFG */,
				       false /* Analysis Pass */);

namespace llvm {

  Pass* createAddFOODebugPass() { return new AddFOODebugPass(); }

}

bool AddFOODebugPass::runOnModule(Module& M) {

  DIBuilder DIB(M);
  DIB.createCompileUnit(dwarf::DW_LANG_C89, "llpe.file", "/nonesuch", "LLPE", true, "", 0);
  this->fakeDebugType = DIB.createBasicType("fakechar", 8, 0, dwarf::DW_ATE_signed);

  for(Module::iterator MI = M.begin(), ME = M.end(); MI != ME; ++MI)
    if(!hasDebugInfo(*MI))
      addDebugInfo(*MI);

  return true;

}

bool AddFOODebugPass::hasDebugInfo(Function& F) {

  for(Function::iterator it = F.begin(), itend = F.end(); it != itend; ++it) {
    
    for(BasicBlock::iterator IIt = it->begin(), IEnd = it->end(); IIt != IEnd; ++IIt)
      if(!IIt->getDebugLoc().isUnknown())
	return true;
    
  }
  
  return false;

}

void AddFOODebugPass::addDebugInfo(Function& F) {

  std::string fakeFilename;
  {
    raw_string_ostream RSO(fakeFilename);
    RSO << "__fakedebug__" << F.getName();
  }

  DIBuilder DIB(*F.getParent());

  DIFile fakeFile = DIB.createFile(fakeFilename, "/nonesuch");
  DISubprogram fakeFunction = DIB.createFunction(fakeFile, fakeFilename,
						 fakeFilename, fakeFile, 1,
						 fakeDebugType, false,
						 true, 1);
  DILexicalBlock fakeBlock = DIB.createLexicalBlock(fakeFunction, fakeFile, 1, 0);
  DebugLoc fakeLoc = DebugLoc::getFromDILexicalBlock(fakeBlock);

  for(Function::iterator it = F.begin(), itend = F.end();
      it != itend; ++it) {

    for(BasicBlock::iterator IIt = it->begin(), IEnd = it->end(); IIt != IEnd; ++IIt)
      IIt->setDebugLoc(fakeLoc);

  }

}
