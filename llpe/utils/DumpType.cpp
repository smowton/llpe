//===-- DumpType.cpp ------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm {

class Type;
class Value;

class DumpTypePass : public ModulePass {
public:

  StructType* Print;
  const StructLayout* Layout;

  static char ID; // Pass identification, replacement for typeid
  DumpTypePass() : ModulePass(ID), Print(0) {
    //initializeDumpTypePass(*PassRegistry::getPassRegistry());
  }

  /// Print the types found in the module.  If the optional Module parameter is
  /// passed in, then the types are printed symbolically if possible, using the
  /// symbol table from the module.
  ///
  void print(raw_ostream &o, const Module *M) const;

public:
  /// run - This incorporates all types used by the specified module
  bool runOnModule(Module &M);

  /// getAnalysisUsage - We do not modify anything.
  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }
};

}

using namespace llvm;

static cl::opt<std::string> PrintName("dump-type-name", cl::init(""));
static cl::opt<std::string> PrintGlobal("dump-type-of-global", cl::init(""));

static RegisterPass<DumpTypePass> X("dump-type", "Describe a named type",
						 false /* Only looks at CFG */,
						 true /* Analysis Pass */);

char DumpTypePass::ID = 0;

bool DumpTypePass::runOnModule(Module &M) {

  if(PrintName == "" && PrintGlobal == "") {
    errs() << "Must specify dump-type-name or dump-type-of-global";
    exit(1);
  }

  if(PrintName != "")
    Print = M.getTypeByName(PrintName);
  else {
    GlobalValue* GV = M.getNamedValue(PrintGlobal);
    if(!GV) {
      errs() << "Global " << PrintGlobal << " not found\n";
      exit(1);
    }

    PointerType* PT = dyn_cast<PointerType>(GV->getType());
    if(!PT) {
      errs() << "Global " << PrintGlobal << " not pointer typed\n";
      exit(1);
    }

    Print = dyn_cast<StructType>(PT->getElementType());
    if(!Print) {
      errs() << "Global " << PrintGlobal << " doesn't point to a struct\n";
      exit(1);
    }

  }

  const DataLayout* DL = &M.getDataLayout();
  Layout = DL->getStructLayout(Print);

  return false;
  
}

void DumpTypePass::print(raw_ostream &OS, const Module *M) const {

  OS << "Layout for " << Print->getName() << ":\n";
  
  for(uint32_t i = 0, ilim = Print->getNumElements(); i != ilim; ++i) {

    Type* El = Print->getElementType(i);
    uint64_t Off = Layout->getElementOffset(i);

    OS << "Element " << i << " at offset " << Off << ": " << (*El) << "\n";

  }

}
