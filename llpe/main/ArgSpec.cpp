//===-- ArgSpec.cpp -------------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

// Implement specialisation w.r.t. environment or argv.

#include <stdlib.h>
#include <ctype.h>
#include <string>

#include "llvm/Analysis/LLPE.h"

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Attributes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/MemoryBuffer.h"

using namespace llvm;

// Read a file into a std::string
static void readWholeFile(std::string& path, std::string& out, bool addnewline) {

  ErrorOr<std::unique_ptr<MemoryBuffer>> MB = MemoryBuffer::getFile(path);
  if(std::error_code ec = MB.getError()) {

    errs() << "Failed to load from " << path << ": " << ec.message() << "\n";
    exit(1);

  }

  out = (*MB)->getBuffer();
  if(addnewline && (out.size() == 0 || out[out.size() - 1] != '\n')) {
    out += '\n';
  }  

}

// Create a new constant global pointing to a maybe-null-terminated string
GlobalVariable* llvm::getStringArray(std::string& bytes, Module& M, bool addNull) {

  Constant* EnvInit = ConstantDataArray::getString(M.getContext(), bytes, addNull);  
  return new GlobalVariable(M, EnvInit->getType(), true, GlobalValue::PrivateLinkage, EnvInit, "spec_env_str");

}

// Create an array of pointers into a constant string, as seen in C's argv and env pointers.
static Constant* getStringPtrArray(std::string& bytes, std::vector<size_t>& lineStarts, Module& M) {

  GlobalVariable* EnvInitG = getStringArray(bytes, M);

  // Build an array of GEPs into that string:
  std::vector<Constant*> lineStartConsts;
  Type* Int64 = Type::getInt64Ty(M.getContext());
  Type* I8P = Type::getInt8PtrTy(M.getContext());
  Constant* Zero = ConstantInt::get(Int64, 0);

  for(unsigned i = 0; i < lineStarts.size(); ++i) {

    size_t start = lineStarts[i];

    Constant* gepArgs[] = { Zero, ConstantInt::get(Int64, start) };
    lineStartConsts.push_back(ConstantExpr::getGetElementPtr(0, EnvInitG, gepArgs));

  }

  // Conclude with 2 nulls to signal we don't supply an ELF header at spec time.
  lineStartConsts.push_back(Constant::getNullValue(I8P));
  lineStartConsts.push_back(Constant::getNullValue(I8P));
			    
  ArrayType* PtrArrT = ArrayType::get(lineStartConsts[0]->getType(), lineStartConsts.size());
  Constant* PtrArray = ConstantArray::get(PtrArrT, lineStartConsts);
  GlobalVariable* EnvPtrsG = new GlobalVariable(M, PtrArray->getType(), true, GlobalValue::PrivateLinkage, PtrArray, "spec_env_ptrs");
  Constant* gepArgs[] = { Zero, Zero };
  Constant* EnvPtrsPtr = ConstantExpr::getGetElementPtr(0, EnvPtrsG, gepArgs);

  return EnvPtrsPtr;

}

// Fetch a newline-delimited command-line (saves escaping spaces etc) and provide a char** argv replacement.
void LLPEAnalysisPass::loadArgv(Function* F, std::string& path, unsigned argvIdx, unsigned& argc) {

  std::string argvtext;
  readWholeFile(path, argvtext, true);

  size_t startidx = 0;

  std::vector<int> lineStarts;

  for(size_t findidx = argvtext.find('\n'); findidx != std::string::npos; findidx = argvtext.find('\n', startidx)) {

    bool foundalpha = false;

    for(size_t i = startidx; i != findidx; ++i) {

      if(!isspace(argvtext[i]))
	foundalpha = true;

    }

    bool isUnknown = false;
    if(!argvtext.compare(startidx, findidx - startidx, "__undef__")) {
      lineStarts.push_back(-1);
      isUnknown = true;
    }

    if((!foundalpha) || isUnknown) {

      argvtext.erase(startidx, (findidx - startidx) + 1);
      // Start search again from the same index.

    }
    else {

      argvtext.replace(findidx, 1, 1, '\0');
      lineStarts.push_back(startidx);
      
      startidx = findidx + 1;

    }

  }

  argc = lineStarts.size();
  GlobalVariable* ArgvConsts = getStringArray(argvtext, *(F->getParent()));

  BasicBlock& EntryBB = F->getEntryBlock();
  BasicBlock::iterator BI = EntryBB.begin();
  while(isa<AllocaInst>(BI))
    ++BI;

  Instruction* InsertBefore = &*BI;

  Function::arg_iterator Arg = F->arg_begin();
  for(long i = 0; i < argvIdx; ++i)
    ++Arg;

  Type* Int64 = Type::getInt64Ty(F->getContext());
  Type* BytePtr = Type::getInt8PtrTy(F->getContext());
  for(unsigned i = 0; i < argc; ++i) {

    if(lineStarts[i] != -1) {
      
      // Get a pointer into the constant argv:
      Constant* gepArgs[] = { ConstantInt::get(Int64, 0), ConstantInt::get(Int64, lineStarts[i]) };
      Constant* stringPtr = ConstantExpr::getGetElementPtr(0, ArgvConsts, gepArgs);

      // Get a pointer into the real argv:
      Constant* gepArg = ConstantInt::get(Int64, i);
      Instruction* argvPtr = GetElementPtrInst::Create(BytePtr, &*Arg, gepArg, "argv_ptr", InsertBefore);
      new StoreInst(stringPtr, argvPtr, InsertBefore);

    }

  }

  // Null terminate the argv array:
  Constant* gepArg = ConstantInt::get(Int64, argc);
  Instruction* argvEndPtr = GetElementPtrInst::Create(BytePtr, &*Arg, gepArg, "argv_end_ptr", InsertBefore);
  Constant* nullPtr = Constant::getNullValue(BytePtr);
  new StoreInst(nullPtr, argvEndPtr, InsertBefore);

  F->addParamAttr(argvIdx, Attribute::NoAlias);

}

// Fetch an environment (newline-delimited key=value settings) from path and provide a constant suitable for replacing the char** environ pointer.
Constant* LLPEAnalysisPass::loadEnvironment(Module& M, std::string& path) {

  std::string useenv;
  readWholeFile(path, useenv, true);

  size_t startidx = 0;

  std::vector<size_t> lineStarts;
  std::vector<bool> lineUnknown;

  for(size_t findidx = useenv.find('\n'); findidx != std::string::npos; findidx = useenv.find('\n', startidx)) {

    bool foundalpha = false;
    bool foundequals = false;

    for(size_t i = startidx; i != findidx; ++i) {

      if(useenv[i] == '=')
	foundequals = true;
      if(!isspace(useenv[i]))
	foundalpha = true;

    }

    if(!foundequals) {

      if(foundalpha) {

	errs() << "Warning: discarded junk " << useenv.substr(startidx, findidx - startidx) << "\n";

      }

      useenv.erase(startidx, (findidx - startidx) + 1);
      // Start search again from the same index.

    }
    else {

      useenv.replace(findidx, 1, 1, '\0');
      lineStarts.push_back(startidx);
      lineUnknown.push_back(false);
      startidx = findidx + 1;

    }

  }

  return getStringPtrArray(useenv, lineStarts, M);
  
}
