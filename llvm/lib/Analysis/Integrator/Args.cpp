// Implement specialisation w.r.t. environment or argv.

#include <stdlib.h>
#include <ctype.h>
#include <string>

#include "llvm/Analysis/HypotheticalConstantFolder.h"

#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Module.h"
#include "llvm/Type.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Constants.h"
#include "llvm/GlobalVariable.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static void readWholeFile(std::string& path, std::string& out, bool addnewline) {

  std::string error;
  MemoryBuffer* MB = MemoryBuffer::getFile(path, &error);
  if(!MB) {

    errs() << "Failed to load from " << path << ": " << error << "\n";
    exit(1);

  }

  out = MB->getBuffer();
  if(addnewline && (out.size() == 0 || out[out.size() - 1] != '\n')) {
    out += '\n';
  }  

}

static Constant* getStringPtrArray(std::string& bytes, std::vector<size_t>& lineStarts, std::vector<bool>& lineUnknown, Module& M) {

  Constant* EnvInit = ConstantArray::get(M.getContext(), bytes, false);
  GlobalVariable* EnvInitG = new GlobalVariable(M, EnvInit->getType(), true, GlobalValue::PrivateLinkage, EnvInit, "spec_env_str");

  // Build an array of GEPs into that string:
  std::vector<Constant*> lineStartConsts;
  const Type* Int64 = Type::getInt64Ty(M.getContext());
  Constant* Zero = ConstantInt::get(Int64, 0);

  for(unsigned i = 0; i < lineStarts.size(); ++i) {

    size_t start = lineStarts[i];
    bool unknown = lineUnknown[i];

    size_t offset;
    Constant* base;

    if(unknown) {

      GlobalVariable* UnknownStr = new GlobalVariable(M, ArrayType::get(Type::getInt8Ty(M.getContext()), 1), false, GlobalValue::PrivateLinkage, 0, "unknown_spec_str");
      offset = 0;
      base = UnknownStr;      

    }
    else {
      
      offset = start;
      base = EnvInitG;

    }

    Constant* gepArgs[] = { Zero, ConstantInt::get(Int64, offset) };
    lineStartConsts.push_back(ConstantExpr::getGetElementPtr(base, gepArgs, 2));

  }

  lineStartConsts.push_back(Constant::getNullValue(Type::getInt8PtrTy(M.getContext())));
			    
  const ArrayType* PtrArrT = ArrayType::get(lineStartConsts[0]->getType(), lineStartConsts.size());
  Constant* PtrArray = ConstantArray::get(PtrArrT, lineStartConsts);
  GlobalVariable* EnvPtrsG = new GlobalVariable(M, PtrArray->getType(), true, GlobalValue::PrivateLinkage, PtrArray, "spec_env_ptrs");
  Constant* gepArgs[] = { Zero, Zero };
  Constant* EnvPtrsPtr = ConstantExpr::getGetElementPtr(EnvPtrsG, gepArgs, 2);

  return EnvPtrsPtr;

}

// Fetch a newline-delimited command-line (saves escaping spaces etc) and provide a char** argv replacement.
Constant* IntegrationHeuristicsPass::loadArgv(Module& M, std::string& path, unsigned& argc) {

  std::string argvtext;
  readWholeFile(path, argvtext, true);

  size_t startidx = 0;

  std::vector<size_t> lineStarts;
  std::vector<bool> lineUnknown;

  for(size_t findidx = argvtext.find('\n'); findidx != std::string::npos; findidx = argvtext.find('\n', startidx)) {

    bool foundalpha = false;

    for(size_t i = startidx; i != findidx; ++i) {

      if(!isspace(argvtext[i]))
	foundalpha = true;

    }

    bool isUnknown = false;
    if(!argvtext.compare(startidx, findidx - startidx, "__undef__")) {
      lineUnknown.push_back(true);
      lineStarts.push_back(-1);
      isUnknown = true;
    }

    if((!foundalpha) || isUnknown) {

      argvtext.erase(startidx, (findidx - startidx) + 1);
      // Start search again from the same index.

    }
    else {

      argvtext.replace(findidx, 1, 1, '\0');
      lineUnknown.push_back(false);
      lineStarts.push_back(startidx);
      
      startidx = findidx + 1;

    }

  }

  argc = lineStarts.size();
  return getStringPtrArray(argvtext, lineStarts, lineUnknown, M);

}

// Fetch an environment (newline-delimited key=value settings) from path and provide a constant suitable for replacing the char** environ pointer.
Constant* IntegrationHeuristicsPass::loadEnvironment(Module& M, std::string& path) {

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

  return getStringPtrArray(useenv, lineStarts, lineUnknown, M);
  
}
