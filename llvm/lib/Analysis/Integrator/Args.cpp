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

// Fetch an environment (newline-delimited key=value settings) from path and use it as @__environ.
void IntegrationHeuristicsPass::loadEnvironment(Module& M, std::string& path) {

  std::string error;
  MemoryBuffer* MB = MemoryBuffer::getFile(path, &error);
  if(!MB) {

    errs() << "Failed to load environment from " << path << ": " << error << "\n";
    exit(1);

  }

  std::string useenv = MB->getBuffer();
  if(useenv.size() == 0 || useenv[useenv.size() - 1] != '\n') {
    useenv += '\n';
  }

  size_t startidx = 0;

  std::vector<size_t> lineStarts;

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
      startidx = findidx + 1;

    }

  }

  Constant* EnvInit = ConstantArray::get(M.getContext(), useenv, false);
  GlobalVariable* EnvInitG = new GlobalVariable(M, EnvInit->getType(), true, GlobalValue::PrivateLinkage, EnvInit, "spec_env_str");

  // Build an array of GEPs into that string:
  std::vector<Constant*> lineStartConsts;
  const Type* Int64 = Type::getInt64Ty(M.getContext());
  Constant* Zero = ConstantInt::get(Int64, 0);

  for(std::vector<size_t>::iterator it = lineStarts.begin(), it2 = lineStarts.end(); it != it2; ++it) {

    Constant* gepArgs[] = { Zero, ConstantInt::get(Int64, *it) };
    lineStartConsts.push_back(ConstantExpr::getGetElementPtr(EnvInitG, gepArgs, 2));

  }

  lineStartConsts.push_back(Constant::getNullValue(Type::getInt8PtrTy(M.getContext())));
			    
  const ArrayType* PtrArrT = ArrayType::get(lineStartConsts[0]->getType(), lineStartConsts.size());
  Constant* PtrArray = ConstantArray::get(PtrArrT, lineStartConsts);
  GlobalVariable* EnvPtrsG = new GlobalVariable(M, PtrArray->getType(), true, GlobalValue::PrivateLinkage, PtrArray, "spec_env_ptrs");
  Constant* gepArgs[] = { Zero, Zero };
  Constant* EnvPtrsPtr = ConstantExpr::getGetElementPtr(EnvPtrsG, gepArgs, 2);

  GlobalVariable* RealEnv = M.getGlobalVariable("__environ", true);
  if(!RealEnv) {

    errs() << "Source file did not contain a global __environ!\n";
    exit(1);

  }
  RealEnv->setInitializer(EnvPtrsPtr);

}
