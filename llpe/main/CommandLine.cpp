//===-- CommandLine.cpp ---------------------------------------------------===//
//
//                                  LLPE
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/Support/CommandLine.h"

#include <sstream>
#include <string>

#define DEBUG_TYPE "llpe-misc"

using namespace llvm;

// Command-line args. See llpe.org for documentation.
// One extra arg is declared in TopLevel.cpp: the root function name.

static cl::opt<std::string> GraphOutputDirectory("llpe-graphs-dir", cl::init(""));
static cl::opt<std::string> EnvFileAndIdx("spec-env", cl::init(""));
static cl::opt<std::string> ArgvFileAndIdxs("spec-argv", cl::init(""));
static cl::opt<unsigned> MallocAlignment("llpe-malloc-alignment", cl::init(1));
static cl::list<std::string> SpecialiseParams("spec-param", cl::ZeroOrMore);
static cl::list<std::string> AlwaysInlineFunctions("llpe-always-inline", cl::ZeroOrMore);
static cl::list<std::string> OptimisticLoops("llpe-optimistic-loop", cl::ZeroOrMore);
static cl::list<std::string> AlwaysIterLoops("llpe-always-iterate", cl::ZeroOrMore);
static cl::list<std::string> AssumeEdges("llpe-assume-edge", cl::ZeroOrMore);
static cl::list<std::string> IgnoreLoops("llpe-ignore-loop", cl::ZeroOrMore);
static cl::list<std::string> IgnoreLoopsWithChildren("llpe-ignore-loop-children", cl::ZeroOrMore);
static cl::list<std::string> AlwaysExploreFunctions("llpe-always-explore", cl::ZeroOrMore);
static cl::list<std::string> LoopMaxIters("llpe-loop-max", cl::ZeroOrMore);
static cl::list<std::string> IgnoreBlocks("llpe-ignore-block", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsInt("llpe-path-condition-int", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsFptr("llpe-path-condition-fptr", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsString("llpe-path-condition-str", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsIntmem("llpe-path-condition-intmem", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsFptrmem("llpe-path-condition-fptrmem", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsFunc("llpe-path-condition-func", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsStream("llpe-path-condition-stream", cl::ZeroOrMore);
static cl::list<std::string> PathConditionsGlobalInit("llpe-path-condition-global-unmodified", cl::ZeroOrMore);
static cl::opt<bool> SkipBenefitAnalysis("skip-benefit-analysis");
static cl::opt<bool> SkipDIE("skip-llpe-die");
static cl::opt<bool> SkipTL("skip-check-elim");
static cl::opt<unsigned> MaxContexts("llpe-stop-after", cl::init(0));
static cl::opt<bool> VerboseOverdef("llpe-verbose-overdef");
static cl::opt<bool> EnableFunctionSharing("llpe-enable-sharing");
static cl::opt<bool> VerboseFunctionSharing("llpe-verbose-sharing");
static cl::opt<bool> UseGlobalInitialisers("llpe-use-global-initialisers");
static cl::list<std::string> SpecialLocations("llpe-special-location", cl::ZeroOrMore);
static cl::list<std::string> ModelFunctions("llpe-model-function", cl::ZeroOrMore);
static cl::list<std::string> YieldFunctions("llpe-yield-function", cl::ZeroOrMore);
static cl::list<std::string> TargetStack("llpe-target-stack", cl::ZeroOrMore);
static cl::list<std::string> SimpleVolatiles("llpe-simple-volatile-load", cl::ZeroOrMore);
static cl::list<std::string> LockDomains("llpe-lock-domain", cl::ZeroOrMore);
static cl::list<std::string> PessimisticLocks("llpe-pessimistic-lock", cl::ZeroOrMore);
static cl::opt<bool> DumpDSE("llpe-dump-dse");
static cl::opt<bool> DumpTL("llpe-dump-tl");
static cl::list<std::string> ForceNoAliasArgs("llpe-force-noalias-arg", cl::ZeroOrMore);
static cl::list<std::string> VarAllocators("llpe-allocator-fn", cl::ZeroOrMore);
static cl::list<std::string> ConstAllocators("llpe-allocator-fn-const", cl::ZeroOrMore);
static cl::opt<bool> VerbosePathConditions("llpe-verbose-path-conditions");
static cl::opt<std::string> LLIOPreludeFn("llpe-prelude-fn", cl::init(""));
static cl::opt<int> LLIOPreludeStackIdx("llpe-prelude-stackidx", cl::init(-1));
static cl::opt<std::string> LLIOConfFile("llpe-write-llio-conf", cl::init(""));
static cl::opt<std::string> StatsFile("llpe-stats-file", cl::init(""));
static cl::list<std::string> NeverInline("llpe-never-inline", cl::ZeroOrMore);
static cl::opt<bool> SingleThreaded("llpe-single-threaded");
static cl::opt<bool> OmitChecks("llpe-omit-checks");
static cl::opt<bool> OmitMallocChecks("llpe-omit-malloc-checks");
static cl::list<std::string> SplitFunctions("llpe-force-split");
static cl::opt<bool> EmitFakeDebug("llpe-emit-fake-debug");

static void dieEnvUsage() {

  errs() << "--spec-env must have form N,filename where N is an integer\n";
  exit(1);

}

static void dieArgvUsage() {

  errs() << "--spec-argv must have form M,N,filename where M and N are integers\n";
  exit(1);

}

static void dieSpecUsage() {

  errs() << "--spec-param must have form N,param-spec where N is an integer\n";
  exit(1);

}

static bool parseIntCommaString(const std::string& str, long& idx, std::string& rest) {

  size_t splitIdx = str.find(',');

  if(splitIdx == std::string::npos || splitIdx == 0 || splitIdx == EnvFileAndIdx.size() - 1) {
    return false;
  }
  
  rest = str.substr(splitIdx + 1);
  std::string idxstr = str.substr(0, splitIdx);
  char* IdxEndPtr;
  idx = strtol(idxstr.c_str(), &IdxEndPtr, 10);
  
  if(IdxEndPtr - idxstr.c_str() != (int64_t)idxstr.size()) {
    return false;
  }
  
  return true;

}

static void parseFB(const char* paramName, const std::string& arg, Module& M, Function*& F, BasicBlock*& BB1) {

  std::string FName, BB1Name;
  size_t firstComma = arg.find(',');
  if(firstComma == std::string::npos) {
    errs() << "--" << paramName << " must have the form fname,bbname\n";
    exit(1);
  }

  FName = arg.substr(0, firstComma);
  BB1Name = arg.substr(firstComma + 1);

  F = M.getFunction(FName);
  if(!F) {
    errs() << "No such function " << FName << "\n";
    exit(1);
  }

  BB1 = 0;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    if(FI->getName() == BB1Name) {
      BB1 = &*FI;
      break;
    }

  }

  if(!BB1) {
    errs() << "No such block " << BB1Name << " in " << FName << "\n";
    exit(1);
  }

}

static void parseFBB(const char* paramName, const std::string& arg, Module& M, Function*& F, BasicBlock*& BB1, BasicBlock*& BB2) {

  std::string FName, BB1Name, BB2Name;
  size_t firstComma = arg.find(',');
  size_t secondComma = std::string::npos;
  if(firstComma != std::string::npos)
    secondComma = arg.find(',', firstComma+1);
  if(firstComma == std::string::npos || secondComma == std::string::npos) {
    errs() << "--" << paramName << " must have the form fname,bbname,bbname\n";
    exit(1);
  }

  FName = arg.substr(0, firstComma);
  BB1Name = arg.substr(firstComma + 1, (secondComma - firstComma) - 1);
  BB2Name = arg.substr(secondComma + 1);

  F = M.getFunction(FName);
  if(!F) {
    errs() << "No such function " << FName << "\n";
    exit(1);
  }

  BB1 = BB2 = 0;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    if(FI->getName() == BB1Name)
      BB1 = &*FI;
    if(FI->getName() == BB2Name)
      BB2 = &*FI;

  }

  if(!BB1) {
    errs() << "No such block " << BB1Name << " in " << FName << "\n";
    exit(1);
  }
  if(!BB2) {
    errs() << "No such block " << BB2Name << " in " << FName << "\n";
    exit(1);
  }

}

static void parseFBI(const char* paramName, const std::string& arg, Module& M, Function*& F, BasicBlock*& BB, uint64_t& IOut) {

  std::string FName, BBName, IStr;
  size_t firstComma = arg.find(',');
  size_t secondComma = std::string::npos;
  if(firstComma != std::string::npos)
    secondComma = arg.find(',', firstComma+1);
  if(firstComma == std::string::npos || secondComma == std::string::npos) {
    errs() << "--" << paramName << " must have the form fname,bbname,int\n";
    exit(1);
  }

  FName = arg.substr(0, firstComma);
  BBName = arg.substr(firstComma + 1, (secondComma - firstComma) - 1);
  IStr = arg.substr(secondComma + 1);

  F = M.getFunction(FName);
  if(!F) {
    errs() << "No such function " << FName << "\n";
    exit(1);
  }

  BB = 0;

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {

    if(FI->getName() == BBName)
      BB = &*FI;

  }

  if(!BB) {
    errs() << "No such block " << BBName << " in " << FName << "\n";
    exit(1);
  }

  char* IdxEndPtr;
  IOut = strtol(IStr.c_str(), &IdxEndPtr, 10);
  
  if(IdxEndPtr - IStr.c_str() != (int64_t)IStr.size()) {
    errs() << "Couldn't parse " << IStr << " as an integer\n";
    exit(1);
  }

}

void LLPEAnalysisPass::setParam(InlineAttempt* IA, long Idx, Constant* Val) {

  Type* Target = IA->F.getFunctionType()->getParamType(Idx);

  if(Val->getType() != Target) {

    errs() << "Type mismatch: constant " << *Val << " supplied for parameter of type " << *Target << "\n";
    exit(1);

  }

  ImprovedValSetSingle* ArgPB = newIVS();
  getImprovedValSetSingle(ShadowValue(Val), *ArgPB);
  if(ArgPB->Overdef || ArgPB->Values.size() != 1) {

    errs() << "Couldn't get a PB for " << *Val << "\n";
    exit(1);

  }

  IA->argShadows[Idx].i.PB = ArgPB;

}

#define CHECK_ARG(i, c) if(((uint32_t)i) >= c.size()) { errs() << "Function " << F.getName() << " has does not have a (zero-based) argument #" << i << "\n"; exit(1); }

static int64_t getInteger(std::string& s, const char* desc) {

  char* end;
  int64_t instIndex = strtoll(s.c_str(), &end, 10);
  if(s.empty() || *end) {
    errs() << desc << " not an integer\n";
    exit(1);
  }
  return instIndex;

}

static bool tryGetInteger(std::string& s, int64_t& out) {

  char* end;
  out = strtoll(s.c_str(), &end, 10);
  return !(s.empty() || *end);

}

uint32_t llvm::findBlock(ShadowFunctionInvar* SFI, StringRef name) {

  for(uint32_t i = 0; i < SFI->BBs.size(); ++i) {
    if(SFI->BBs[i].BB->getName() == name)
      return i;
  }  

  errs() << "Block " << name << " not found\n";
  exit(1);

}

uint32_t llvm::findBlock(ShadowFunctionInvar* SFI, BasicBlock* BB) {

  for(uint32_t i = 0; i < SFI->BBs.size(); ++i) {
    if(SFI->BBs[i].BB == BB)
      return i;
  }  

  errs() << "Block " << BB->getName() << " not found\n";
  exit(1);  

}

static BasicBlock* findBlockRaw(Function* F, std::string& name) {

  for(Function::iterator FI = F->begin(), FE = F->end(); FI != FE; ++FI) {
    if((&*FI)->getName() == name)
      return &*FI;
  }

  errs() << "Block " << name << " not found\n";
  exit(1);

}

static Type* getIntTypeAtOffset(Type* Ty, uint64_t Offset) {

  PointerType* Ptr = dyn_cast<PointerType>(Ty);
  if(!Ptr)
    return 0;

  Type* ElTy = Ptr->getElementType();

  if(StructType* ST = dyn_cast<StructType>(ElTy)) {

    const StructLayout* SL = GlobalTD->getStructLayout(ST);
    unsigned FieldNo = SL->getElementContainingOffset(Offset);
    release_assert(SL->getElementOffset(FieldNo) == Offset && "Bad path condition alignment");

    Type* ret = ST->getElementType(FieldNo);

    while(isa<ArrayType>(ret) || isa<StructType>(ret)) {
      if(isa<ArrayType>(ret))
	ret = cast<ArrayType>(ret)->getElementType();
      else
	ret = cast<StructType>(ret)->getElementType(0);
    }

    return ret;
    
  }
  else {

    return ElTy;

  }

}

BasicBlock* LLPEAnalysisPass::parsePCBlock(Function* fStack, std::string& bbName) {

  if(bbName == "__globals__")
    return 0;
  else if(bbName == "__args__")
    return (BasicBlock*)ULONG_MAX;
  else
    return findBlockRaw(fStack, bbName);
  
}

int64_t LLPEAnalysisPass::parsePCInst(BasicBlock* bb, Module* M, std::string& instIndexStr) {

  if(!bb) {
    GlobalVariable* GV = M->getGlobalVariable(instIndexStr, true);
    if(!GV) {

      errs() << "No global variable " << instIndexStr << "\n";
      exit(1);

    }
    return (int64_t)getShadowGlobalIndex(GV);
  }
  else
    return getInteger(instIndexStr, "Instruction index");

}

void LLPEAnalysisPass::parsePathConditions(cl::list<std::string>& L, PathConditionTypes Ty, InlineAttempt* IA) {

  uint32_t newGVIndex = 0;
  if(Ty == PathConditionTypeString)
    newGVIndex = std::distance(IA->F.getParent()->global_begin(), IA->F.getParent()->global_end());

  for(cl::list<std::string>::iterator it = L.begin(), itend = L.end(); it != itend; ++it) {

    std::string fStackIdxStr;
    std::string bbName;
    std::string instIndexStr;
    std::string assumeStr;
    std::string assumeStackIdxStr;
    std::string assumeBlock;
    std::string offsetStr;

    {
      std::istringstream istr(*it);
      std::getline(istr, fStackIdxStr, ',');
      std::getline(istr, bbName, ',');
      std::getline(istr, instIndexStr, ',');
      std::getline(istr, assumeStr, ',');
      std::getline(istr, assumeStackIdxStr, ',');
      std::getline(istr, assumeBlock, ',');
      std::getline(istr, offsetStr, ',');
    }

    if(fStackIdxStr.empty() || bbName.empty() || instIndexStr.empty() || assumeStr.empty() || assumeStackIdxStr.empty() || assumeBlock.empty()) {

      errs() << "Bad int path condtion\n";
      exit(1);

    }

    Function* fStack;

    int64_t fStackIdx;
    if(tryGetInteger(fStackIdxStr, fStackIdx)) {
      
      if(fStackIdx >= ((int64_t)targetCallStack.size())) {
	
	errs() << "Bad stack index\n";
	exit(1);

      }

      fStack = targetCallStack[fStackIdx].first->getParent();

    }
    else {

      fStack = IA->F.getParent()->getFunction(fStackIdxStr);
      if(!fStack) {

	errs() << "No function " << fStackIdxStr << "\n";
	exit(1);

      }

      fStackIdx = UINT_MAX;

    }

    BasicBlock* bb = parsePCBlock(fStack, bbName);
    int64_t instIndex = parsePCInst(bb, IA->F.getParent(), instIndexStr);
   
    uint32_t assumeStackIdx;
    Function* assumeF;
    if(fStackIdx != UINT_MAX) {

      assumeStackIdx = getInteger(assumeStackIdxStr, "Assume stack index");     

      if(assumeStackIdx >= targetCallStack.size()) {
	
	errs() << "Bad stack index\n";
	exit(1);
	
      }

      assumeF = targetCallStack[assumeStackIdx].first->getParent();

    }
    else {

      if(assumeStackIdxStr != fStackIdxStr) {

	errs() << "Non-stack path conditions must not make assumptions that cross function boundaries\n";
	exit(1);
	
      }

      assumeStackIdx = UINT_MAX;
      assumeF = fStack;

    }

    if(Ty == PathConditionTypeInt && assumeStackIdx != fStackIdx) {

      errs() << "SSA assumptions cannot cross function boundaries (assume about an argument instead)\n";
      exit(1);

    }

    BasicBlock* assumeBB = findBlockRaw(assumeF, assumeBlock);

    uint64_t offset = 0;
    if(!offsetStr.empty())
      offset = getInteger(offsetStr, "Path condition offset");

    Constant* assumeC;
    switch(Ty) {
    case PathConditionTypeInt:
    case PathConditionTypeIntmem:
      {
	int64_t assumeInt = getInteger(assumeStr, "Integer path condition");

	Type* targetType;
	if(bb) {
	  BasicBlock::iterator it = bb->begin();
	  std::advance(it, instIndex);
	  Instruction* assumeInst = &*it;
	  targetType = assumeInst->getType();
	}
	else if(bb == (BasicBlock*)ULONG_MAX) {
	  Function::arg_iterator it = fStack->arg_begin();
	  std::advance(it, instIndex);
	  Argument* A = &*it;
	  targetType = A->getType();
	}
	else {
	  GlobalVariable* GV = IA->F.getParent()->getGlobalVariable(instIndexStr, true);
	  targetType = GV->getType();
	}
	Type* ConstType;
	if(Ty == PathConditionTypeInt)
	  ConstType = targetType;
	else {
	  ConstType = getIntTypeAtOffset(targetType, offset);
	  release_assert(ConstType && "Failed to find assigned type for path condition");
	}
	release_assert((ConstType->isIntegerTy() || (ConstType->isPointerTy() && !assumeInt)) && "Instructions with an integer assumption must be integer typed");
	if(ConstType->isIntegerTy())
	  assumeC = ConstantInt::get(ConstType, assumeInt);
	else
	  assumeC = Constant::getNullValue(ConstType);
	break;
      }
    case PathConditionTypeFptr:
    case PathConditionTypeFptrmem:
      {
	int64_t Offset = 0;
	size_t plusOffset = assumeStr.find('+');
	if(plusOffset != std::string::npos) {
	  std::string offsetStr(assumeStr, plusOffset + 1);
	  Offset = getInteger(offsetStr, "Global value path condition +offset");
	  assumeStr = std::string(assumeStr, 0, plusOffset);
	}
	
	assumeC = IA->F.getParent()->getNamedValue(assumeStr);
	if(!assumeC) {
	  errs() << "No such global value: " << assumeStr << "\n";
	  exit(1);
	}

	if(Offset != 0) {
	  
	  if(assumeC->getType() != GInt8Ptr)
	    assumeC = ConstantExpr::getBitCast(assumeC, GInt8Ptr);
	  assumeC = ConstantExpr::getGetElementPtr(0, assumeC, ConstantInt::get(GInt64, Offset));

	}

	break;
      }
    case PathConditionTypeString:
      {
	GlobalVariable* NewGV = getStringArray(assumeStr, *IA->F.getParent(), /*addNull=*/true);
	assumeC = NewGV;
	// Register the new global:
	shadowGlobals[newGVIndex].G = NewGV;
	shadowGlobalsIdx[NewGV] = newGVIndex;
	shadowGlobals[newGVIndex].storeSize = 0;
	++newGVIndex;
	break;
      }
    case PathConditionTypeStream:
      assumeC = (Constant*)strdup(assumeStr.c_str());
      break;
    case PathConditionTypeGlobalInit:
      {
	release_assert((!bb) && "Unmodified global assumption relating to a non-global?");
	GlobalVariable* GV = shadowGlobals[instIndex].G;
	assumeC = GV->getInitializer();
	break;
      }
    default:
      release_assert(0 && "Bad path condition type");
      llvm_unreachable("Bad path condition type");
    }

    PathCondition newCond((uint32_t)fStackIdx, 
			  bb, 
			  (uint32_t)instIndex, 
			  assumeStackIdx, 
			  assumeBB, 
			  assumeC, 
			  offset);

    if(fStackIdx == UINT_MAX) {

      // Path condition applies to all instances of some function -- attach it to the invarInfo
      // for that function.

      ShadowFunctionInvar* invarInfo = getFunctionInvarInfo(*fStack);
      if(!invarInfo->pathConditions)
	invarInfo->pathConditions = new PathConditions();
      invarInfo->pathConditions->addForType(newCond, Ty);

    }
    else {

      pathConditions.addForType(newCond, Ty);

    }

  }

}

void LLPEAnalysisPass::parseArgs(Function& F, std::vector<Constant*>& argConstants, uint32_t& argvIdxOut) {

  this->statsFile = StatsFile;
  this->mallocAlignment = MallocAlignment;
  this->maxContexts = MaxContexts;
  
  if(EnvFileAndIdx != "") {

    long idx;
    std::string EnvFile;
    if(!parseIntCommaString(EnvFileAndIdx, idx, EnvFile))
      dieEnvUsage();

    CHECK_ARG(idx, argConstants);
    Constant* Env = loadEnvironment(*(F.getParent()), EnvFile);
    argConstants[idx] = Env;

  }

  if(ArgvFileAndIdxs != "") {

    long argcIdx;
    std::string ArgvFileAndIdx;
    if(!parseIntCommaString(ArgvFileAndIdxs, argcIdx, ArgvFileAndIdx))
      dieArgvUsage();
    long argvIdx;
    std::string ArgvFile;
    if(!parseIntCommaString(ArgvFileAndIdx, argvIdx, ArgvFile))
      dieArgvUsage();

    unsigned argc;
    loadArgv(&F, ArgvFile, argvIdx, argc);
    CHECK_ARG(argcIdx, argConstants);
    argConstants[argcIdx] = ConstantInt::get(Type::getInt32Ty(F.getContext()), argc);
    argvIdxOut = argvIdx;

  }

  for(cl::list<std::string>::const_iterator ArgI = SpecialiseParams.begin(), ArgE = SpecialiseParams.end(); ArgI != ArgE; ++ArgI) {

    long idx;
    std::string Param;
    if(!parseIntCommaString(*ArgI, idx, Param))
      dieSpecUsage();

    Type* ArgTy = F.getFunctionType()->getParamType(idx);
    
    if(ArgTy->isIntegerTy()) {

      char* end;
      int64_t arg = strtoll(Param.c_str(), &end, 10);
      if(end != (Param.c_str() + Param.size())) {

	errs() << "Couldn't parse " << Param << " as in integer\n";
	exit(1);

      }

      Constant* ArgC = ConstantInt::getSigned(ArgTy, arg);
      CHECK_ARG(idx, argConstants);
      argConstants[idx] = ArgC;

    }
    else if(PointerType* ArgTyP = dyn_cast<PointerType>(ArgTy)) {

      Type* StrTy = Type::getInt8PtrTy(F.getContext());
      Type* ElemTy = ArgTyP->getElementType();
      
      if(ArgTyP == StrTy) {

	Constant* Str = ConstantDataArray::getString(F.getContext(), Param);
	Constant* GStr = new GlobalVariable(*(F.getParent()), Str->getType(), true, GlobalValue::InternalLinkage, Str, "specstr");
	Constant* Zero = ConstantInt::get(Type::getInt64Ty(F.getContext()), 0);
	Constant* GEPArgs[] = { Zero, Zero };
	Constant* StrPtr = ConstantExpr::getGetElementPtr(0, GStr, GEPArgs, 2);
	CHECK_ARG(idx, argConstants);
	argConstants[idx] = StrPtr;

      }
      else if(ElemTy->isFunctionTy()) {

	Constant* Found = F.getParent()->getFunction(Param);

	if(!Found) {

	  // Check for a zero value, indicating a null pointer.
	  char* end;
	  int64_t arg = strtoll(Param.c_str(), &end, 10);

	  if(arg || end != Param.c_str() + Param.size()) {

	    errs() << "Couldn't find a function named " << Param << "\n";
	    exit(1);

	  }

	  Found = Constant::getNullValue(ArgTyP);

	}

	CHECK_ARG(idx, argConstants);
	argConstants[idx] = Found;

      }
      else {

	errs() << "Setting pointers other than char* not supported yet\n";
	exit(1);

      }

    }
    else {

      errs() << "Argument type " << *(ArgTy) << " not supported yet\n";
      exit(1);

    }

  }

  for(cl::list<std::string>::const_iterator ArgI = AlwaysInlineFunctions.begin(), ArgE = AlwaysInlineFunctions.end(); ArgI != ArgE; ++ArgI) {

    Function* AlwaysF = F.getParent()->getFunction(*ArgI);
    if(!AlwaysF) {
      errs() << "No such function " << *ArgI << "\n";
      exit(1);
    }
    alwaysInline.insert(AlwaysF);

  }

  for(cl::list<std::string>::const_iterator ArgI = AlwaysExploreFunctions.begin(), ArgE = AlwaysExploreFunctions.end(); ArgI != ArgE; ++ArgI) {

    Function* AlwaysF = F.getParent()->getFunction(*ArgI);
    if(!AlwaysF) {
      errs() << "No such function " << *ArgI << "\n";
      exit(1);
    }
    alwaysExplore.insert(AlwaysF);

  }

  for(cl::list<std::string>::const_iterator ArgI = OptimisticLoops.begin(), ArgE = OptimisticLoops.end(); ArgI != ArgE; ++ArgI) {

    Function* LoopF;
    BasicBlock *BB1, *BB2;

    parseFBB("llpe-optimistic-loop", *ArgI, *(F.getParent()), LoopF, BB1, BB2);

    optimisticLoopMap[std::make_pair(LoopF, BB1)] = BB2;

  }

  for(cl::list<std::string>::const_iterator ArgI = AlwaysIterLoops.begin(), ArgE = AlwaysIterLoops.end(); ArgI != ArgE; ++ArgI) {

    Function* LoopF;
    BasicBlock *HBB;

    parseFB("llpe-always-iterate", *ArgI, *(F.getParent()), LoopF, HBB);
    
    alwaysIterLoops[LoopF].insert(HBB);

  }

  for(cl::list<std::string>::const_iterator ArgI = AssumeEdges.begin(), ArgE = AssumeEdges.end(); ArgI != ArgE; ++ArgI) {

    Function* AssF;
    BasicBlock *BB1, *BB2;
    
    parseFBB("llpe-assume-edge", *ArgI, *(F.getParent()), AssF, BB1, BB2);

    assumeEdges[AssF].insert(std::make_pair(BB1, BB2));

  }

  for(cl::list<std::string>::const_iterator ArgI = IgnoreLoops.begin(), ArgE = IgnoreLoops.end(); ArgI != ArgE; ++ArgI) {

    Function* LF;
    BasicBlock* HBB;

    parseFB("llpe-ignore-loop", *ArgI, *(F.getParent()), LF, HBB);

    ignoreLoops[LF].insert(HBB);

  }

  for(cl::list<std::string>::const_iterator ArgI = IgnoreLoopsWithChildren.begin(), ArgE = IgnoreLoopsWithChildren.end(); ArgI != ArgE; ++ArgI) {

    Function* LF;
    BasicBlock* HBB;

    parseFB("llpe-ignore-loop", *ArgI, *(F.getParent()), LF, HBB);

    ignoreLoopsWithChildren[LF].insert(HBB);

  }

  for(cl::list<std::string>::const_iterator ArgI = LoopMaxIters.begin(), ArgE = LoopMaxIters.end(); ArgI != ArgE; ++ArgI) {

    Function* LF;
    BasicBlock* HBB;
    uint64_t Count;
    
    parseFBI("llpe-loop-max", *ArgI, *(F.getParent()), LF, HBB, Count);

    maxLoopIters[std::make_pair(LF, HBB)] = Count;

  }

  for(cl::list<std::string>::const_iterator ArgI = SpecialLocations.begin(), ArgE = SpecialLocations.end(); ArgI != ArgE; ++ArgI) {

    std::istringstream istr(*ArgI);
    std::string fName, sizeStr;
    std::getline(istr, fName, ',');
    std::getline(istr, sizeStr, ',');

    if(fName.empty() || sizeStr.empty()) {

      errs() << "-llpe-special-location must have form function_name,size\n";
      exit(1);

    }

    Function* SpecF = F.getParent()->getFunction(fName);
    if(!SpecF) {

      errs() << "-llpe-special-location: no such function " << fName << "\n";
      exit(1);

    }

    int64_t size = getInteger(sizeStr, "-llpe-special-location size");
    SpecialLocationDescriptor& sd = specialLocations[SpecF];
    sd.storeSize = (uint64_t)size;
    ImprovedValSetSingle* Init = new ImprovedValSetSingle(ValSetTypeScalar);
    Init->setOverdef();
    sd.store.store = Init;
   
  }

  for(cl::list<std::string>::const_iterator ArgI = ModelFunctions.begin(), ArgE = ModelFunctions.end(); ArgI != ArgE; ++ArgI) {

    std::istringstream istr(*ArgI);
    std::string realFName, modelFName;
    std::getline(istr, realFName, ',');
    std::getline(istr, modelFName, ',');

    if(modelFName.empty() || realFName.empty()) {

      errs() << "-llpe-model-function must have form original_name,new_name";
      exit(1);

    }

    Function* realF = F.getParent()->getFunction(realFName);
    Function* modelF = F.getParent()->getFunction(modelFName);
    if((!realF) || !modelF) {

      errs() << "-llpe-model-function: no such function " << realFName << " or " << modelFName << "\n";
      exit(1);

    }

    modelFunctions[realF] = modelF;

  }

  for(cl::list<std::string>::const_iterator ArgI = YieldFunctions.begin(), ArgE = YieldFunctions.end(); ArgI != ArgE; ++ArgI) {

    Function* YieldF = F.getParent()->getFunction(*ArgI);
    if(!YieldF) {

      errs() << "-llpe-yield-function: no such function " << *ArgI << "\n";
      exit(1);

    }
    yieldFunctions.insert(YieldF);

  }

  for(cl::list<std::string>::iterator it = TargetStack.begin(), 
	itend = TargetStack.end(); it != itend; ++it) {
    
    std::string& thisCall = *it;
    
    std::string fName, bbName, instIdxStr;

    std::istringstream istr(thisCall);
    std::getline(istr, fName, ',');
    std::getline(istr, bbName, ',');
    std::getline(istr, instIdxStr, ',');

    if(fName.empty() || bbName.empty() || instIdxStr.empty()) {
      errs() << "llpe-target-stack must have form functionName,blockName,index\n";
      exit(1);
    }

    Function* StackF = F.getParent()->getFunction(fName);
    if(!StackF) {
      errs() << "Bad function in llpe-target-stack\n";
      exit(1);
    }

    BasicBlock* BB = findBlockRaw(StackF, bbName);
    uint32_t instIdx = (uint32_t)getInteger(instIdxStr, "llpe-target-stack instruction index");

    if(instIdx >= BB->size()) {
      errs() << "llpe-target-stack: call instruction index out of range\n";
      exit(1);
    }

    BasicBlock::iterator TestBI = BB->begin();
    std::advance(TestBI, instIdx);
    if((!isa<CallInst>(TestBI)) && (!isa<InvokeInst>(TestBI))) {
      errs() << "llpe-target-stack: index does not refer to a call or invoke\n";
      exit(1);
    }
    
    targetCallStack.push_back(std::make_pair(BB, instIdx));
    
  }

  for(cl::list<std::string>::iterator it = SimpleVolatiles.begin(),
	itend = SimpleVolatiles.end(); it != itend; ++it) {

    Function* LoadF;
    BasicBlock* BB;
    uint64_t Offset;

    parseFBI("llpe-simple-volatile-load", *it, *(F.getParent()), LoadF, BB, Offset);

    BasicBlock::iterator BI = BB->begin();
    std::advance(BI, Offset);

    if(!(isa<LoadInst>(BI) || isa<AtomicRMWInst>(BI) || isa<AtomicCmpXchgInst>(BI))) {
      errs() << "llpe-simple-volatile-load: " << *it << " does not denote an atomic op\n";
      exit(1);
    }

    simpleVolatileLoads.insert(&*BI);

  }

  for(cl::list<std::string>::iterator it = LockDomains.begin(),
	itend = LockDomains.end(); it != itend; ++it) {

    Function* LockF;
    BasicBlock* BB;
    uint64_t Offset;

    // TODO here: add a better specification of lock domain than just a list of globals!

    size_t pos = 0;
    for(uint32_t i = 0; i < 3; ++i) {

      pos = it->find(',', pos);
      if(pos == std::string::npos) {
	errs() << "llpe-lock-domain: usage: lockf,lockblock,lockoffset,global1,...,globaln\n";
	exit(1);
      }
      ++pos;

    }

    std::string FBI(*it, 0, pos - 1);

    parseFBI("llpe-lock-domain", FBI, *(F.getParent()), LockF, BB, Offset);
    BasicBlock::iterator BI = BB->begin();
    std::advance(BI, Offset);
    CallInst* CI = dyn_cast<CallInst>(BI);
    
    if(!CI) {
      errs() << "llpe-lock-domain: " << *it << " does not denote a call\n";
      exit(1);
    }

    std::vector<GlobalVariable*>& thisDomain = lockDomains[CI];

    std::string globals(*it, pos);

    std::istringstream istr(globals);
    while(!istr.eof()) {
      
      std::string thisGlobal;
      std::getline(istr, thisGlobal, ',');
      if(thisGlobal.empty())
	continue;
      GlobalVariable* GV = F.getParent()->getGlobalVariable(thisGlobal, true);
      if(!GV) {

	errs() << "Global not found: " << thisGlobal << "\n";
	exit(1);

      }
      thisDomain.push_back(GV);

    }

  }

  for(cl::list<std::string>::iterator it = PessimisticLocks.begin(),
	itend = PessimisticLocks.end(); it != itend; ++it) {

    Function* LockF;
    BasicBlock* BB;
    uint64_t Offset;

    parseFBI("llpe-pessimistic-lock", *it, *(F.getParent()), LockF, BB, Offset);
    BasicBlock::iterator BI = BB->begin();
    std::advance(BI, Offset);
    CallInst* CI = dyn_cast<CallInst>(BI);
    
    if(!CI) {
      errs() << "llpe-pessimistic-lock: " << *it << " does not denote a call\n";
      exit(1);
    }

    pessimisticLocks.insert(CI);

  }
  
  for(cl::list<std::string>::iterator it = ForceNoAliasArgs.begin(),
	itend = ForceNoAliasArgs.end(); it != itend; ++it) {

    uint32_t argIdx = (uint32_t)getInteger(*it, "llpe-force-noalias-arg parameter");
    forceNoAliasArgs.insert(argIdx);
    
  }

  for(cl::list<std::string>::iterator it = VarAllocators.begin(),
	itend = VarAllocators.end(); it != itend; ++it) {

    std::string fName, idxStr, freeName, freeIdxStr;

    std::istringstream istr(*it);
    std::getline(istr, fName, ',');
    std::getline(istr, idxStr, ',');
    std::getline(istr, freeName, ',');
    std::getline(istr, freeIdxStr, ',');

    Function* allocF = F.getParent()->getFunction(fName);
    if(!allocF) {

      errs() << "-llpe-allocator-fn: must specify a function\n";
      exit(1);

    }

    uint32_t sizeParam = getInteger(idxStr, "llpe-allocator-fn second param");

    allocatorFunctions[allocF] = AllocatorFn::getVariableSize(sizeParam);
    SpecialFunctionMap[allocF] = SF_MALLOC;

    if(!freeName.empty()) {

      Function* freeF = F.getParent()->getFunction(freeName);
      if(!freeF) {

	errs() << "-llpe-allocator-fn: bad release function " << freeName << "\n";
	exit(1);

      }
      
      uint32_t releaseArg = getInteger(freeIdxStr, "llpe-allocator-fn fourth param");
      deallocatorFunctions[freeF] = DeallocatorFn(releaseArg);
      SpecialFunctionMap[freeF] = SF_FREE;

    }

  }

  for(cl::list<std::string>::iterator it = ConstAllocators.begin(),
	itend = ConstAllocators.end(); it != itend; ++it) {

    std::string fName, sizeStr, freeName, freeIdxStr, reallocName, reallocPtrIdxStr, reallocSizeIdxStr;

    std::istringstream istr(*it);
    std::getline(istr, fName, ',');
    std::getline(istr, sizeStr, ',');
    std::getline(istr, freeName, ',');
    std::getline(istr, freeIdxStr, ',');
    std::getline(istr, reallocName, ',');
    std::getline(istr, reallocPtrIdxStr, ',');
    std::getline(istr, reallocSizeIdxStr, ',');


    Function* allocF = F.getParent()->getFunction(fName);
    if(!allocF) {

      errs() << "-llpe-allocator-fn-const: must specify a function\n";
      exit(1);

    }

    uint32_t size = getInteger(sizeStr, "llpe-allocator-fn-const second param");

    IntegerType* I32 = Type::getInt32Ty(F.getContext());

    allocatorFunctions[allocF] = AllocatorFn::getConstantSize(ConstantInt::get(I32, size));
    SpecialFunctionMap[allocF] = SF_MALLOC;

    if(!freeName.empty()) {

      Function* freeF = F.getParent()->getFunction(freeName);
      if(!freeF) {

	errs() << "-llpe-allocator-fn: bad release function " << freeName << "\n";
	exit(1);

      }

      uint32_t releaseArg = getInteger(freeIdxStr, "llpe-allocator-fn fourth param");
      deallocatorFunctions[freeF] = DeallocatorFn(releaseArg);
      SpecialFunctionMap[freeF] = SF_FREE;

    }

    if(!reallocName.empty()) {

      Function* reallocF = F.getParent()->getFunction(reallocName);
      if(!reallocF) {

	errs() << "-llpe-allocator-fn: bad realloc function " << reallocName << "\n";
	exit(1);

      }

      uint32_t reallocPtrIdx = getInteger(reallocPtrIdxStr, "llpe-allocator-fn sixth param");
      uint32_t reallocSizeIdx = getInteger(reallocPtrIdxStr, "llpe-allocator-fn seventh param");
      reallocatorFunctions[reallocF] = ReallocatorFn(reallocPtrIdx, reallocSizeIdx);
      SpecialFunctionMap[reallocF] = SF_REALLOC;

    }

  }

  for(cl::list<std::string>::iterator it = NeverInline.begin(), itend = NeverInline.end(); it != itend; ++it) {

    Function* IgnoreF = F.getParent()->getFunction(*it);
    if(!IgnoreF) {

      errs() << "llpe-never-inline: no such function " << *it << "\n";
      exit(1);

    }

    blacklistedFunctions.insert(IgnoreF);

  }

  for(cl::list<std::string>::iterator it = SplitFunctions.begin(), itend = SplitFunctions.end(); it != itend; ++it) {

    Function* SplitF = F.getParent()->getFunction(*it);
    if(!SplitF) {

      errs() << "llpe-force-split: no such function " << *it << "\n";
      exit(1);

    }

    splitFunctions.insert(SplitF);

  }

  if(Function* libcMalloc = F.getParent()->getFunction("malloc"))
    allocatorFunctions[libcMalloc] = AllocatorFn::getVariableSize(0);
  if(Function* libcFree = F.getParent()->getFunction("free"))
    deallocatorFunctions[libcFree] = DeallocatorFn(0);
  if(Function* libcRealloc = F.getParent()->getFunction("realloc")) {
    deallocatorFunctions[libcRealloc] = DeallocatorFn(0);
    reallocatorFunctions[libcRealloc] = ReallocatorFn(0, 1);
  }

  this->verboseOverdef = VerboseOverdef;
  this->enableSharing = EnableFunctionSharing;
  this->verboseSharing = VerboseFunctionSharing;
  this->verbosePCs = VerbosePathConditions;
  this->programSingleThreaded = SingleThreaded;
  this->useGlobalInitialisers = UseGlobalInitialisers;
  this->omitChecks = OmitChecks;
  this->omitMallocChecks = OmitMallocChecks;
  if(this->omitChecks && !this->programSingleThreaded) {

    errs() << "omit-checks currently requires single-threaded\n";
    exit(1);

  }

  if(LLIOPreludeStackIdx != -1) {

    this->llioPreludeStackIdx = LLIOPreludeStackIdx;
    this->llioPreludeFn = 0;

  }
  else {

    this->llioPreludeStackIdx = -1;    
    if(Function* preludeFn = F.getParent()->getFunction(LLIOPreludeFn))
      this->llioPreludeFn = preludeFn;
    else
      this->llioPreludeFn = &F;

  }

  this->llioConfigFile = LLIOConfFile;
  this->emitFakeDebug = EmitFakeDebug;

  if(this->emitFakeDebug) {
    DIBuilder DIB(*F.getParent());
    DIFile* file = DIB.createFile("llpe.file", "/nonesuch");
    DIB.createCompileUnit(dwarf::DW_LANG_C89, file, "LLPE", true, "", 0);
    DIBasicType* retType = DIB.createBasicType("fakechar", 8, dwarf::DW_ATE_signed);
    DITypeRefArray functionParamTypes = DIB.getOrCreateTypeArray(ArrayRef<Metadata*>((Metadata*)retType));
    this->fakeDebugType = DIB.createSubroutineType(functionParamTypes);
  }

}

void LLPEAnalysisPass::parseArgsPostCreation(InlineAttempt* IA) {

  for(cl::list<std::string>::iterator it = IgnoreBlocks.begin(), itend = IgnoreBlocks.end();
      it != itend; ++it) {

    std::string fName;
    std::string bbName;
    {
      std::istringstream istr(*it);
      std::getline(istr, fName, ',');
      std::getline(istr, bbName, ',');
    }

    if(fName != IA->F.getName()) {

      errs() << "llpe-ignore-block currently only supported in the root function\n";
      exit(1);

    }

    IA->addIgnoredBlock(bbName);

  }

  parsePathConditions(PathConditionsInt, PathConditionTypeInt, IA);
  parsePathConditions(PathConditionsFptr, PathConditionTypeFptr, IA);
  parsePathConditions(PathConditionsString, PathConditionTypeString, IA);
  parsePathConditions(PathConditionsIntmem, PathConditionTypeIntmem, IA);  
  parsePathConditions(PathConditionsFptrmem, PathConditionTypeFptrmem, IA);
  parsePathConditions(PathConditionsStream, PathConditionTypeStream, IA);
  parsePathConditions(PathConditionsGlobalInit, PathConditionTypeGlobalInit, IA);

  for(cl::list<std::string>::iterator it = PathConditionsFunc.begin(), 
	itend = PathConditionsFunc.end(); it != itend; ++it) {

    std::string fStackIdxStr;
    std::string bbName;
    std::string calledName;
    std::string verifyName;
    std::istringstream istr(*it);

    {
      std::getline(istr, fStackIdxStr, ',');
      std::getline(istr, bbName, ',');
      std::getline(istr, calledName, ',');
      std::getline(istr, verifyName, ',');
    }

    if(fStackIdxStr.empty() || bbName.empty() || calledName.empty() || verifyName.empty()) {

      errs() << "-llpe-path-condition-func usage: context-function,context-block,path-function,verify-function" << "\n";
      exit(1);

    }

    int64_t fStackIdx;
    Function* callerFunction;

    if(tryGetInteger(fStackIdxStr, fStackIdx)) {

      if(fStackIdx >= (int64_t)targetCallStack.size()) {
	errs() << "Bad stack index for path function\n";
	exit(1);
      }

      callerFunction = targetCallStack[fStackIdx].first->getParent();

    }
    else {

      callerFunction = IA->F.getParent()->getFunction(fStackIdxStr);
      if(!callerFunction) {

	errs() << "No such function " << fStackIdxStr << "\n";
	exit(1);

      }

      fStackIdx = UINT_MAX;

    }
    
    BasicBlock* assumeBlock = findBlockRaw(callerFunction, bbName);
    Function* CallF = IA->F.getParent()->getFunction(calledName);
    Function* VerifyF = IA->F.getParent()->getFunction(verifyName);

    if(!CallF) {
      
      errs() << "No such function " << calledName << "\n";
      exit(1);

    }
    
    if(!VerifyF) {

      errs() << "No such function " << verifyName << "\n";
      exit(1);

    }

    if(!VerifyF->getFunctionType()->getReturnType()->isIntegerTy()) {

      errs() << "Verification functions must return an integer\n";
      exit(1);

    }

    FunctionType* FType = CallF->getFunctionType();
    PathConditions* PC;

    if(fStackIdx == UINT_MAX) {

      ShadowFunctionInvar* SFI = getFunctionInvarInfo(*callerFunction);
      if(!SFI->pathConditions)
	SFI->pathConditions = new PathConditions();
      PC = SFI->pathConditions;

    }
    else {

      PC = &pathConditions;

    }

    PC->FuncPathConditions.push_back(PathFunc(fStackIdx, assumeBlock, CallF, VerifyF));
    PathFunc& newFunc = PC->FuncPathConditions.back();

    while(!istr.eof()) {

      std::string argStackIdxStr;
      std::string argBBStr;
      std::string argIdxStr;
      std::getline(istr, argStackIdxStr, ',');
      std::getline(istr, argBBStr, ',');
      std::getline(istr, argIdxStr, ',');

      uint32_t argStackIdx;
      Function* fStack;

      if(fStackIdx == UINT_MAX) {

	if(argStackIdxStr != fStackIdxStr) {

	  errs() << "Non-stack path functions can only use local arguments\n";
	  exit(1);

	}

	argStackIdx = UINT_MAX;
	fStack = callerFunction;

      }
      else {

	argStackIdx = getInteger(argStackIdxStr, "Path function argument stack index");
	fStack = targetCallStack[argStackIdx].first->getParent();

      }

      BasicBlock* argBB = parsePCBlock(fStack, argBBStr);
      int64_t argInstIdx = parsePCInst(argBB, IA->F.getParent(), argIdxStr);
      newFunc.args.push_back(PathFuncArg(argStackIdx, argBB, argInstIdx));

    }

    release_assert(FType->getNumParams() == newFunc.args.size() && "Path function with wrong arg count");
  
  }

}

// Cheeky export for TopLevel.cpp's consumption:
namespace llvm {
  size_t getStringPathConditionCount() {
    return PathConditionsString.size();
  }
}
