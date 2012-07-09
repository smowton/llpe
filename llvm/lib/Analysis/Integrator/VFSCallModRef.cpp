
#include <llvm/Analysis/VFSCallModRef.h>

#include <llvm/Function.h>

#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/LibCallSemantics.h>
#include <llvm/Analysis/HypotheticalConstantFolder.h>

using namespace llvm;

// Two locations:
// 1. errno, modelled here as __errno_location, which is likely to be pretty brittle.
// 2. an abstract location representing the buffer that's passed to a read call.

static LibCallLocationInfo::LocResult isErrnoForLocation(ImmutableCallSite CS, const Value* Ptr, unsigned Size, HCFParentCallbacks* Ctx) {

  if(Ctx && Ctx->isResolvedVFSCall(CS.getInstruction())) {

    // Resolved VFS calls definitely do not write to errno, so ignore any potential alias.
    return LibCallLocationInfo::No;

  }

  // Try to identify errno: if it's a call to __errno_location(), it is. If it's a resolved object of any kind,
  // it isn't.

  if(const CallInst* CI = dyn_cast<CallInst>(Ptr)) {
  
    if(Function* F = CI->getCalledFunction()) {

      if(F->getName() == "__errno_location") {
	return LibCallLocationInfo::Yes;
      }

    }

  }

  ValCtx VC = Ctx->getUltimateUnderlyingObject(const_cast<Value*>(Ptr));

  if(isIdentifiedObject(VC.first))
    return LibCallLocationInfo::No;

  return LibCallLocationInfo::Unknown;

}

static LibCallLocationInfo::LocResult isReadBuf(ImmutableCallSite CS, const Value* Ptr, unsigned Size, HCFParentCallbacks* Ctx) {

  ConstantInt* ReadSize = cast_or_null<ConstantInt>(Ctx->getConstReplacement(const_cast<Value*>(CS.getArgument(2))));

  AliasAnalysis::AliasResult AR = Ctx->getAA()->aliasHypothetical(Ptr, Size, CS.getArgument(1), ReadSize ? ReadSize->getLimitedValue() : AliasAnalysis::UnknownSize, Ctx);

  switch(AR) {
  case AliasAnalysis::MustAlias:
    return LibCallLocationInfo::Yes;
  case AliasAnalysis::NoAlias:
    return LibCallLocationInfo::No;
  default:
    return LibCallLocationInfo::Unknown;
  }

}

static LibCallLocationInfo VFSCallLocations[] = {
  { isErrnoForLocation },
  { isReadBuf }
};

unsigned VFSCallModRef::getLocationInfo(const LibCallLocationInfo *&Array) const {

  Array = VFSCallLocations;
  return 2;
    
}
  
static LibCallFunctionInfo::LocationMRInfo OpenMR[] = {
  { 0, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo ReadMR[] = {
  { 0, AliasAnalysis::Mod },
  { 1, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo VFSCallFunctions[] = {

  { "open", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, OpenMR },
  { "read", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, ReadMR }

};
  
/// getFunctionInfoArray - Return an array of descriptors that describe the
/// set of libcalls represented by this LibCallInfo object.  This array is
/// terminated by an entry with a NULL name.
const LibCallFunctionInfo* VFSCallModRef::getFunctionInfoArray() const {

  return VFSCallFunctions;

}

FunctionPass *createVFSCallAliasAnalysisPass() {

  return new VFSCallAliasAnalysis();

}

// Register this pass...
char VFSCallAliasAnalysis::ID = 0;
INITIALIZE_AG_PASS(VFSCallAliasAnalysis, AliasAnalysis, "vfscall-aa",
                   "VFS Call Alias Analysis", false, true, false);

