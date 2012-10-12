
#include <llvm/Analysis/VFSCallModRef.h>

#include <llvm/Function.h>

#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/LibCallSemantics.h>
#include <llvm/Analysis/HypotheticalConstantFolder.h>

// For TCGETS et al
#include <termios.h>
#include <sys/ioctl.h>

using namespace llvm;

// Two locations:
// 1. errno, modelled here as __errno_location, which is likely to be pretty brittle.
// 2. an abstract location representing the buffer that's passed to a read call.

static LibCallLocationInfo::LocResult isErrnoForLocation(ImmutableCallSite CS, const Value* Ptr, unsigned Size, IntegrationAttempt* CSCtx, IntegrationAttempt* PtrCtx) {

  if(CSCtx && CSCtx->isSuccessfulVFSCall(CS.getInstruction())) {

    // Resolved VFS calls definitely do not write to errno, so ignore any potential alias.
    return LibCallLocationInfo::No;

  }

  // Try to identify errno: if it's a call to __errno_location(), it is. If it's a resolved object of any kind,
  // it isn't.

  if(const CallInst* CI = dyn_cast<CallInst>(Ptr)) {
  
    if(Function* F = CI->getCalledFunction()) {

      if(F && F->getName() == "__errno_location") {
	return LibCallLocationInfo::Yes;
      }

    }

  }

  ValCtx VC = PtrCtx->getUltimateUnderlyingObject(const_cast<Value*>(Ptr));

  if(isIdentifiedObject(VC.first))
    return LibCallLocationInfo::No;

  return LibCallLocationInfo::Unknown;

}

static LibCallLocationInfo::LocResult aliasCheckAsLCI(const Value* Ptr1, IntegrationAttempt* Ptr1C, uint64_t Ptr1Size, const Value* Ptr2, IntegrationAttempt* Ptr2C, uint64_t Ptr2Size) {

  AliasAnalysis::AliasResult AR = Ptr1C->getAA()->aliasHypothetical(make_vc(const_cast<Value*>(Ptr1), Ptr1C), Ptr1Size, make_vc(const_cast<Value*>(Ptr2), Ptr2C), Ptr2Size);

  switch(AR) {
  case AliasAnalysis::MustAlias:
    return LibCallLocationInfo::Yes;
  case AliasAnalysis::NoAlias:
    return LibCallLocationInfo::No;
  default:
    return LibCallLocationInfo::Unknown;
  }

}

static LibCallLocationInfo::LocResult isReadBuf(ImmutableCallSite CS, const Value* Ptr, unsigned Size, IntegrationAttempt* CSCtx, IntegrationAttempt* PCtx) {

  ConstantInt* ReadSize = cast_or_null<ConstantInt>(CSCtx->getConstReplacement(const_cast<Value*>(CS.getArgument(2))));

  return aliasCheckAsLCI(Ptr, PCtx, Size, CS.getArgument(1), CSCtx, ReadSize ? ReadSize->getLimitedValue() : AliasAnalysis::UnknownSize);

}

static LibCallLocationInfo::LocResult isArg0(ImmutableCallSite CS, const Value* Ptr, unsigned Size, IntegrationAttempt* CSCtx, IntegrationAttempt* PCtx) {

  return aliasCheckAsLCI(Ptr, PCtx, Size, CS.getArgument(0), CSCtx, AliasAnalysis::UnknownSize);
  
}

static LibCallLocationInfo::LocResult isArg1(ImmutableCallSite CS, const Value* Ptr, unsigned Size, IntegrationAttempt* CSCtx, IntegrationAttempt* PCtx) {

  return aliasCheckAsLCI(Ptr, PCtx, Size, CS.getArgument(1), CSCtx, AliasAnalysis::UnknownSize);
  
}

static LibCallLocationInfo::LocResult isReturnVal(ImmutableCallSite CS, const Value* Ptr, unsigned Size, IntegrationAttempt* CSCtx, IntegrationAttempt* PCtx) {

  return aliasCheckAsLCI(Ptr, PCtx, Size, CS.getInstruction(), CSCtx, AliasAnalysis::UnknownSize);
  
}

static LibCallLocationInfo::LocResult isTermios(ImmutableCallSite CS, const Value* Ptr, unsigned Size, IntegrationAttempt* CSCtx, IntegrationAttempt* PCtx) {

  return aliasCheckAsLCI(Ptr, PCtx, Size, CS.getArgument(2), CSCtx, sizeof(struct termios));

}

static LibCallLocationInfo VFSCallLocations[] = {
  { isErrnoForLocation },
  { isReadBuf },
  { isArg0 },
  { isTermios },
  { isReturnVal },
  { isArg1 }
};

unsigned VFSCallModRef::getLocationInfo(const LibCallLocationInfo *&Array) const {

  Array = VFSCallLocations;
  return 6;
    
}
  
static LibCallFunctionInfo::LocationMRInfo JustErrno[] = {
  { 0, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo ReadMR[] = {
  { 0, AliasAnalysis::Mod },
  { 1, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo FreeMR[] = {
  { 2, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo ReallocMR[] = {
  { 2, AliasAnalysis::Mod },
  { 4, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo MallocMR[] = {
  { 4, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo TCGETSMR[] = {
  { 0, AliasAnalysis::Mod },
  { 3, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo GettimeMR[] = {
  { 0, AliasAnalysis::Mod },
  { 5, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo GettimeofdayMR[] = {
  { 0, AliasAnalysis::Mod },
  { 2, AliasAnalysis::Mod },
  { 5, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static const LibCallFunctionInfo::LocationMRInfo* getIoctlLocDetails(ImmutableCallSite CS, IntegrationAttempt* Ctx) {

  if(ConstantInt* C = cast_or_null<ConstantInt>(Ctx->getConstReplacement(const_cast<Value*>(CS.getArgument(1))))) {

    switch(C->getLimitedValue()) {
    case TCGETS:
      return TCGETSMR;
    }

  }

  return 0;

}

static LibCallFunctionInfo VFSCallFunctions[] = {

  { "open", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "read", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, ReadMR, 0 },
  { "lseek", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "llseek", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "lseek64", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "close", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "free", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, FreeMR, 0 },
  { "malloc", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, MallocMR, 0 },
  { "realloc", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, ReallocMR, 0 },
  { "ioctl", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, 0, getIoctlLocDetails },
  { "clock_gettime", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, GettimeMR, 0 },
  { "gettimeofday", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, GettimeofdayMR, 0 },
  // Terminator
  { 0, AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, 0, 0 }

};

/// getFunctionInfoArray - Return an array of descriptors that describe the
/// set of libcalls represented by this LibCallInfo object.  This array is
/// terminated by an entry with a NULL name.
const LibCallFunctionInfo* VFSCallModRef::getFunctionInfoArray() const {

  return VFSCallFunctions;

}

ModulePass *createVFSCallAliasAnalysisPass() {

  return new VFSCallAliasAnalysis();

}

// Register this pass...
char VFSCallAliasAnalysis::ID = 0;
INITIALIZE_AG_PASS(VFSCallAliasAnalysis, AliasAnalysis, "vfscall-aa",
                   "VFS Call Alias Analysis", false, true, false);

