
#include <llvm/Analysis/VFSCallModRef.h>

#include <llvm/Module.h>
#include <llvm/Function.h>
#include <llvm/Constants.h>

#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/LibCallSemantics.h>
#include <llvm/Analysis/HypotheticalConstantFolder.h>

// For TCGETS et al
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <poll.h>

using namespace llvm;

// Two locations:
// 1. errno, modelled here as __errno_location, which is likely to be pretty brittle.
// 2. an abstract location representing the buffer that's passed to a read call.

static LibCallLocationInfo::LocResult isErrnoForLocation(ShadowValue CS, ShadowValue P, unsigned Size, bool usePBKnowledge, int64_t Ptr1Offset, IntAAProxy* AACB) {

  if(CS.getCtx() && CS.getCtx()->isSuccessfulVFSCall(CS.getInst()->invar->I)) {

    // Resolved VFS calls definitely do not write to errno, so ignore any potential alias.
    return LibCallLocationInfo::No;

  }

  // Try to identify errno: if it's a call to __errno_location(), it is. If it's a resolved object of any kind,
  // it isn't.

  if(const CallInst* CI = dyn_cast_val<CallInst>(P)) {
  
    if(Function* F = CI->getCalledFunction()) {

      if(F && F->getName() == "__errno_location") {
	return LibCallLocationInfo::Yes;
      }

    }

  }

  ShadowValue Base;
  int64_t Offset;
  if(Ptr1Offset != LLONG_MAX || getBaseAndOffset(P, Base, Offset))
    return LibCallLocationInfo::No;
  
  return LibCallLocationInfo::Unknown;

}

static LibCallLocationInfo::LocResult aliasCheckAsLCI(ShadowValue Ptr1, uint64_t Ptr1Size, ShadowValue Ptr2, uint64_t Ptr2Size, bool usePBKnowledge, int64_t Ptr1Offset, IntAAProxy* AACB) {

  SVAAResult AR;
  if(Ptr1Offset != LLONG_MAX)
    AR = tryResolvePointerBases(Ptr1, Ptr1Offset, Ptr1Size, Ptr2, Ptr2Size, true);
  else
    AR = aliasSVs(Ptr1, Ptr1Size, Ptr2, Ptr2Size, usePBKnowledge);

  switch(AR) {
  case SVMustAlias:
    return LibCallLocationInfo::Yes;
  case SVNoAlias:
    return LibCallLocationInfo::No;
  default:
    return LibCallLocationInfo::Unknown;
  }

}

static LibCallLocationInfo::LocResult isReadBuf(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  ConstantInt* ReadSize = cast_or_null<ConstantInt>(getConstReplacement(getValArgOperand(CS, 2)));

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 1), ReadSize ? ReadSize->getLimitedValue() : AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);

}

static LibCallLocationInfo::LocResult isArg0(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 0), AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isArg0Size24(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 0), 24, usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isPollFds(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  ConstantInt* nFDs = cast_or_null<ConstantInt>(getConstReplacement(getValArgOperand(CS, 1)));
  uint64_t fdArraySize = nFDs ? (nFDs->getLimitedValue() * sizeof(struct pollfd)) : AliasAnalysis::UnknownSize;

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 0), fdArraySize, usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isArg1(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 1), AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isArg2(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 2), AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isArg2SockLen(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 2), sizeof(socklen_t), usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isArg3(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 3), AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isReturnVal(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, CS, AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);
  
}

static LibCallLocationInfo::LocResult isTermios(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  return aliasCheckAsLCI(Ptr, Size, getValArgOperand(CS, 2), sizeof(struct termios), usePBKnowledge, POffset, AACB);

}

static LibCallLocationInfo::LocResult isStdOut(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  Module& M = CS.getCtx()->getModule();
  GlobalVariable* Stdout = M.getNamedGlobal("_stdio_streams");
  assert(Stdout);
  return aliasCheckAsLCI(Ptr, Size, Stdout, AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);

}

static LibCallLocationInfo::LocResult isStdErr(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  Module& M = CS.getCtx()->getModule();
  GlobalVariable* Stderr = M.getNamedGlobal("_stdio_streams");
  assert(Stderr);
  return aliasCheckAsLCI(Ptr, Size, Stderr, AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);

}

static LibCallLocationInfo::LocResult isStdBufs(ShadowValue CS, ShadowValue Ptr, unsigned Size, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  Module& M = CS.getCtx()->getModule();
  GlobalVariable* Stdbufs = M.getNamedGlobal("_fixed_buffers");
  assert(Stdbufs);
  return aliasCheckAsLCI(Ptr, Size, Stdbufs, AliasAnalysis::UnknownSize, usePBKnowledge, POffset, AACB);

}

static LibCallLocationInfo VFSCallLocations[] = {
  { isErrnoForLocation },
  { isReadBuf },
  { isArg0 },
  { isTermios },
  { isReturnVal },
  { isArg1 },
  { isArg2 },
  { isArg3 },
  { isArg0Size24 },
  { isStdOut },
  { isStdErr },
  { isStdBufs },
  { isArg2SockLen },
  { isPollFds },
};

unsigned VFSCallModRef::getLocationInfo(const LibCallLocationInfo *&Array) const {

  Array = VFSCallLocations;
  return 14;
    
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

static LibCallFunctionInfo::LocationMRInfo TimeMR[] = {
  { 0, AliasAnalysis::Mod },
  { 2, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo LocaltimeTZIMR[] = {
  { 2, AliasAnalysis::Ref },
  { 5, AliasAnalysis::Mod },
  { 6, AliasAnalysis::Ref },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo FwriteMR[] = {
  { 0, AliasAnalysis::Mod },
  { 2, AliasAnalysis::Ref },
  { 7, AliasAnalysis::Mod },
  { 11, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo MemsetByteMR[] = {
  { 0, AliasAnalysis::Mod },
  { 2, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo LanginfoLMR[] = {

  { 5, AliasAnalysis::Ref },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo LanginfoMR[] = {

  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo VAStartMR[] = {

  { 8, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo VACopyMR[] = {

  { 8, AliasAnalysis::Mod },
  { 5, AliasAnalysis::Ref },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo ErrorMR[] = {

  { 9, AliasAnalysis::Mod },
  { 10, AliasAnalysis::Mod },
  { 11, AliasAnalysis::Mod },
  { 0, AliasAnalysis::Mod },
  { 2, AliasAnalysis::Ref },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo StrToLMR[] = {

  { 5, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo FerrorMR[] = {

  { 2, AliasAnalysis::Ref },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo WriteMR[] = {

  { 5, AliasAnalysis::Ref },
  { 0, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo StatMR[] = {

  { 0, AliasAnalysis::Mod },
  { 2, AliasAnalysis::Ref },
  { 5, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo SigactionMR[] = {

  { 0, AliasAnalysis::Mod },
  { 5, AliasAnalysis::Ref },
  { 6, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo AcceptMR[] = {

  { 0, AliasAnalysis::Mod },
  { 5, AliasAnalysis::Mod },
  { 12, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo PollMR[] = {

  { 0, AliasAnalysis::Mod },
  { 13, AliasAnalysis::Mod },
  { ~0U, AliasAnalysis::ModRef }

};

static const LibCallFunctionInfo::LocationMRInfo* getIoctlLocDetails(ShadowValue CS) {

  if(ConstantInt* C = cast_or_null<ConstantInt>(getConstReplacement(getValArgOperand(CS, 1)))) {

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
  { "free", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "malloc", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, MallocMR, 0 },
  { "realloc", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, ReallocMR, 0 },
  { "ioctl", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, 0, getIoctlLocDetails },
  { "clock_gettime", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, GettimeMR, 0 },
  { "gettimeofday", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, GettimeofdayMR, 0 },
  { "time", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, TimeMR, 0 },
  { "llvm.va_start", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, VAStartMR, 0 },
  { "llvm.va_copy", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, VACopyMR, 0 },
  { "llvm.va_end", AliasAnalysis::NoModRef, LibCallFunctionInfo::DoesOnly, 0, 0 },
  { "write", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, WriteMR, 0 },
  { "__libc_fcntl", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "posix_fadvise", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "stat", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, StatMR, 0 },
  { "isatty", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, JustErrno, 0},
  { "__libc_sigaction", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, SigactionMR, 0 },
  { "socket", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "bind", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "listen", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "setsockopt", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "__libc_accept", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, AcceptMR, 0 },
  { "poll", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, PollMR, 0 },
  { "shutdown", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
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

