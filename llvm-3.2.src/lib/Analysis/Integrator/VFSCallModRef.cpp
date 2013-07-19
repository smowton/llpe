
#include <llvm/Analysis/VFSCallModRef.h>

#include <llvm/Module.h>
#include <llvm/Function.h>
#include <llvm/Constants.h>

#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/LibCallSemantics.h>
#include <llvm/Analysis/HypotheticalConstantFolder.h>

// For various structures and constants:
#include <termios.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <poll.h>
#include <time.h>
#include <sys/time.h>
#include <sys/resource.h>

using namespace llvm;

VFSCallAliasAnalysis::VFSCallAliasAnalysis() : LibCallAliasAnalysis(ID, new VFSCallModRef()) {
  //initializeBasicAliasAnalysisPass(*PassRegistry::getPassRegistry());
}

const LibCallFunctionInfo* VFSCallAliasAnalysis::getFunctionInfo(Function* F) {
  
  return LCI->getFunctionInfo(F);

}

static LibCallLocationInfo::LocResult aliasCheckAsLCI(ShadowValue Ptr1, uint64_t Ptr1Size, ShadowValue Ptr2, uint64_t Ptr2Size, bool usePBKnowledge, int64_t Ptr1Offset, IntAAProxy* AACB) {

  SVAAResult AR;
  if(Ptr1Offset != LLONG_MAX)
    AR = tryResolveImprovedValSetSingles(Ptr1, Ptr1Offset, Ptr1Size, Ptr2, Ptr2Size, true);
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

LibCallLocationInfo::LocResult VFSCallModRef::isLocation(const LibCallLocationInfo& LCI, ShadowValue CS, ShadowValue Ptr, uint64_t Size, const MDNode* PtrTag, bool usePBKnowledge, int64_t POffset, IntAAProxy* AACB) {

  ShadowValue CSPtr;
  uint64_t CSPtrSize;
  if(!LCI.getLocation) {
    CSPtr = getValArgOperand(CS, LCI.argIndex);
    CSPtrSize = LCI.argSize;
  }
  else {
    LCI.getLocation(CS, CSPtr, CSPtrSize);
  }
  return aliasCheckAsLCI(Ptr, Size, CSPtr, CSPtrSize, usePBKnowledge, POffset, AACB);

}

static void isReadBuf(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  ConstantInt* ReadSize = cast_or_null<ConstantInt>(getConstReplacement(getValArgOperand(CS, 2)));
  V = getValArgOperand(CS, 1);
  Size = ReadSize ? ReadSize->getLimitedValue() : AliasAnalysis::UnknownSize;

}

static void isPollFds(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  ConstantInt* nFDs = cast_or_null<ConstantInt>(getConstReplacement(getValArgOperand(CS, 1)));
  Size = nFDs ? (nFDs->getLimitedValue() * sizeof(struct pollfd)) : AliasAnalysis::UnknownSize;
  V = getValArgOperand(CS, 0);
  
}

static void isReturnVal(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  V = CS;
  Size = AliasAnalysis::UnknownSize;

}

static void isRecvfromBuffer(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  ShadowValue LenArg = getValArgOperand(CS, 2);
  if(ConstantInt* CI = dyn_cast_or_null<ConstantInt>(getConstReplacement(LenArg)))
    Size = CI->getLimitedValue();
  else
    Size = AliasAnalysis::UnknownSize;
  V = getValArgOperand(CS, 1);

}

static void isErrno(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  if(GlobalVariable* GV = cast<CallInst>(CS.getBareVal())->getParent()->getParent()->getParent()->getGlobalVariable("errno")) {
    V = ShadowValue(GV);
    Size = AliasAnalysis::UnknownSize;
  }

}

// Plain parameters:
struct LibCallLocationInfo locArg0 = { 0, 0, AliasAnalysis::UnknownSize };
struct LibCallLocationInfo locArg1 = { 0, 1, AliasAnalysis::UnknownSize };
struct LibCallLocationInfo locArg2 = { 0, 2, AliasAnalysis::UnknownSize };

// Sized parameters:
struct LibCallLocationInfo locTermios = { 0, 2, sizeof(struct termios) };
struct LibCallLocationInfo locTimespecArg1 = { 0, 1, sizeof(struct timespec) };
struct LibCallLocationInfo locSockaddrArg4 = { 0, 4, sizeof(struct sockaddr) };
struct LibCallLocationInfo locSocklenArg2 = { 0, 2, sizeof(socklen_t) };
struct LibCallLocationInfo locSocklenArg5 = { 0, 5, sizeof(socklen_t) };
struct LibCallLocationInfo locRlimitArg1 = { 0, 1, sizeof(struct rlimit) };
struct LibCallLocationInfo locVaListArg0 = { 0, 0, 24 };

// Call-dependent parameters
struct LibCallLocationInfo locReturnVal = { isReturnVal, 0, 0 };
struct LibCallLocationInfo locPollFds = { isPollFds, 0, 0 };
struct LibCallLocationInfo locReadBuf = { isReadBuf, 0, 0 };
struct LibCallLocationInfo locRecvfromBuffer = { isRecvfromBuffer, 0, 0 };

// Globals
struct LibCallLocationInfo locErrno = { isErrno, 0, 0 };

// Begin function descriptions

static LibCallFunctionInfo::LocationMRInfo JustErrno[] = {
  { &locErrno, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo ReadMR[] = {
  { &locErrno, AliasAnalysis::Mod },
  { &locReadBuf, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo ReallocMR[] = {
  { &locArg0, AliasAnalysis::Mod },
  { &locReturnVal, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo MallocMR[] = {
  { &locReturnVal, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo TCGETSMR[] = {
  { &locErrno, AliasAnalysis::Mod },
  { &locTermios, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo GettimeMR[] = {
  { &locErrno, AliasAnalysis::Mod },
  { &locArg1, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo GettimeofdayMR[] = {
  { &locErrno, AliasAnalysis::Mod },
  { &locArg0, AliasAnalysis::Mod },
  { &locArg1, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo Arg0AndErrnoMR[] = {
  { &locErrno, AliasAnalysis::Mod },
  { &locArg0, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }
};

static LibCallFunctionInfo::LocationMRInfo VAStartMR[] = {

  { &locVaListArg0, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo VACopyMR[] = {

  { &locVaListArg0, AliasAnalysis::Mod },
  { &locArg1, AliasAnalysis::Ref },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo WriteMR[] = {

  { &locArg1, AliasAnalysis::Ref },
  { &locErrno, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo StatMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locArg0, AliasAnalysis::Ref },
  { &locArg1, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo SigactionMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locArg1, AliasAnalysis::Ref },
  { &locArg2, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo AcceptMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locArg1, AliasAnalysis::Mod },
  { &locSocklenArg2, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo PollMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locPollFds, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo NanosleepMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locTimespecArg1, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo RecvfromMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locRecvfromBuffer, AliasAnalysis::Mod },
  { &locSockaddrArg4, AliasAnalysis::Mod },
  { &locSocklenArg5, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo RlimitMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locRlimitArg1, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo SigprocmaskMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locArg2, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo DirentsMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locArg1, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

};

static LibCallFunctionInfo::LocationMRInfo UnameMR[] = {

  { &locErrno, AliasAnalysis::Mod },
  { &locArg0, AliasAnalysis::Mod },
  { 0, AliasAnalysis::ModRef }

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
  { "time", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, Arg0AndErrnoMR, 0 },
  { "llvm.va_start", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, VAStartMR, 0 },
  { "llvm.va_copy", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, VACopyMR, 0 },
  { "llvm.va_end", AliasAnalysis::NoModRef, LibCallFunctionInfo::DoesOnly, 0, 0 },
  { "llvm.lifetime.start", AliasAnalysis::NoModRef, LibCallFunctionInfo::DoesOnly, 0, 0 },
  { "llvm.lifetime.end", AliasAnalysis::NoModRef, LibCallFunctionInfo::DoesOnly, 0, 0 },
  { "write", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, WriteMR, 0 },
  { "__libc_fcntl", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "__fcntl_nocancel", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "posix_fadvise", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "stat", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, StatMR, 0 },
  { "fstat", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, StatMR, 0 },
  { "isatty", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, JustErrno, 0},
  { "__libc_sigaction", AliasAnalysis::ModRef, LibCallFunctionInfo::DoesOnly, SigactionMR, 0 },
  { "socket", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "bind", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "listen", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "setsockopt", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "__libc_accept", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, AcceptMR, 0 },
  { "poll", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, PollMR, 0 },
  { "shutdown", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "__libc_nanosleep", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, NanosleepMR, 0 },
  { "mkdir", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "rmdir", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "rename", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "setuid", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "getuid", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "geteuid", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "setgid", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "getgid", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "getegid", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "closedir", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "opendir", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "getsockname", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "__libc_recvfrom", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, RecvfromMR, 0 },
  { "__libc_sendto", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "mmap", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "munmap", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "mremap", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "clock_getres", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, NanosleepMR, 0 },
  { "getrlimit", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, RlimitMR, 0 },
  { "sigprocmask", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, SigprocmaskMR, 0 },
  { "unlink", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "__getdents64", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, DirentsMR, 0 },
  { "brk", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "getpid", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "kill", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, JustErrno, 0 },
  { "uname", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, UnameMR, 0 },
  { "__pthread_mutex_init", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, Arg0AndErrnoMR, 0 },
  { "__pthread_mutex_lock", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, Arg0AndErrnoMR, 0 },
  { "__pthread_mutex_trylock", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, Arg0AndErrnoMR, 0 },  
  { "__pthread_mutex_unlock", AliasAnalysis::Mod, LibCallFunctionInfo::DoesOnly, Arg0AndErrnoMR, 0 },
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

static RegisterPass<VFSCallAliasAnalysis> X1("vfscall-aa", "VFS Call Alias Analysis", false /* Only looks at CFG */, true /* Analysis Pass */);
static RegisterAGBase X2("vfscall-aa", &AliasAnalysis::ID, &VFSCallAliasAnalysis::ID);
