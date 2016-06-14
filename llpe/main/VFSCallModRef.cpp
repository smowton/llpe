//===- VFSCallModRef.cpp --------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <llvm/IR/Module.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Constants.h>

#include <llvm/Analysis/LLPE.h>
#include "llvm/Analysis/AliasAnalysis.h"

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

// This file describes the modified and referenced parameters of various Linux syscalls.
// If you want to generalise to another kernel or treat the libc interface like the syscall interface (for example)
// you'll want to factor this out.

// Functions to retrieve mod-ref locations that depend on other call parameters,
// e.g. the 'read' syscall gives the read extent as another parameter.

// Get 'read' syscall buffer:
static void getReadBuf(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  if(!tryGetConstantInt(getValArgOperand(CS, 2), Size))
    Size = MemoryLocation::UnknownSize;
  V = getValArgOperand(CS, 1);

}

// Get the pollfd array read by 'poll' if possible:
static void getPollFds(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  if(!tryGetConstantInt(getValArgOperand(CS, 1), Size))
    Size = MemoryLocation::UnknownSize;
  else
    Size *= sizeof(struct pollfd);
  V = getValArgOperand(CS, 0);
  
}

// Get a syscall's returned pointer:
static void getReturnVal(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  V = CS;
  Size = MemoryLocation::UnknownSize;

}

// 'recvfrom' gives the buffer size like 'read':
static void getRecvfromBuffer(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  ShadowValue LenArg = getValArgOperand(CS, 2);
  if(!tryGetConstantInt(LenArg, Size))
    Size = MemoryLocation::UnknownSize;
  V = getValArgOperand(CS, 1);

}

// Get the 'errno' global if possible:
static void getErrno(ShadowValue CS, ShadowValue& V, uint64_t& Size) {

  if(GlobalVariable* GV = cast<CallInst>(CS.getBareVal())->getParent()->getParent()->getParent()->getGlobalVariable("errno", true)) {
    V = ShadowValue(GV);
    Size = MemoryLocation::UnknownSize;
  }

}

// IHPLocationInfo's members:
// Either:
// { getBufferFunc, _, _ }, where getBufferFunc retrieves the buffer and size during specialisation
// Or:
// { NULL, argument number, buffer size }

// Plain parameters. These read/modify the given argument in its entirety.
struct IHPLocationInfo locArg0 = { 0, 0, MemoryLocation::UnknownSize };
struct IHPLocationInfo locArg1 = { 0, 1, MemoryLocation::UnknownSize };
struct IHPLocationInfo locArg2 = { 0, 2, MemoryLocation::UnknownSize };

// Sized parameters, These read/modify a particular argument size. This could need
// fixing if there's a chance we're building against a different struct than the kernel
// or alignment, pointer-size differ etc.
struct IHPLocationInfo locTermios = { 0, 2, sizeof(struct termios) };
struct IHPLocationInfo locTimespecArg1 = { 0, 1, sizeof(struct timespec) };
struct IHPLocationInfo locSockaddrArg4 = { 0, 4, sizeof(struct sockaddr) };
struct IHPLocationInfo locSocklenArg2 = { 0, 2, sizeof(socklen_t) };
struct IHPLocationInfo locSocklenArg5 = { 0, 5, sizeof(socklen_t) };
struct IHPLocationInfo locRlimitArg1 = { 0, 1, sizeof(struct rlimit) };
struct IHPLocationInfo locVaListArg0 = { 0, 0, 24 };

// Call-dependent parameters
struct IHPLocationInfo locReturnVal = { getReturnVal, 0, 0 };
struct IHPLocationInfo locPollFds = { getPollFds, 0, 0 };
struct IHPLocationInfo locReadBuf = { getReadBuf, 0, 0 };
struct IHPLocationInfo locRecvfromBuffer = { getRecvfromBuffer, 0, 0 };

// Globals
struct IHPLocationInfo locErrno = { getErrno, 0, 0 };

// Begin function descriptions. These are null-terminated lists of IHPLocationMRInfos.

static IHPLocationMRInfo JustErrno[] = {
  { &locErrno },
  { 0 }
};

static IHPLocationMRInfo ReadMR[] = {
  { &locErrno },
  { &locReadBuf },
  { 0 }
};

static IHPLocationMRInfo ReallocMR[] = {
  { &locArg0 },
  { &locReturnVal },
  { 0 }
};

static IHPLocationMRInfo MallocMR[] = {
  { &locReturnVal },
  { 0 }
};

static IHPLocationMRInfo TCGETSMR[] = {
  { &locErrno },
  { &locTermios },
  { 0 }
};

static IHPLocationMRInfo Arg1AndErrnoMR[] = {
  { &locErrno },
  { &locArg1 },
  { 0 }
};

static IHPLocationMRInfo GettimeofdayMR[] = {
  { &locErrno },
  { &locArg0 },
  { &locArg1 },
  { 0 }
};

static IHPLocationMRInfo Arg0AndErrnoMR[] = {
  { &locErrno },
  { &locArg0 },
  { 0 }
};

static IHPLocationMRInfo VAStartMR[] = {

  { &locVaListArg0 },
  { 0 }

};

static IHPLocationMRInfo VACopyMR[] = {

  { &locVaListArg0 },
  { 0 }

};

static IHPLocationMRInfo StatMR[] = {

  { &locErrno },
  { &locArg1 },
  { 0 }

};

static IHPLocationMRInfo SigactionMR[] = {

  { &locErrno },
  { &locArg2 },
  { 0 }

};

static IHPLocationMRInfo AcceptMR[] = {

  { &locErrno },
  { &locArg1 },
  { &locSocklenArg2 },
  { 0 }

};

static IHPLocationMRInfo PollMR[] = {

  { &locErrno },
  { &locPollFds },
  { 0 }

};

static IHPLocationMRInfo NanosleepMR[] = {

  { &locErrno },
  { &locTimespecArg1 },
  { 0 }

};

static IHPLocationMRInfo RecvfromMR[] = {

  { &locErrno },
  { &locRecvfromBuffer },
  { &locSockaddrArg4 },
  { &locSocklenArg5 },
  { 0 }

};

static IHPLocationMRInfo RlimitMR[] = {

  { &locErrno },
  { &locRlimitArg1 },
  { 0 }

};

static IHPLocationMRInfo SigprocmaskMR[] = {

  { &locErrno },
  { &locArg2 },
  { 0 }

};

static IHPLocationMRInfo DirentsMR[] = {

  { &locErrno },
  { &locArg1 },
  { 0 }

};

static IHPLocationMRInfo UnameMR[] = {

  { &locErrno },
  { &locArg0 },
  { 0 }

};

// This isn't very general, since TCGETS etc can alias other ioctls with different device types.
static const IHPLocationMRInfo* getIoctlLocDetails(ShadowValue CS) {

  uint64_t ioctlCode;
  if(!tryGetConstantInt(getValArgOperand(CS, 1), ioctlCode))
    return 0;
  
  switch(ioctlCode) {
  case TCGETS:
    return TCGETSMR;
  case FIONBIO:
    return JustErrno;
  default:
    return 0;
  }

}

// These relate function names to IHPLocationInfo arrays.
// The second field, if true, specifies the function is nomodref.
// The third gives a static array of IHPLocationInfos,
// or alternatively the fourth gives a function that will return an array
// that depends on the current specialisation state, currently only used for 'ioctl'.
static IHPFunctionInfo VFSCallFunctions[] = {

  { "open", false, JustErrno, 0 },
  { "read", false, ReadMR, 0 },
  { "lseek", false, JustErrno, 0 },
  { "llseek", false, JustErrno, 0 },
  { "lseek64", false, JustErrno, 0 },
  { "close", false, JustErrno, 0 },
  { "free", false, JustErrno, 0 },
  { "malloc", false, MallocMR, 0 },
  { "realloc", false, ReallocMR, 0 },
  { "ioctl", false, 0, getIoctlLocDetails },
  { "clock_gettime", false, Arg1AndErrnoMR, 0 },
  { "gettimeofday", false, GettimeofdayMR, 0 },
  { "time", false, Arg0AndErrnoMR, 0 },
  { "llvm.va_start", false, VAStartMR, 0 },
  { "llvm.va_copy", false, VACopyMR, 0 },
  { "llvm.va_end", true, 0, 0 },
  { "llvm.lifetime.start", true, 0, 0 },
  { "llvm.lifetime.end", true, 0, 0 },
  { "write", false, JustErrno, 0 },
  { "__libc_fcntl", false, JustErrno, 0 },
  { "__fcntl_nocancel", false, JustErrno, 0 },
  { "posix_fadvise", false, JustErrno, 0 },
  { "stat", false, StatMR, 0 },
  { "fstat", false, StatMR, 0 },
  { "isatty", false, JustErrno, 0},
  { "__libc_sigaction", false, SigactionMR, 0 },
  { "socket", false, JustErrno, 0 },
  { "bind", false, JustErrno, 0 },
  { "listen", false, JustErrno, 0 },
  { "setsockopt", false, JustErrno, 0 },
  { "__libc_accept", false, AcceptMR, 0 },
  { "poll", false, PollMR, 0 },
  { "shutdown", false, JustErrno, 0 },
  { "__libc_nanosleep", false, NanosleepMR, 0 },
  { "mkdir", false, JustErrno, 0 },
  { "rmdir", false, JustErrno, 0 },
  { "rename", false, JustErrno, 0 },
  { "setuid", false, JustErrno, 0 },
  { "getuid", false, JustErrno, 0 },
  { "geteuid", false, JustErrno, 0 },
  { "setgid", false, JustErrno, 0 },
  { "getgid", false, JustErrno, 0 },
  { "getegid", false, JustErrno, 0 },
  { "closedir", false, JustErrno, 0 },
  { "opendir", false, JustErrno, 0 },
  { "getsockname", false, JustErrno, 0 },
  { "__libc_recvfrom", false, RecvfromMR, 0 },
  { "__libc_sendto", false, JustErrno, 0 },
  { "mmap", false, JustErrno, 0 },
  { "munmap", false, JustErrno, 0 },
  { "mremap", false, JustErrno, 0 },
  { "clock_getres", false, NanosleepMR, 0 },
  { "getrlimit", false, RlimitMR, 0 },
  { "sigprocmask", false, SigprocmaskMR, 0 },
  { "unlink", false, JustErrno, 0 },
  { "__getdents64", false, DirentsMR, 0 },
  { "brk", false, JustErrno, 0 },
  { "getpid", false, JustErrno, 0 },
  { "kill", false, JustErrno, 0 },
  { "uname", false, UnameMR, 0 },
  { "__pthread_mutex_init", false, Arg0AndErrnoMR, 0 },
  { "__pthread_mutex_lock", false, Arg0AndErrnoMR, 0 },
  { "__pthread_mutex_trylock", false, Arg0AndErrnoMR, 0 },  
  { "__pthread_mutex_unlock", false, Arg0AndErrnoMR, 0 },
  { "pthread_setcanceltype", false, Arg1AndErrnoMR, 0 },
  { "pthread_setcancelstate", false, Arg1AndErrnoMR, 0 },
  { "writev", false, JustErrno, 0 },
  { "epoll_create", false, JustErrno, 0 },
  { "dup2", false, JustErrno, 0 },
  { "access", false, JustErrno, 0 },
  // Terminator
  { 0, false, 0, 0 }

};

// Populate tables relating Function* to mod-ref info, instead of looking up by name every time.
void LLPEAnalysisPass::initMRInfo(Module* M) {

  for(uint32_t i = 0; VFSCallFunctions[i].Name; ++i) {

    Function* F = M->getFunction(VFSCallFunctions[i].Name);
    functionMRInfo[F] = VFSCallFunctions[i];

  }

}

IHPFunctionInfo* LLPEAnalysisPass::getMRInfo(Function* F) {

  DenseMap<Function*, IHPFunctionInfo>::iterator findit = functionMRInfo.find(F);
  if(findit == functionMRInfo.end())
    return 0;
  else
    return &findit->second;
  
}
