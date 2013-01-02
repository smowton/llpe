
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/Debug.h"
#include "llvm/System/Path.h"
#include "llvm/Support/CFG.h"

#include <fcntl.h> // For O_RDONLY et al
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>

// Implement a backward walker to identify a VFS operation's predecessor, and a forward walker to identify open instructions
// which can be shown pointless because along all paths it ends up at a close instruction.

using namespace llvm;

bool IntegrationAttempt::tryPromoteOpenCall(CallInst* CI) {
  
  if(Function *SysOpen = F.getParent()->getFunction("open")) {
    const FunctionType *FT = SysOpen->getFunctionType();
    if (FT->getNumParams() == 2 && FT->getReturnType()->isIntegerTy(32) &&
        FT->getParamType(0)->isPointerTy() &&
        FT->getParamType(1)->isIntegerTy(32) &&
	FT->isVarArg()) {

      if(Function* FCalled = getCalledFunction(CI)) {

	if(FCalled == SysOpen) {

	  ValCtx ModeArg = getReplacement(CI->getArgOperand(1));
	  if(ConstantInt* ModeValue = dyn_cast<ConstantInt>(ModeArg.first)) {
	    int RawMode = (int)ModeValue->getLimitedValue();
	    if(RawMode & O_RDWR || RawMode & O_WRONLY) {
	      LPDEBUG("Can't promote open call " << itcache(*CI) << " because it is not O_RDONLY\n");
	      return true;
	    }
	  }
	  else {
	    LPDEBUG("Can't promote open call " << itcache(*CI) << " because its mode argument can't be resolved\n");
	    return true;
	  }
	  
	  ValCtx NameArg = getReplacement(CI->getArgOperand(0));
	  std::string Filename;
	  if (!GetConstantStringInfo(NameArg.first, Filename)) {
	    LPDEBUG("Can't promote open call " << itcache(*CI) << " because its filename argument is unresolved\n");
	    return true;
	  }

	  bool FDEscapes = false;
	  for(Value::use_iterator UI = CI->use_begin(), UE = CI->use_end(); (!FDEscapes) && (UI != UE); ++UI) {

	    if(Instruction* I = dyn_cast<Instruction>(*UI)) {

	      if(I->mayWriteToMemory()) {
		
		LPDEBUG("Marking open call " << itcache(*CI) << " escaped due to user " << itcache(*I) << "\n");
		FDEscapes = true;

	      }

	    }

	  }
	  
	  bool exists = sys::Path(Filename).exists();
	  forwardableOpenCalls[CI] = new OpenStatus(Filename, exists, FDEscapes);
	  if(exists) {
	    LPDEBUG("Successfully promoted open of file " << Filename << ": queueing initial forward attempt\n");
	  }
	  else {
	    LPDEBUG("Open of " << Filename << " returning ENOENT\n");
	  }

	  return true;
      
	}
	else {
	  
	  LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because it calls something else\n");

	}

      }
      else {
	
	LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because its target is unknown\n");

      }

    }
    else {

      LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because the symbol 'open' resolves to something with inappropriate type!\n");

    }

  }
  else {

    LPDEBUG("Unable to identify " << itcache(*CI) << " as an open call because no symbol 'open' is in scope\n");

  }

  return false;

}

class FindVFSPredecessorWalker : public BackwardIAWalker {

  CallInst* SourceOp;
  IntegrationAttempt* SourceCtx;
  ValCtx FD;

public:

  int64_t unqiueIncomingOffset;

  FindVFSPredecessorWalker(CallInst* CI, IntegrationAttempt* IA, ValCtx _FD) 
    : BackwardIAWalker(SourceOp, SourceCtx, true), SourceOp(CI), SourceCtx(IA), FD(_FD),
      uniqueIncomingOffset(-1) { }
  WalkInstructionResult walkInstruction(Instruction*, IntegrationAttempt*);
  bool shouldEnterCall(CallInst*, IntegrationAttempt*);
  bool blockedByUnexpandedCall(CallInst*, IntegrationAttempt*);

};

WalkInstructionResult FindVFSPredecessorWalker::walkInstruction(Instruction* I, IntegrationAttempt* IA) {

  // Determine whether this instruction is a VFS call using our FD.
  // No need to worry about call instructions, just return WIRContinue and we'll enter it if need be.

  if(CallInst* CI = dyn_cast<CallInst>(BI)) {

    WalkInstructionResult WIR = IA->isVfsCallUsingFD(CI, FD);
    if(WIR == WIRStopThisPath) {

      // Call definitely uses this FD. Find the incoming offset if possible.
      int64_t incomingOffset = IA->tryGetIncomingOffset(CI);
      if(incomingOffset == -1) {
	
	return WIRStopWholeWalk;
	
      }
      else if(uniqueIncomingOffset == -1) {

	uniqueIncomingOffset = incomingOffset;

      }
      else if(uniqueIncomingOffset != incomingOffset) {

	// Conflict!
	uniqueIncomingOffset = -1;
	return WIRStopWholeWalk;

      }

    }

    return WIR;

  }

  return WIRContinue;

}

bool FindVFSPredecessorWalker::shouldEnterCall(CallInst* CI, IntegrationAttempt* IA) {

  // This call cannot affect the FD we're pursuing unless (a) it uses the FD, or (b) the FD escapes (is stored) and the function is non-pure.
  
  OpenStatus& OS = FD.second->getOpenStatus(FD.first);
  Function* calledF = IA->getCalledFunction(CI);

  // None of the blacklisted syscalls not accounted for under vfsCallBlocksOpen mess with FDs in a way that's important to us.
  bool ignore = false;
  if(isa<MemIntrinsic>(CI) || isa<DbgInfoIntrinsic>(CI) || (calledF && IA->functionIsBlacklisted(calledF)))
    return false;
  else if(OS.FDEscapes && ((!calledF) || !calledF->doesNotAccessMemory()))
    return true;

  for(unsigned i = 0; i < CI->getNumArgOperands() && !callMayUseFD; ++i) {

    ValCtx ArgVC = IA->getReplacement(CI->getArgOperand(i));
    if(ArgVC == OpenInst)
      return true;
    if(IA->isUnresolved(CI->getArgOperand(i)))
      return true;
    
  }
	    
}

bool FindVFSPredecessorWalker::blockedByUnexpandedCall(CallInst* CI, IntegrationAttempt* IA) {

  uniqueIncomingOffset = -1;
  return true;

}

// Return value: is this a VFS call (regardless of whether we resolved it successfully)
bool IntegrationAttempt::tryResolveVFSCall(CallInst* CI) {

  Function* F = getCalledFunction(CI);
  if(!F)
    return false;

  const FunctionType *FT = F->getFunctionType();
  
  if(!(F->getName() == "close" || F->getName() == "llseek" || F->getName() == "lseek" || 
       F->getName() == "lseek64" || F->getName() == "close"))
    return false;

  Value* FD = CI->getArgOperand(0);
  if(isUnresolved(FD))
    return true;

  ValCtx OpenCall = getReplacement(FD);
  OpenStatus& OS = OpenCall.second->getOpenStatus(OpenCall.first);

  bool needsWalk = false;
  if(F->getName() == "llseek" || F->getName() == "lseek" || F->getName() == "lseek64") {

    // Check for needed values now:
    Constant* whence = getConstReplacement(CI->getArgOperand(2));
    Constant* newOffset = getConstReplacement(CI->getArgOperand(1));
    
    if((!newOffset) || (!whence))
      return true;

    uint64_t intOffset = cast<ConstantInt>(newOffset)->getLimitedValue();
    int32_t seekWhence = (int32_t)cast<ConstantInt>(whence)->getSExtValue();
    
    bool needsWalk = false;
    switch(seekWhence) {
    case SEEK_CUR:
      {
	// Needs the incoming offset. Go to walk:
	needsWalk = true;
	break;
      }
    case SEEK_END:
      {
	struct stat file_stat;
	if(::stat(OS.Name.c_str(), &file_stat) == -1) {
	  
	  LPDEBUG("Failed to stat " << OS.Name << "\n");
	  return true;
	  
	}
	intOffset += file_stat.st_size;
	break;
      }  
    case SEEK_SET:
      break;
    default:
      LPDEBUG("Seek whence parameter is unknown value " << seekWhence << "!");
      return true;
    }

    if(!needsWalk) {

      // Doesn't matter what came before, resolve this call here.
      setReplacement(CI, const_vc(ConstantInt::get(FT->getParamType(1), intOffset)));
      resolveSeekCall(VFSCall, SeekFile(&OS, intOffset));
      return true;

    }
    // Else fall through to the walk phase.

  }
  else if(F->getName() == "close") {

    resolvedCloseCalls[VFSCall] = CloseFile(&OS);    
    setReplacement(VFSCall, const_vc(ConstantInt::get(FT->getReturnType(), 0)));

  }
  // Else it's a read call, and we need the incoming file offset.

  FindVFSPredecessorWalker Walk(CI, this, OpenCall);
  Walk.walk();

  if(Walk.uniqueIncomingOffset == -1)
    return true;

  if(F->getName() == "read") {

    Value* readBytes = CI->getArgOperand(2);
    ConstantInt* intBytes = cast<ConstantInt>(getConstReplacement(readBytes));
    
    int64_t cBytes = intBytes->getLimitedValue();

    struct stat file_stat;
    if(::stat(OS.Name.c_str(), &file_stat) == -1) {
      LPDEBUG("Failed to stat " << OS.Name << "\n");
      return true;
    }
    
    int64_t bytesAvail = file_stat.st_size - Walk.uniqueIncomingOffset;
    if(cBytes > bytesAvail) {
      LPDEBUG("Desired read of " << cBytes << " truncated to " << bytesAvail << " (EOF)\n");
      cBytes = bytesAvail;
    }

    // OK, we know what this read operation does. Record that and queue another exploration from this point.
    LPDEBUG("Successfully resolved " << itcache(*CI) << " which reads " << cBytes << " bytes\n");
    
    resolveReadCall(CI, ReadFile(&OS, Walk.uniqueIncomingOffset, cBytes));
    
    // The number of bytes read is also the return value of read.
    setReplacement(VFSCall, const_vc(ConstantInt::get(Type::getInt64Ty(VFSCall->getContext()), cBytes)));

  }
  else {

    // It's a seek call, with SEEK_CUR.
    Constant* newOffset = getConstReplacement(CI->getArgOperand(1));
    int64_t intOffset = cast<ConstantInt>(newOffset)->getLimitedValue();
    intOffset += Walk.uniqueIncomingOffset;

    resolveSeekCall(CI, SeekFile(&OS, intOffset));

  }

  return true;
  
}

int64_t IntegrationAttempt::tryGetIncomingOffset(CallInst* CI) {

  if(forwardableOpenCalls.count(CI))
    return 0;

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return it->second.incomingOffset + it->second.readSize;

  DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
  if(it != resolvedSeekCalls.end())
    return it->second.newOffset;
 
  return -1;

}

ReadFile* IntegrationAttempt::tryGetReadFile(CallInst* CI) {

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return &it->second;
  else
    return 0;

}

WalkInstructionResult IntegrationAttempt::isVfsCallUsingFD(CallInst* VFSCall, ValCtx FD) {
  
  // Is VFSCall a call to open, read, seek or close that concerns FD?
  
  Function* Callee = getCalledFunction(VFSCall);
  if(!Callee)
    return WIRContinue;

  if(make_vc(VFSCall, this) == FD)
    return WIRStopThisPath;

  StringRef CalleeName = Callee->getName();
  if(CalleeName == "read") {
    
    Value* readFD = VFSCall->getArgOperand(0);
    if(isUnresolved(readFD)) {
      
      LPDEBUG("Can't resolve VFS call because FD argument of " << itcache(*VFSCall) << " is unresolved\n");
      return WIRStopWholeWalk;
      
    }
    else if(getReplacement(readFD) != FD) {
      
      LPDEBUG("Ignoring " << itcache(*VFSCall) << " which references a different file\n");
      return WIRContinue;
      
    }

    return WIRStopThisPath;
    
  }
  else if(CalleeName == "close") {

    // Finding this indicates we could double-close if this path were followed for real!
    // Walk through it to find its predecessors.
    return WIRContinue;
    
  }
  else if(CalleeName == "llseek" || CalleeName == "lseek" || CalleeName == "lseek64") {
    
    Value* seekFD = VFSCall->getArgOperand(0);
    if(isUnresolved(seekFD)) {
      return WIRStopWholeWalk;
    }
    else if(getReplacement(seekFD) != OpenInst) {
      return WIRContinue;
    }
    
    return WIRStopThisPath;
    
  }
  
  return WIRContinue;
  
}

bool IntegrationAttempt::isCloseCall(CallInst* CI) {

  return resolvedCloseCalls.count(CI);

}

void IntegrationAttempt::resolveReadCall(CallInst* CI, struct ReadFile RF) {

  resolvedReadCalls[CI] = RF;

}

void IntegrationAttempt::resolveSeekCall(CallInst* CI, struct SeekFile SF) {

  resolvedSeekCalls[CI] = SF;

}

bool IntegrationAttempt::isResolvedVFSCall(const Instruction* I) {
  
  if(CallInst* CI = dyn_cast<CallInst>(const_cast<Instruction*>(I))) {

    return forwardableOpenCalls.count(CI) || resolvedReadCalls.count(CI) || resolvedSeekCalls.count(CI) || resolvedCloseCalls.count(CI);

  }

  return false;

}

bool IntegrationAttempt::isSuccessfulVFSCall(const Instruction* I) {
  
  if(CallInst* CI = dyn_cast<CallInst>(const_cast<Instruction*>(I))) {

    DenseMap<CallInst*, OpenStatus*>::iterator it = forwardableOpenCalls.find(CI);
    if(it != forwardableOpenCalls.end() && !it->second->success)
      return false;

    return forwardableOpenCalls.count(CI) || resolvedReadCalls.count(CI) || resolvedSeekCalls.count(CI) || resolvedCloseCalls.count(CI);

  }

  return false;

}

bool IntegrationAttempt::isUnusedReadCall(CallInst* CI) {

  // Return true if CI is a read instruction that won't be in the final committed program:
  // this is true if it's zero-length or if there are no live users of the buffer it writes.
  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end()) {

    return unusedWriters.count(CI) || !it->second.readSize;

  }

  return false;

}

OpenStatus& getOpenStatus(CallInst* CI) {

  return forwardableOpenCalls[CI];

}

