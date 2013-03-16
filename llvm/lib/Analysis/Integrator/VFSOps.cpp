
#include "llvm/Analysis/HypotheticalConstantFolder.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/BasicBlock.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/Debug.h"
#include "llvm/System/Path.h"
#include "llvm/Support/CFG.h"

#include <fcntl.h> // For O_RDONLY et al
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <errno.h>

// Implement a backward walker to identify a VFS operation's predecessor, and a forward walker to identify open instructions
// which can be shown pointless because along all paths it ends up at a close instruction.

using namespace llvm;

bool IntegrationAttempt::getConstantString(ShadowValue Ptr, ShadowInstruction* SearchFrom, std::string& Result) {

  if(Ptr.isVal() && GetConstantStringInfo(cast<Constant>(Ptr.getVal()), Result))
    return true;

  ShadowValue StrBase;
  int64_t StrOffset;
  if(!getBaseAndConstantOffset(Ptr, StrBase, StrOffset))
    return false;

  Result = "";
  
  // Try to LF one character at a time until we get null or a failure.

  LPDEBUG("forwarding off " << itcache(Ptr) << "\n");

  const Type* byteType = Type::getInt8PtrTy(SearchFrom->invar->I->getContext());

  bool success = true;

  for(; success; ++StrOffset) {

    // Create a GEP to access the next byte:

    std::string fwdError;

    PointerBase byte = tryForwardLoadArtificial(SearchFrom, StrBase, StrOffset, 1, byteType, 0, fwdError, 0);
    if(byte.Overdef || byte.Type != ValSetTypeScalar || byte.Values.size() != 1) {

      LPDEBUG("Open forwarding error: " << fwdError << "\n");
      success = false;
      
    }
    else {

      DEBUG(dbgs() << "Open forwarding success: ");
      DEBUG(printPB(dbgs(), byte));
      DEBUG(dbgs() << "\n");

      uint64_t nextChar = cast<ConstantInt>(byte.Values[0].V.getVal())->getLimitedValue();
      if(!nextChar) {
	
	// Null terminator.
	break;

      }
      else {

	Result.push_back((unsigned char)nextChar);

      }

    }

  }

  return success;

}

bool IntegrationAttempt::tryPromoteOpenCall(ShadowInstruction* SI) {

  CallInst* CI = cast<CallInst>(SI->invar->I);
  
  if(Function *SysOpen = F.getParent()->getFunction("open")) {
    const FunctionType *FT = SysOpen->getFunctionType();
    if (FT->getNumParams() == 2 && FT->getReturnType()->isIntegerTy(32) &&
        FT->getParamType(0)->isPointerTy() &&
        FT->getParamType(1)->isIntegerTy(32) &&
	FT->isVarArg()) {

      if(Function* FCalled = getCalledFunction(SI)) {

	if(FCalled == SysOpen) {

	  if(ConstantInt* ModeValue = dyn_cast_or_null<ConstantInt>(getConstReplacement(SI->getCallArgOperand(1)))) {
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
	  
	  ShadowValue NameArg = SI->getCallArgOperand(0);
	  std::string Filename;
	  if (!getConstantString(NameArg, SI, Filename)) {
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
	    SI->i.PB = PointerBase::get(ImprovedVal(ShadowValue(SI)), ValSetTypeFD);
	    LPDEBUG("Successfully promoted open of file " << Filename << ": queueing initial forward attempt\n");
	  }
	  else {
	    setReplacement(SI, ConstantInt::get(SI->invar->I->getType(), (uint64_t)-1, true));
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

  ShadowInstruction* SourceOp;
  IntegrationAttempt* IA;
  ShadowInstruction* FD;

public:

  int64_t uniqueIncomingOffset;

  FindVFSPredecessorWalker(ShadowInstruction* CI, ShadowInstruction* _FD) 
    : BackwardIAWalker(CI->invar->idx, CI->parent, true), SourceOp(CI), FD(_FD),
      uniqueIncomingOffset(-1) { 
    IA = SourceOp->parent->IA;
  }
  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void*);
  virtual bool shouldEnterCall(ShadowInstruction*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);

};

WalkInstructionResult FindVFSPredecessorWalker::walkInstruction(ShadowInstruction* I, void*) {

  // Determine whether this instruction is a VFS call using our FD.
  // No need to worry about call instructions, just return WIRContinue and we'll enter it if need be.

  IntegrationAttempt* IA = I->parent->IA;

  if(CallInst* CI = dyn_cast_inst<CallInst>(I)) {

    WalkInstructionResult WIR = IA->isVfsCallUsingFD(I, FD, true);
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

static ShadowInstruction* getFD(ShadowValue V) {

  if(V.isVal())
    return 0;

  PointerBase VPB;
  if(!getPointerBase(V, VPB))
    return 0;

  if(VPB.Overdef || VPB.Values.size() != 1 || VPB.Type != ValSetTypeFD)
    return 0;

  return VPB.Values[0].V.getInst();

}

static AliasAnalysis::AliasResult aliasesFD(ShadowValue V, ShadowInstruction* FD) {

  if(V.isVal())
    return AliasAnalysis::NoAlias;

  PointerBase VPB;
  if(!getPointerBase(V, VPB))
    return AliasAnalysis::MayAlias;

  if(VPB.Overdef || VPB.Values.size() == 0)
    return AliasAnalysis::MayAlias;

  if(VPB.Type != ValSetTypeFD)
    return AliasAnalysis::NoAlias;

  if(VPB.Values.size() == 1 && VPB.Values[0].V.getInst() == FD)
    return AliasAnalysis::MustAlias;

  for(uint32_t i = 0; i < VPB.Values.size(); ++i) {
    if(VPB.Values[i].V.getInst() == FD)
      return AliasAnalysis::MayAlias;
  }

  return AliasAnalysis::NoAlias;

}

static bool callMayUseFD(ShadowInstruction* SI, ShadowInstruction* FD) {

  CallInst* CI = cast_inst<CallInst>(SI);

 // This call cannot affect the FD we're pursuing unless (a) it uses the FD, or (b) the FD escapes (is stored) and the function is non-pure.
  
  OpenStatus& OS = FD->parent->IA->getOpenStatus(cast_inst<CallInst>(FD));
  Function* calledF = getCalledFunction(SI);

  // None of the blacklisted syscalls not accounted for under vfsCallBlocksOpen mess with FDs in a way that's important to us.
  if(isa<MemIntrinsic>(CI) || isa<DbgInfoIntrinsic>(CI) || (calledF && functionIsBlacklisted(calledF)))
    return false;
  else if(OS.FDEscapes && ((!calledF) || !calledF->doesNotAccessMemory()))
    return true;

  for(unsigned i = 0; i < CI->getNumArgOperands(); ++i) {

    ShadowValue ArgOp = SI->getCallArgOperand(i);
    if(aliasesFD(ArgOp, FD) != AliasAnalysis::NoAlias)
      return true;
    
  }

  return false;

}

bool FindVFSPredecessorWalker::shouldEnterCall(ShadowInstruction* SI) {

  return callMayUseFD(SI, FD);
	    
}

bool FindVFSPredecessorWalker::blockedByUnexpandedCall(ShadowInstruction* SI, void*) {

  uniqueIncomingOffset = -1;
  return true;

}

// Return value: is this a VFS call (regardless of whether we resolved it successfully)
bool IntegrationAttempt::tryResolveVFSCall(ShadowInstruction* SI) {

  CallInst* CI = cast<CallInst>(SI->invar->I);

  Function* F = getCalledFunction(SI);
  if(!F)
    return false;

  const FunctionType *FT = F->getFunctionType();
  
  if(!(F->getName() == "read" || F->getName() == "llseek" || F->getName() == "lseek" || 
       F->getName() == "lseek64" || F->getName() == "close" || F->getName() == "stat" ||
       F->getName() == "isatty"))
    return false;

  if(F->getName() == "stat") {

    // TODO: Add LF resolution code notifying file size. All users so far have just
    // used stat as an existence test. Similarly set errno = ENOENT as appropriate.

    std::string Filename;
    if (!getConstantString(SI->getCallArgOperand(0), SI, Filename)) {
      LPDEBUG("Can't resolve stat call " << itcache(*CI) << " because its filename argument is unresolved\n");
      return true;
    }
    
    struct stat file_stat;
    int stat_ret = ::stat(Filename.c_str(), &file_stat);

    if(stat_ret == -1 && errno != ENOENT)
      return true;

    setReplacement(SI, ConstantInt::get(FT->getReturnType(), stat_ret));
    return true;

  }

  // All calls beyond here operate on FDs.
  ShadowInstruction* OpenCall = getFD(SI->getCallArgOperand(0));
  if(!OpenCall)
    return true;

  OpenStatus& OS = OpenCall->parent->IA->getOpenStatus(cast_inst<CallInst>(OpenCall));

  if(F->getName() == "isatty") {

    // OpenStatus items like this are always real files, not TTYs, for now.
    setReplacement(SI, ConstantInt::get(FT->getReturnType(), 0));
    return true;

  }
  else if(F->getName() == "llseek" || F->getName() == "lseek" || F->getName() == "lseek64") {

    // Check for needed values now:
    Constant* whence = getConstReplacement(SI->getCallArgOperand(2));
    Constant* newOffset = getConstReplacement(SI->getCallArgOperand(1));
    
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
      setReplacement(SI, ConstantInt::get(FT->getParamType(1), intOffset));
      resolveSeekCall(CI, SeekFile(&OS, intOffset));
      return true;

    }
    // Else fall through to the walk phase.

  }
  else if(F->getName() == "close") {

    resolvedCloseCalls[CI] = CloseFile(&OS, OpenCall);    
    setReplacement(SI, ConstantInt::get(FT->getReturnType(), 0));
    return true;

  }
  // Else it's a read call or relative seek, and we need the incoming file offset.

  FindVFSPredecessorWalker Walk(SI, OpenCall);
  Walk.walk();

  if(Walk.uniqueIncomingOffset == -1)
    return true;

  if(F->getName() == "read") {

    ShadowValue readBytes = SI->getCallArgOperand(2);
    ConstantInt* intBytes = cast_or_null<ConstantInt>(getConstReplacement(readBytes));
    if(!intBytes)
      return true;
    
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
    setReplacement(SI, ConstantInt::get(Type::getInt64Ty(CI->getContext()), cBytes));

  }
  else {

    // It's a seek call, with SEEK_CUR.
    Constant* newOffset = getConstReplacement(CI->getArgOperand(1));
    int64_t intOffset = cast<ConstantInt>(newOffset)->getLimitedValue();
    intOffset += Walk.uniqueIncomingOffset;

    resolveSeekCall(CI, SeekFile(&OS, intOffset));

    // Return value: new file offset.
    setReplacement(SI, ConstantInt::get(FT->getParamType(1), intOffset));

  }

  return true;
  
}

int64_t IntegrationAttempt::tryGetIncomingOffset(CallInst* CI) {

  if(forwardableOpenCalls.count(CI))
    return 0;

  {
    DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
    if(it != resolvedReadCalls.end())
      return it->second.incomingOffset + it->second.readSize;
  }

  {
    DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
    if(it != resolvedSeekCalls.end())
      return it->second.newOffset;
  } 

  return -1;

}

ReadFile* IntegrationAttempt::tryGetReadFile(CallInst* CI) {

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return &it->second;
  else
    return 0;

}

WalkInstructionResult IntegrationAttempt::isVfsCallUsingFD(ShadowInstruction* VFSCall, ShadowInstruction* FD, bool ignoreClose) {
  
  // Is VFSCall a call to open, read, seek or close that concerns FD?
  
  Function* Callee = getCalledFunction(VFSCall);
  if(!Callee)
    return WIRContinue;

  if(VFSCall == FD)
    return WIRStopThisPath;

  StringRef CalleeName = Callee->getName();
  if(CalleeName == "read") {
    
    ShadowValue readFD = VFSCall->getCallArgOperand(0);
    
    switch(aliasesFD(readFD, FD)) {
    case AliasAnalysis::MayAlias:
      LPDEBUG("Can't resolve VFS call because FD argument of " << itcache(*VFSCall) << " is unresolved\n");
      return WIRStopWholeWalk;
    case AliasAnalysis::NoAlias:
      LPDEBUG("Ignoring " << itcache(*VFSCall) << " which references a different file\n");
      return WIRContinue;
    case AliasAnalysis::MustAlias:
      return WIRStopThisPath;
    }
    
  }
  else if(CalleeName == "close") {

    // If we're walking backwards:
    // Finding this indicates we could double-close if this path were followed for real!
    // Walk through it to find its predecessors.
    // If we're walking forwards this is a chain ender.
    return ignoreClose ? WIRContinue : WIRStopThisPath;
    
  }
  else if(CalleeName == "llseek" || CalleeName == "lseek" || CalleeName == "lseek64") {
    
    ShadowValue seekFD = VFSCall->getCallArgOperand(0);
    
    switch(aliasesFD(seekFD, FD)) {
    case AliasAnalysis::MayAlias:
      return WIRStopWholeWalk;
    case AliasAnalysis::NoAlias:
      return WIRContinue;
    case AliasAnalysis::MustAlias:
      return WIRStopThisPath;
    }
    
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

bool IntegrationAttempt::VFSCallWillUseFD(const Instruction* I) {

  CallInst* CI = cast<CallInst>(const_cast<Instruction*>(I));

  {
    DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
    if(it != resolvedReadCalls.end())
      return false;
  }

  {
    DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
    if(it != resolvedSeekCalls.end())
      return !it->second.MayDelete;
  }

  {
    DenseMap<CallInst*, CloseFile>::iterator it = resolvedCloseCalls.find(CI);
    if(it != resolvedCloseCalls.end())
      return !(it->second.MayDelete && it->second.openArg->MayDelete && 
	       it->second.openInst->i.dieStatus == INSTSTATUS_DEAD);
  }

  return true;

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

bool IntegrationAttempt::isUnusedReadCall(ShadowInstruction* CI) {

  // Return true if CI is a read instruction that won't be in the final committed program:
  // this is true if it's zero-length or if there are no live users of the buffer it writes.
  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(cast<CallInst>(CI->invar->I));
  if(it != resolvedReadCalls.end()) {

    return CI->i.dieStatus & INSTSTATUS_UNUSED_WRITER || !it->second.readSize;

  }

  return false;

}

OpenStatus& IntegrationAttempt::getOpenStatus(CallInst* CI) {

  return *(forwardableOpenCalls[CI]);

}

//// Implement a forward walker that determines whether an open instruction may have any remaining uses.

class OpenInstructionUnusedWalker : public ForwardIAWalker {

  ShadowInstruction* OpenInst;

public:

  SmallVector<ShadowInstruction*, 4> CloseInstructions;
  SmallVector<ShadowInstruction*, 4> UserInstructions;
  bool residualUserFound;

  OpenInstructionUnusedWalker(ShadowInstruction* I) : ForwardIAWalker(I->invar->idx, I->parent, true), OpenInst(I), residualUserFound(false) { }

  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void*);
  virtual bool shouldEnterCall(ShadowInstruction*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);

};

bool OpenInstructionUnusedWalker::shouldEnterCall(ShadowInstruction* SI) {

  return callMayUseFD(SI, OpenInst);

}

bool OpenInstructionUnusedWalker::blockedByUnexpandedCall(ShadowInstruction* SI, void*) {

  residualUserFound = true;
  return true;

}

WalkInstructionResult OpenInstructionUnusedWalker::walkInstruction(ShadowInstruction* I, void*) {

  CallInst* CI = dyn_cast_inst<CallInst>(I);
  if(!CI)
    return WIRContinue;

  WalkInstructionResult WIR = I->parent->IA->isVfsCallUsingFD(I, OpenInst, false);

  if(WIR == WIRContinue)
    return WIR;
  else if(WIR == WIRStopThisPath) {

    // This call definitely uses this FD.
    if(!I->parent->IA->isResolvedVFSCall(CI)) {

      // But apparently we couldn't understand it. Perhaps some of its arguments are vague.
      residualUserFound = true;
      return WIRStopWholeWalk;

    }
    else {

      // We'll be able to remove this instruction: reads will be replaced by memcpy from constant buffer,
      // seeks will disappear entirely leaving just a numerical return value, closes will be deleted.
      Function* F = getCalledFunction(I);
      UserInstructions.push_back(I);

      if(F->getName() == "close") {
	CloseInstructions.push_back(I);
	return WIRStopThisPath;
      }
      else
	return WIRContinue;

    }

  }
  else {

    // This call may use this FD.
    residualUserFound = true;
    return WIRStopWholeWalk;

  }

}

//// Implement a closely related walker that determines whether a seek call can be elim'd or a read call's
//// implied SEEK_CUR can be omitted when residualising.

class SeekInstructionUnusedWalker : public ForwardIAWalker {

  ShadowInstruction* FD;

public:

  SmallVector<ShadowInstruction*, 4> SuccessorInstructions;
  bool seekNeeded;

  SeekInstructionUnusedWalker(ShadowInstruction* _FD, ShadowInstruction* Start) : ForwardIAWalker(Start->invar->idx, Start->parent, true), FD(_FD), seekNeeded(false) { }

  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void*);
  virtual bool shouldEnterCall(ShadowInstruction*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);

};

bool SeekInstructionUnusedWalker::shouldEnterCall(ShadowInstruction* SI) {

  return callMayUseFD(SI, FD);

}

bool SeekInstructionUnusedWalker::blockedByUnexpandedCall(ShadowInstruction* SI, void*) {

  seekNeeded = true;
  return true;

}

WalkInstructionResult SeekInstructionUnusedWalker::walkInstruction(ShadowInstruction* I, void*) {

  CallInst* CI = dyn_cast_inst<CallInst>(I);
  if(!CI)
    return WIRContinue;

  WalkInstructionResult WIR = I->parent->IA->isVfsCallUsingFD(I, FD, false);

  if(WIR == WIRContinue)
    return WIR;
  else if(WIR == WIRStopThisPath) {

    IntegrationAttempt* IA = I->parent->IA;

    // This call definitely uses this FD.
    if(!IA->isResolvedVFSCall(CI)) {

      // But apparently we couldn't understand it. Perhaps some of its arguments are vague.
      seekNeeded = true;
      return WIRStopWholeWalk;

    }
    else {

      SuccessorInstructions.push_back(I);
      return WIRStopThisPath;

    }

  }
  else {

    // This call may use this FD.
    seekNeeded = true;
    return WIRStopWholeWalk;

  }

}

void IntegrationAttempt::tryKillAllVFSOps() {

  for(uint32_t i = 0, ilim = nBBs; i != ilim; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

      ShadowInstruction* SI = &(BB->insts[j]);
      if(CallInst* CI = dyn_cast_inst<CallInst>(SI)) {

	{
	  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
	  if(it != resolvedReadCalls.end()) {
	    ShadowInstruction* FD = getFD(SI->getCallArgOperand(0));
	    if(!FD)
	      continue;
	    SeekInstructionUnusedWalker Walk(FD, SI);
	    Walk.walk();
	    if(!Walk.seekNeeded) {
	      it->second.needsSeek = false;
	    }	    
	    continue;
	  }
	}
	{
	  DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
	  if(it != resolvedSeekCalls.end()) {
	    ShadowInstruction* FD = getFD(SI->getCallArgOperand(0));
	    if(!FD)
	      continue;
	    SeekInstructionUnusedWalker Walk(FD, SI);
	    Walk.walk();
	    if(!Walk.seekNeeded) {
	      it->second.MayDelete = true;
	    }
	  }
	}

      }

    }

  }


  for(uint32_t i = 0, ilim = nBBs; i != ilim; ++i) {

    ShadowBB* BB = BBs[i];
    if(!BB)
      continue;

    for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

      ShadowInstruction* SI = &(BB->insts[j]);
      if(CallInst* CI = dyn_cast_inst<CallInst>(SI)) {

	DenseMap<CallInst*, OpenStatus*>::iterator it = forwardableOpenCalls.find(CI);
	if(it == forwardableOpenCalls.end())
	  continue;
	// Skip failed opens, we can always delete those
	if(!it->second->success)
	  continue;

	OpenInstructionUnusedWalker Walk(SI);
	Walk.walk();
	if(!Walk.residualUserFound) {

	  it->second->MayDelete = true;
	  for(unsigned i = 0; i < Walk.CloseInstructions.size(); ++i) {

	    Walk.CloseInstructions[i]->parent->IA->markCloseCall(cast_inst<CallInst>(Walk.CloseInstructions[i]));

	  }

	}

      }

    }

  }

  for(DenseMap<CallInst*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {
    if(ignoreIAs.count(it->first))
      continue;
    it->second->tryKillAllVFSOps();
  }

  for(DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {
    if(ignorePAs.count(it->first))
      continue;
    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->tryKillAllVFSOps();
  }

}

void IntegrationAttempt::markCloseCall(CallInst* CI) {

  resolvedCloseCalls[CI].MayDelete = true;

}
