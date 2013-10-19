
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
#include <stdio.h>

// Implement a backward walker to identify a VFS operation's predecessor, and a forward walker to identify open instructions
// which can be shown pointless because along all paths it ends up at a close instruction.

using namespace llvm;

bool IntegrationAttempt::getConstantString(ShadowValue Ptr, ShadowInstruction* SearchFrom, std::string& Result) {

  StringRef RResult;
  if(Ptr.isVal() && getConstantStringInfo(cast<Constant>(Ptr.getVal()), RResult)) {
    Result = RResult.str();
    return true;
  }

  ShadowValue StrBase;
  int64_t StrOffset;
  if(!getBaseAndConstantOffset(Ptr, StrBase, StrOffset))
    return false;

  if(ShadowGV* G = StrBase.getGV()) {
      
    GlobalVariable* GV = G->G;
    if(GV->isConstant()) {
      Type* Int8Ptr = Type::getInt8PtrTy(GV->getContext());
      Constant* QueryCE = getGVOffset(GV, StrOffset, Int8Ptr);
      if(getConstantStringInfo(QueryCE, RResult)) {
	Result = RResult.str();
	return true;
      }
    }

  }

  Result = "";
  
  // Try to LF one character at a time until we get null or a failure.

  LPDEBUG("forwarding off " << itcache(StrBase) << "\n");

  Type* byteType = Type::getInt8Ty(SearchFrom->invar->I->getContext());

  bool success = true;

  for(; success; ++StrOffset) {

    // Create a GEP to access the next byte:

    //std::string* fwdError = 0;

    ImprovedValSetSingle byte;
    readValRange(StrBase, StrOffset, 1, SearchFrom->parent, byte, 0, 0 /* fwdError */);
    if(byte.Overdef || byte.SetType != ValSetTypeScalar || byte.Values.size() != 1) {

      DEBUG(dbgs() << "Open forwarding error: " << fwdError << "\n");
      success = false;
      
    }
    else {

      byte.coerceToType(byteType, 1, 0);

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

  if(Function *SysOpen = F.getParent()->getFunction("open")) {
    const FunctionType *FT = SysOpen->getFunctionType();
    if (FT->getNumParams() == 2 && FT->getReturnType()->isIntegerTy(32) &&
        FT->getParamType(0)->isPointerTy() &&
        FT->getParamType(1)->isIntegerTy(32) &&
	FT->isVarArg()) {

      if(Function* FCalled = getCalledFunction(SI)) {

	if(FCalled == SysOpen) {

	  if(SI->i.PB)
	    deleteIV(SI->i.PB);
	  SI->i.PB = newOverdefIVS();

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

	  bool exists = sys::Path(Filename).exists();
	  pass->forwardableOpenCalls[SI] = new OpenStatus(Filename, exists);
	  if(exists) {
	    cast<ImprovedValSetSingle>(SI->i.PB)->set(ImprovedVal(ShadowValue(SI)), ValSetTypeFD);
	    LPDEBUG("Successfully promoted open of file " << Filename << ": queueing initial forward attempt\n");
	  }
	  else {
	    Constant* negOne = ConstantInt::get(SI->invar->I->getType(), (uint64_t)-1, true);
	    cast<ImprovedValSetSingle>(SI->i.PB)->set(ImprovedVal(ShadowValue(negOne)), ValSetTypeScalar);
	    LPDEBUG("Open of " << Filename << " returning ENOENT\n");
	  }

	  // Can't share functions that open() or we'll confuse the two open points.
	  noteVFSOp();

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
    : BackwardIAWalker(CI->invar->idx, CI->parent, /*skipFirst=*/true, 0, 0, /*doIgnoreEdges=*/true), SourceOp(CI), FD(_FD),
      uniqueIncomingOffset(-1) { 
    IA = SourceOp->parent->IA;
  }
  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void*);
  virtual bool shouldEnterCall(ShadowInstruction*, void*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);

};

WalkInstructionResult FindVFSPredecessorWalker::walkInstruction(ShadowInstruction* I, void*) {

  // Determine whether this instruction is a VFS call using our FD.
  // No need to worry about call instructions, just return WIRContinue and we'll enter it if need be.

  IntegrationAttempt* IA = I->parent->IA;

  if(inst_is<CallInst>(I)) {

    WalkInstructionResult WIR = IA->isVfsCallUsingFD(I, FD, true);
    if(WIR == WIRStopThisPath) {

      // Call definitely uses this FD. Find the incoming offset if possible.
      int64_t incomingOffset = IA->tryGetIncomingOffset(I);
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

  ImprovedValSetSingle VPB;
  if(!getImprovedValSetSingle(V, VPB))
    return 0;

  if(VPB.Overdef || VPB.Values.size() != 1 || VPB.SetType != ValSetTypeFD)
    return 0;

  return VPB.Values[0].V.getInst();

}

static AliasAnalysis::AliasResult aliasesFD(ShadowValue V, ShadowInstruction* FD) {

  if(V.isVal())
    return AliasAnalysis::NoAlias;

  ImprovedValSetSingle VPB;
  if(!getImprovedValSetSingle(V, VPB))
    return AliasAnalysis::MayAlias;

  if(VPB.Overdef || VPB.Values.size() == 0)
    return AliasAnalysis::MayAlias;

  if(VPB.SetType != ValSetTypeFD)
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
  
  Function* calledF = getCalledFunction(SI);

  // None of the blacklisted syscalls not accounted for under vfsCallBlocksOpen mess with FDs in a way that's important to us.
  if(IntrinsicInst* II = dyn_cast<IntrinsicInst>(CI)) {

    switch(II->getIntrinsicID()) {

    case Intrinsic::vastart:
    case Intrinsic::vacopy:
    case Intrinsic::vaend:
    case Intrinsic::memcpy:
    case Intrinsic::memmove:
    case Intrinsic::memset:
    case Intrinsic::dbg_declare:
    case Intrinsic::dbg_value:
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
    case Intrinsic::invariant_start:
    case Intrinsic::invariant_end:
      return false;

    default:
      break;

    }

  }
  else if(calledF && functionIsBlacklisted(calledF))
   return false;
  
  return true;

}

bool FindVFSPredecessorWalker::shouldEnterCall(ShadowInstruction* SI, void*) {

  return callMayUseFD(SI, FD);
	    
}

bool FindVFSPredecessorWalker::blockedByUnexpandedCall(ShadowInstruction* SI, void*) {

  // If we get to here and the call is a syscall then it doesn't alter the FD position.
  if(Function* F = getCalledFunction(SI)) {

    if(GlobalIHP->getMRInfo(F))
      return false;

    if(SpecialFunctionMap.count(F))
      return false;

    if(GlobalIHP->specialLocations.count(F))
      return false;

  }

  uniqueIncomingOffset = -1;
  return true;

}

void llvm::noteLLIODependency(std::string& Filename) {
  
  std::vector<std::string>::iterator findit = 
    std::find(GlobalIHP->llioDependentFiles.begin(), GlobalIHP->llioDependentFiles.end(), Filename);

  if(findit == GlobalIHP->llioDependentFiles.end())
    GlobalIHP->llioDependentFiles.push_back(Filename);
  
}

bool IntegrationAttempt::executeStatCall(ShadowInstruction* SI, Function* F, std::string& Filename) {

  struct stat file_stat;
  int stat_ret = ::stat(Filename.c_str(), &file_stat);

  if(stat_ret == -1 && errno != ENOENT)
    return false;

  noteLLIODependency(Filename);
  SI->needsRuntimeCheck = RUNTIME_CHECK_SPECIAL;

  if(stat_ret == 0) {

    // Populate stat structure at spec time:
    Constant* Data = 
      ConstantDataArray::get(SI->invar->I->getContext(), 
			     ArrayRef<uint8_t>((uint8_t*)&file_stat, sizeof(struct stat)));
    
    ImprovedValSetSingle PtrSet;
    ImprovedValSetSingle ValSet;
    ShadowValue PtrOp = SI->getOperand(1);
    
    getImprovedValSetSingle(PtrOp, PtrSet);
    ValSet.set(ImprovedVal(ShadowValue(Data)), ValSetTypeScalar);

    executeWriteInst(&PtrOp, PtrSet, ValSet, sizeof(struct stat), SI);

  }

  const FunctionType *FT = F->getFunctionType();
  setReplacement(SI, ConstantInt::get(FT->getReturnType(), stat_ret));

  return true;

}

// Return value: is this a VFS call (regardless of whether we resolved it successfully)
bool IntegrationAttempt::tryResolveVFSCall(ShadowInstruction* SI) {

  Function* F = getCalledFunction(SI);
  if(!F)
    return false;

  const FunctionType *FT = F->getFunctionType();
  
  if(!(F->getName() == "read" || F->getName() == "llseek" || F->getName() == "lseek" || 
       F->getName() == "lseek64" || F->getName() == "close" || F->getName() == "stat" ||
       F->getName() == "fstat" || F->getName() == "isatty"))
    return false;

  if(SI->i.PB)
    deleteIV(SI->i.PB);
  SI->i.PB = newOverdefIVS();

  // noteVFSOp() calls are inserted below wherever a resolution depends on
  // not just the FD being used but its position, as this state is not explicitly
  // maintained at the moment. Eventually FDs should occupy an FD store rather than
  // using a backward walk, akin to the evolution of the load resolution code,
  // and this limitation can go away.

  if(F->getName() == "stat") {

    // TODO: Add LF resolution code notifying file size. All users so far have just
    // used stat as an existence test. Similarly set errno = ENOENT as appropriate.

    // Return false in all cases so that we fall through to handleUnexpandedCall and clobber the stat buffer.

    std::string Filename;
    if (!getConstantString(SI->getCallArgOperand(0), SI, Filename)) {
      LPDEBUG("Can't resolve stat call " << itcache(SI) << " because its filename argument is unresolved\n");
      return false;
    }

    return executeStatCall(SI, F, Filename);

  }

  // All calls beyond here operate on FDs.
  ShadowInstruction* OpenCall = getFD(SI->getCallArgOperand(0));
  if(!OpenCall)
    return true;

  OpenStatus& OS = OpenCall->parent->IA->getOpenStatus(OpenCall);

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

      noteVFSOp();

      // Doesn't matter what came before, resolve this call here.
      setReplacement(SI, ConstantInt::get(FT->getParamType(1), intOffset));
      resolveSeekCall(SI, SeekFile(&OS, intOffset));
      return true;

    }
    // Else fall through to the walk phase.

  }
  else if(F->getName() == "fstat") {

    return executeStatCall(SI, F, OS.Name);

  }
  else if(F->getName() == "close") {

    noteVFSOp();

    pass->resolvedCloseCalls[SI] = CloseFile(&OS, OpenCall);    
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
    LPDEBUG("Successfully resolved " << itcache(*SI) << " which reads " << cBytes << " bytes\n");
    
    noteVFSOp();

    resolveReadCall(SI, ReadFile(&OS, Walk.uniqueIncomingOffset, cBytes));
    
    // The number of bytes read is also the return value of read.
    setReplacement(SI, ConstantInt::get(Type::getInt64Ty(F->getContext()), cBytes));

    executeReadInst(SI, OS, Walk.uniqueIncomingOffset, cBytes);

    noteLLIODependency(OS.Name);
    SI->needsRuntimeCheck = RUNTIME_CHECK_SPECIAL;

  }
  else {

    // It's a seek call, with SEEK_CUR.
    Constant* newOffset = getConstReplacement(SI->getCallArgOperand(1));
    int64_t intOffset = cast<ConstantInt>(newOffset)->getLimitedValue();
    intOffset += Walk.uniqueIncomingOffset;

    noteVFSOp();

    resolveSeekCall(SI, SeekFile(&OS, intOffset));

    // Return value: new file offset.
    setReplacement(SI, ConstantInt::get(FT->getParamType(1), intOffset));

  }

  return true;
  
}

int64_t IntegrationAttempt::tryGetIncomingOffset(ShadowInstruction* CI) {

  if(pass->forwardableOpenCalls.count(CI))
    return 0;

  {
    DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(CI);
    if(it != pass->resolvedReadCalls.end())
      return it->second.incomingOffset + it->second.readSize;
  }

  {
    DenseMap<ShadowInstruction*, SeekFile>::iterator it = pass->resolvedSeekCalls.find(CI);
    if(it != pass->resolvedSeekCalls.end())
      return it->second.newOffset;
  } 

  return -1;

}

ReadFile* IntegrationAttempt::tryGetReadFile(ShadowInstruction* CI) {

  DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(CI);
  if(it != pass->resolvedReadCalls.end())
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
    case AliasAnalysis::PartialAlias:
      return WIRStopWholeWalk;
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
    case AliasAnalysis::PartialAlias:
      return WIRStopWholeWalk;
    }
    
  }
  
  return WIRContinue;
  
}

bool IntegrationAttempt::isCloseCall(ShadowInstruction* CI) {

  return pass->resolvedCloseCalls.count(CI);

}

void IntegrationAttempt::resolveReadCall(ShadowInstruction* CI, struct ReadFile RF) {

  pass->resolvedReadCalls[CI] = RF;

}

void IntegrationAttempt::resolveSeekCall(ShadowInstruction* CI, struct SeekFile SF) {

  pass->resolvedSeekCalls[CI] = SF;

}

bool IntegrationAttempt::isResolvedVFSCall(ShadowInstruction* I) {
  
  if(inst_is<CallInst>(I)) {

    return pass->forwardableOpenCalls.count(I) || pass->resolvedReadCalls.count(I) || pass->resolvedSeekCalls.count(I) || pass->resolvedCloseCalls.count(I);

  }

  return false;

}

bool IntegrationAttempt::VFSCallWillUseFD(ShadowInstruction* CI) {

  {
    DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(CI);
    if(it != pass->resolvedReadCalls.end()) {
      return it->second.needsSeek;
    }
  }

  {
    DenseMap<ShadowInstruction*, SeekFile>::iterator it = pass->resolvedSeekCalls.find(CI);
    if(it != pass->resolvedSeekCalls.end())
      return !it->second.MayDelete;
  }

  {
    DenseMap<ShadowInstruction*, CloseFile>::iterator it = pass->resolvedCloseCalls.find(CI);
    if(it != pass->resolvedCloseCalls.end())
      return !(it->second.MayDelete && it->second.openArg->MayDelete && 
	       it->second.openInst->dieStatus == INSTSTATUS_DEAD);
  }

  return true;

}

bool IntegrationAttempt::isUnusedReadCall(ShadowInstruction* CI) {

  // Return true if CI is a read instruction that won't be in the final committed program:
  // this is true if it's zero-length or if there are no live users of the buffer it writes.
  DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(CI);
  if(it != pass->resolvedReadCalls.end()) {

    return CI->dieStatus & INSTSTATUS_UNUSED_WRITER || !it->second.readSize;

  }

  return false;

}

OpenStatus& IntegrationAttempt::getOpenStatus(ShadowInstruction* CI) {

  return *(pass->forwardableOpenCalls[CI]);

}

//// Implement a forward walker that determines whether an open instruction may have any remaining uses.

class OpenInstructionUnusedWalker : public ForwardIAWalker {

  ShadowInstruction* OpenInst;

public:

  SmallVector<ShadowInstruction*, 4> CloseInstructions;
  SmallVector<ShadowInstruction*, 4> UserInstructions;
  bool residualUserFound;

  OpenInstructionUnusedWalker(ShadowInstruction* I) : ForwardIAWalker(I->invar->idx, I->parent, true, 0, false), OpenInst(I), residualUserFound(false) { }

  virtual WalkInstructionResult walkInstruction(ShadowInstruction*, void*);
  virtual bool shouldEnterCall(ShadowInstruction*, void*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);
  virtual void hitIgnoredEdge() { residualUserFound = true; }
  virtual bool shouldContinue() { return !residualUserFound; }

};

bool OpenInstructionUnusedWalker::shouldEnterCall(ShadowInstruction* SI, void*) {

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
    if(!I->parent->IA->isResolvedVFSCall(I)) {

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
  virtual bool shouldEnterCall(ShadowInstruction*, void*);
  virtual bool blockedByUnexpandedCall(ShadowInstruction*, void*);

};

bool SeekInstructionUnusedWalker::shouldEnterCall(ShadowInstruction* SI, void*) {

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
    if(!IA->isResolvedVFSCall(I)) {

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
      if(inst_is<CallInst>(SI)) {

	{
	  DenseMap<ShadowInstruction*, ReadFile>::iterator it = pass->resolvedReadCalls.find(SI);
	  if(it != pass->resolvedReadCalls.end()) {
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
	  DenseMap<ShadowInstruction*, SeekFile>::iterator it = pass->resolvedSeekCalls.find(SI);
	  if(it != pass->resolvedSeekCalls.end()) {
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
      if(inst_is<CallInst>(SI)) {

	DenseMap<ShadowInstruction*, OpenStatus*>::iterator it = pass->forwardableOpenCalls.find(SI);
	if(it == pass->forwardableOpenCalls.end())
	  continue;
	// Skip failed opens, we can always delete those
	if(!it->second->success)
	  continue;

	OpenInstructionUnusedWalker Walk(SI);
	Walk.walk();
	if(!Walk.residualUserFound) {

	  it->second->MayDelete = true;
	  for(unsigned i = 0; i < Walk.CloseInstructions.size(); ++i) {

	    Walk.CloseInstructions[i]->parent->IA->markCloseCall(Walk.CloseInstructions[i]);

	  }

	}

      }

    }

  }

  for(DenseMap<ShadowInstruction*, InlineAttempt*>::const_iterator it = inlineChildren.begin(), it2 = inlineChildren.end(); it != it2; ++it) {
    if(!it->second->isEnabled())
      continue;
    it->second->tryKillAllVFSOps();
  }

  for(DenseMap<const Loop*, PeelAttempt*>::const_iterator it = peelChildren.begin(), it2 = peelChildren.end(); it != it2; ++it) {
    if(!it->second->isEnabled())
      continue;
    for(unsigned i = 0; i < it->second->Iterations.size(); ++i)
      it->second->Iterations[i]->tryKillAllVFSOps();
  }

}

void IntegrationAttempt::markCloseCall(ShadowInstruction* CI) {

  pass->resolvedCloseCalls[CI].MayDelete = true;

}

bool llvm::getFileBytes(std::string& strFileName, uint64_t realFilePos, uint64_t realBytes, std::vector<Constant*>& arrayBytes, LLVMContext& Context, std::string& errors) {

  FILE* fp = fopen(strFileName.c_str(), "r");
  if(!fp) {
    errors = "Couldn't open " + strFileName + ": " + strerror(errno);
    return false;
  }

  int rc = fseek(fp, realFilePos, SEEK_SET);
  if(rc == -1) {
    errors = "Couldn't seek " + strFileName + ": " + strerror(errno);
    return false;
  }

  uint64_t bytesRead = 0;
  uint8_t buffer[4096];
  Type* charType = IntegerType::get(Context, 8);
  while(bytesRead < realBytes) {
    uint64_t toRead = realBytes - bytesRead;
    toRead = std::min(toRead, (uint64_t)4096);
    size_t reallyRead = fread(buffer, 1, (size_t)toRead, fp);
    if(reallyRead == 0) {
      if(feof(fp))
        break;
      else {
        errors = "Error reading from " + strFileName + ": " + strerror(errno);
        fclose(fp);
        return false;
      }
    }
    for(size_t i = 0; i < reallyRead; i++) {
      Constant* byteAsConst = ConstantInt::get(charType, buffer[i]);
      arrayBytes.push_back(byteAsConst);
    }
    bytesRead += reallyRead;
  }

  fclose(fp);

  return true;

}
