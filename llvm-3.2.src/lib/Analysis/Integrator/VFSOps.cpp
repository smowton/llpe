
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

FDStore* ShadowBB::getWritableFDStore() {

  fdStore = fdStore->getWritable();
  return fdStore;

}

void FDStoreMerger::merge2(FDStore* mergeTo, FDStore* mergeFrom)  {

  // Simple merge rule: FDs only defined on one path or the other go away entirely,
  // FDs with conflicting positions go to pos -1 (unknown), all others stay.

  mergeTo->fds.resize(std::min(mergeTo->fds.size(), mergeFrom->fds.size()));

  for(uint32_t i = 0, ilim = mergeTo->fds.size(); i != ilim; ++i) {

    if(mergeFrom->fds[i].pos != mergeTo->fds[i].pos)
      mergeTo->fds[i].pos = (uint64_t)-1;

  }

}

void FDStoreMerger::doMerge() {

  if(incomingBlocks.empty())
    return;

  // Discard wholesale block duplicates:
  SmallVector<FDStore*, 4> incomingStores;
  incomingStores.reserve(std::distance(incomingBlocks.begin(), incomingBlocks.end()));

  for(SmallVector<ShadowBB*, 4>::iterator it = incomingBlocks.begin(), itend = incomingBlocks.end();
      it != itend; ++it) {

    incomingStores.push_back((*it)->fdStore);

  }
  
  std::sort(incomingStores.begin(), incomingStores.end());
  typename SmallVector<FDStore*, 4>::iterator uniqend = std::unique(incomingStores.begin(), incomingStores.end());

  FDStore* retainMap;
  
  if(std::distance(incomingStores.begin(), uniqend) > 1) {

    // At least some stores differ; need to make a new one.

    // See if we can avoid a CoW break by using a writable incoming store as the target.
    for(typename SmallVector<FDStore*, 4>::iterator it = incomingStores.begin(); it != uniqend; ++it) {
      
      if((*it)->refCount == 1) {

	if(it != incomingStores.begin())
	  std::swap(incomingStores[0], *it);
	break;

      }

    }

    // Position 0 is the target; the rest should be merged in. CoW break if still necessary:
    // Note retainMap is set to the original map rather than the new one as the CoW break drops
    // a reference to it so it should not be unref'd again below.
    retainMap = incomingStores[0];
    FDStore* mergeMap = incomingStores[0] = incomingStores[0]->getWritable();

    SmallVector<FDStore*, 4>::iterator firstMergeFrom = incomingStores.begin();
    ++firstMergeFrom;

    for(SmallVector<FDStore*, 4>::iterator it = firstMergeFrom; it != uniqend; ++it) {

      merge2(mergeMap, *it);

    }

    newStore = mergeMap;

  }
  else {

    // No stores differ; just use #0
    newStore = incomingStores[0];
    retainMap = newStore;

  }

  // Drop refs against each incoming store apart from the store that was either used or
  // implicitly unref'd as part of the CoW break at getWritableFrameMap.

  for(SmallVector<ShadowBB*, 4>::iterator it = incomingBlocks.begin(), itend = incomingBlocks.end();
      it != itend; ++it) {

    FDStore* thisMap = (*it)->fdStore;
    if(thisMap == retainMap)
      retainMap = 0;
    else
      thisMap->dropReference();

  }

}

void llvm::doBlockFDStoreMerge(ShadowBB* BB) {

  // We're entering BB; one or more live predecessor blocks exist and we must produce an appropriate
  // localStore from them.

  LFV3(errs() << "Start block store merge\n");

  // This BB is a merge of all that has gone before; merge to values' base stores
  // rather than a local map.

  FDStoreMerger V;
  BB->IA->visitNormalPredecessorsBW(BB, &V, /* ctx = */0);
  V.doMerge();
  BB->fdStore = V.newStore;

}

void llvm::doCallFDStoreMerge(ShadowBB* CallerBB, InlineAttempt* CallIA) {

  FDStoreMerger V;
  CallIA->visitLiveReturnBlocks(V);
  V.doMerge();

  CallerBB->fdStore = V.newStore;

}

static bool filenameIsForbidden(std::string& s) {

  return s.find("/proc/") == 0 || s.find("/sys/") == 0 || s.find("/dev/") == 0;

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

	    FDStore* FDS = SI->parent->getWritableFDStore();
	    uint32_t newId = pass->fds.size();
	    pass->fds.push_back(FDGlobalState(SI));
	    if(FDS->fds.size() <= newId)
	      FDS->fds.resize(newId + 1);
	    FDS->fds[newId] = FDState(Filename);
	    
	    cast<ImprovedValSetSingle>(SI->i.PB)->set(ImprovedVal(ShadowValue::getFdIdx(newId)), ValSetTypeFD);

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

static uint32_t getFD(ShadowValue V) {

  if(V.isVal())
    return 0;

  ImprovedValSetSingle VPB;
  if(!getImprovedValSetSingle(V, VPB))
    return 0;

  if(VPB.Overdef || VPB.Values.size() != 1 || VPB.SetType != ValSetTypeFD)
    return 0;

  return VPB.Values[0].V.u.PtrOrFd.idx;

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

  FDStore* fdStore = SI->parent->getWritableFDStore();

  // All calls beyond here operate on FDs.

  uint32_t FD = getFD(SI->getCallArgOperand(0));
 
  // Operates on an unknown FD?
  if(FD == (uint32_t)-1) {
    fdStore->fds.clear();
    return true;
  }

  // Operates on an FD not opened on this path?
  if(SI->parent->fdStore->fds.size() <= FD)
    return true;

  FDState& FDS = SI->parent->fdStore->fds[FD];

  if(F->getName() == "isatty") {

    // OpenStatus items like this are always real files, not TTYs, for now.
    setReplacement(SI, ConstantInt::get(FT->getReturnType(), 0));
    return true;

  }
  else if(F->getName() == "llseek" || F->getName() == "lseek" || F->getName() == "lseek64") {

    // Check for needed values now:
    Constant* whence = getConstReplacement(SI->getCallArgOperand(2));
    Constant* newOffset = getConstReplacement(SI->getCallArgOperand(1));
    
    if((!newOffset) || (!whence)) {
      FDS.pos = (uint32_t)-1;
      return true;
    }

    uint64_t intOffset = cast<ConstantInt>(newOffset)->getLimitedValue();
    int32_t seekWhence = (int32_t)cast<ConstantInt>(whence)->getSExtValue();
    
    switch(seekWhence) {
    case SEEK_CUR:
      {
	// Unknown position?
	if(FDS.pos == (uint64_t)-1)
	  return true;
	intOffset += FDS.pos;
	break;
      }
    case SEEK_END:
      {
	struct stat file_stat;
	if(::stat(FDS.filename.c_str(), &file_stat) == -1) {
	  
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

    noteVFSOp();

    // Doesn't matter what came before, resolve this call here.
    setReplacement(SI, ConstantInt::get(FT->getParamType(1), intOffset));
    resolveSeekCall(SI, SeekFile(FDS.filename, intOffset));
    FDS.pos = intOffset;
    return true;

  }
  else if(F->getName() == "fstat") {

    return executeStatCall(SI, F, FDS.filename);

  }
  else if(F->getName() == "close") {

    noteVFSOp();
    setReplacement(SI, ConstantInt::get(FT->getReturnType(), 0));
    return true;

  }
  else if(F->getName() == "read") {

    ShadowValue readBytes = SI->getCallArgOperand(2);
    ConstantInt* intBytes = cast_or_null<ConstantInt>(getConstReplacement(readBytes));
    if(!intBytes) {
      FDS.pos = (uint64_t)-1;
      return true;
    }
    
    int64_t cBytes = intBytes->getLimitedValue();

    if(filenameIsForbidden(FDS.filename)) {
      FDS.pos = (uint64_t)-1;
      return true;
    }

    struct stat file_stat;
    if(::stat(FDS.filename.c_str(), &file_stat) == -1) {
      LPDEBUG("Failed to stat " << OS.Name << "\n");
      FDS.pos = (uint64_t)-1;
      return true;
    }

    if(!(file_stat.st_mode & S_IFREG)) {
      FDS.pos = (uint64_t)-1;
      return true;
    }

    int64_t bytesAvail = file_stat.st_size - FDS.pos;
    if(cBytes > bytesAvail) {
      LPDEBUG("Desired read of " << cBytes << " truncated to " << bytesAvail << " (EOF)\n");
      cBytes = bytesAvail;
    }

    // OK, we know what this read operation does. Record that and queue another exploration from this point.
    LPDEBUG("Successfully resolved " << itcache(*SI) << " which reads " << cBytes << " bytes\n");
    
    noteVFSOp();

    resolveReadCall(SI, ReadFile(FDS.filename, FDS.pos, cBytes));
    
    // The number of bytes read is also the return value of read.
    setReplacement(SI, ConstantInt::get(Type::getInt64Ty(F->getContext()), cBytes));

    executeReadInst(SI, FDS.filename, FDS.pos, cBytes);

    FDS.pos += cBytes;

    noteLLIODependency(FDS.filename);
    SI->needsRuntimeCheck = RUNTIME_CHECK_SPECIAL;

  }

  return true;
  
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

void IntegrationAttempt::resolveReadCall(ShadowInstruction* CI, struct ReadFile RF) {

  pass->resolvedReadCalls[CI] = RF;

}

void IntegrationAttempt::resolveSeekCall(ShadowInstruction* CI, struct SeekFile SF) {

  pass->resolvedSeekCalls[CI] = SF;

}

bool IntegrationAttempt::isResolvedVFSCall(ShadowInstruction* I) {
  
  if(inst_is<CallInst>(I)) {

    return pass->forwardableOpenCalls.count(I) || pass->resolvedReadCalls.count(I) || pass->resolvedSeekCalls.count(I);

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
	    int32_t FD = getFD(SI->getCallArgOperand(0));
	    if(FD == -1)
	      continue;
	    SeekInstructionUnusedWalker Walk(pass->fds[FD].SI, SI);
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
	    int32_t FD = getFD(SI->getCallArgOperand(0));
	    if(FD == -1)
	      continue;
	    SeekInstructionUnusedWalker Walk(pass->fds[FD].SI, SI);
	    Walk.walk();
	    if(!Walk.seekNeeded) {
	      it->second.MayDelete = true;
	    }
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
