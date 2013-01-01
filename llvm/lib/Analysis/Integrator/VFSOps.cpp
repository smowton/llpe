
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

using namespace llvm;

void IntegrationAttempt::tryPromoteOpenCall(CallInst* CI) {
  
  if(!certainBlocks.count(CI->getParent())) {
    LPDEBUG("Won't promote open call " << itcache(*CI) << " yet: not certain to execute\n");
    return;
  }

  if(forwardableOpenCalls.count(CI)) {
    LPDEBUG("Open call " << itcache(*CI) << ": already promoted\n");
    return;
  }
  
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
	      return;
	    }
	  }
	  else {
	    LPDEBUG("Can't promote open call " << itcache(*CI) << " because its mode argument can't be resolved\n");
	    return;
	  }
	  
	  ValCtx NameArg = getReplacement(CI->getArgOperand(0));
	  std::string Filename;
	  if (!GetConstantStringInfo(NameArg.first, Filename)) {
	    LPDEBUG("Can't promote open call " << itcache(*CI) << " because its filename argument is unresolved\n");
	    return;
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
	  forwardableOpenCalls[CI] = new OpenStatus(make_vc(CI, this), Filename, exists, FDEscapes);
	  if(exists) {
	    LPDEBUG("Successfully promoted open of file " << Filename << ": queueing initial forward attempt\n");
	    pass->queueOpenPush(make_vc(CI, this), make_vc(CI, this));
	  }
	  else {
	    LPDEBUG("Open of " << Filename << " returning ENOENT\n");
	  }

	  // Also investigate users, since we now know it'll emit non-negative FD or return -1 with ENOENT.
	  investigateUsers(CI);
      
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

}

void IntegrationAttempt::tryPushOpen(CallInst* OpenI, ValCtx OpenProgress) {

  OpenStatus& OS = *(forwardableOpenCalls[OpenI]);

  if(OS.LatestResolvedUser != OpenProgress) {

    LPDEBUG("Skipping as call has been pushed in the meantime\n");
    return;

  }

  // Try to follow the trail from LastResolvedUser forwards.

  LPDEBUG("Trying to extend VFS op chain for " << itcache(*OpenI) << " from " << itcache(OpenProgress) << "\n");

  ValCtx NextStart = OpenProgress;
  bool skipFirst = true;
  SmallSet<ValCtx, 8> Visited;
  SmallVector<ValCtx, 8> Worklist1;
  SmallVector<ValCtx, 8> Worklist2;
  SmallVector<ValCtx, 2> Defs;
  SmallVector<ValCtx, 2> Clobbers;
  bool CFGTrouble = false;
  
  SmallVector<ValCtx, 8>* PList = &Worklist1;  
  SmallVector<ValCtx, 8>* CList = &Worklist2;

  std::vector<IntegrationAttempt*> Traversed;

  Visited.insert(NextStart);
  PList->push_back(NextStart);

  while((PList->size() || CList->size()) && (Defs.size() + Clobbers.size() < 2)) {

    for(unsigned i = 0; i < CList->size(); ++i) {

      ValCtx ThisStart = (*CList)[i];
      Traversed.push_back(ThisStart.second);
      NextStart = ThisStart;
      // Return false means do not explore successors; this block contains a definition or clobber.
      if(!NextStart.second->tryPushOpenFrom(NextStart, make_vc(OpenI, this), OpenProgress, OS, skipFirst, Defs, Clobbers))
	continue;
      if(NextStart != VCNull) {

	// Found function entry or exit, queue successor:
	if(Visited.insert(NextStart))
	  PList->push_back(NextStart);

      }
      else {
      
	ThisStart.second->queueSuccessorVCs(make_vc(OpenI, this), OpenProgress, cast<Instruction>(ThisStart.first)->getParent(), Visited, *PList, CFGTrouble);

      }

      skipFirst = false;

    }

    CList->clear();
    std::swap(PList, CList);

  }

  if(Defs.size() + Clobbers.size() > 1)
    CFGTrouble = true;

  LPDEBUG(Clobbers.size() + Defs.size() << "\n");
  for(unsigned i = 0; i < Clobbers.size(); ++i) {
    LPDEBUG("Clobber: " << itcache(Clobbers[i]) << "\n");
  }

  for(unsigned i = 0; i < Defs.size(); ++i) {
    LPDEBUG("Def: " <<  itcache(Defs[i]) << "\n");
  }

  if(CFGTrouble) {

    std::sort(Traversed.begin(), Traversed.end());

    std::vector<IntegrationAttempt*>::iterator it, it2;
    it2 = std::unique(Traversed.begin(), Traversed.end());

    for(it = Traversed.begin(); it != it2; ++it)
      (*it)->addBlockedOpen(make_vc(OpenI, this), OpenProgress);

  }
  else if(Defs.size() == 1 && Clobbers.size() == 0) {

    Defs[0].second->setVFSSuccessor(cast<CallInst>(Defs[0].first), make_vc(OpenI, this), OpenProgress, OS);

  }
  
}

// Called in the context of Start.second. OpenInst is the open instruction we're pursuing, and the context where OS is stored.
// ReadInst is the entry in the chain of VFS operations that starts at OpenInst.
bool IntegrationAttempt::tryPushOpenFrom(ValCtx& Start, ValCtx OpenInst, ValCtx ReadInst, OpenStatus& OS, bool skipFirst, SmallVector<ValCtx, 2>& Defs, SmallVector<ValCtx, 2>& Clobbers) {

  Instruction* StartI = cast<Instruction>(Start.first);
  BasicBlock* BB = StartI->getParent();
  BasicBlock::iterator BI(StartI);

  Start = VCNull;

  for(; BI != BB->end(); ++BI) {

    if(!skipFirst) {

      if(CallInst* CI = dyn_cast<CallInst>(BI)) {

	bool isVFSCall, shouldRequeue;
	if(vfsCallBlocksOpen(CI, OpenInst, ReadInst, OS, isVFSCall, shouldRequeue)) {
	  if(shouldRequeue) {
	    // Queue to retry when we know more about the call.
	    LPDEBUG("Inst blocked on " << itcache(*CI) << "\n");
	    InstBlockedOpens[CI].push_back(std::make_pair(OpenInst, ReadInst));
	    Clobbers.push_back(make_vc(CI, this));
	  }
	  else {
	    Defs.push_back(make_vc(CI, this));
	  }
	  return false;
	}

	if(!isVFSCall) {

	  // This call cannot affect the FD we're pursuing unless (a) it uses the FD, or (b) the FD escapes (is stored) and the function is non-pure.
	  bool callMayUseFD = false;

	  Function* calledF = getCalledFunction(CI);

	  // None of the blacklisted syscalls not accounted for under vfsCallBlocksOpen mess with FDs in a way that's important to us.
	  bool ignore = false;
	  if(isa<MemIntrinsic>(CI) || isa<DbgInfoIntrinsic>(CI) || (calledF && functionIsBlacklisted(calledF)))
	    ignore = true;
	  else if(OS.FDEscapes && ((!calledF) || !calledF->doesNotAccessMemory()))
	    callMayUseFD = true;

	  if((!callMayUseFD) && (!ignore)) {

	    for(unsigned i = 0; i < CI->getNumArgOperands() && !callMayUseFD; ++i) {

	      ValCtx ArgVC = getReplacement(CI->getArgOperand(i));
	      if(ArgVC == OpenInst)
		callMayUseFD = true;
	      if(isUnresolved(CI->getArgOperand(i))) {
		LPDEBUG("Assuming " << itcache(*CI) << " may use " << itcache(OpenInst) << " due to unresolved argument " << itcache(ArgVC) << "\n");
		callMayUseFD = true;
	      }

	    }
	    
	  }

	  if(callMayUseFD) {

	    if(InlineAttempt* IA = getInlineAttempt(CI)) {

	      Start = make_vc(IA->getEntryBlock()->begin(), IA);
	      return true;

	    }
	    else {

	      LPDEBUG("Unexpanded call " << itcache(*CI) << " may affect FD from " << itcache(OpenInst) << "\n");
	      InstBlockedOpens[CI].push_back(std::make_pair(OpenInst, ReadInst));
	      Clobbers.push_back(make_vc(CI, this));
	      return false;

	    }

	  }

	}

      }

    }

  }

  if(isa<ReturnInst>(BB->getTerminator())) {

    if(!parent) {

      LPDEBUG("Instruction chain reaches end of main!\n");
      return false;

    }

    BasicBlock::iterator CallIt(getEntryInstruction());
    ++CallIt;
    Start = make_vc(CallIt, parent);
    return true;

  }

  return true;

}

bool InlineAttempt::checkOrQueueLoopIteration(ValCtx OpenInst, ValCtx OpenProgress, BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start) {

  return false;

}

bool PeelIteration::checkOrQueueLoopIteration(ValCtx OpenInst, ValCtx OpenProgress, BasicBlock* PresentBlock, BasicBlock* NextBlock, ValCtx& Start) {

  if(PresentBlock == L->getLoopLatch() && NextBlock == L->getHeader()) {

    PeelIteration* nextIter = getNextIteration();
    if(!nextIter) {

      LPDEBUG("Can't continue to pursue open call because loop " << L->getHeader()->getName() << " does not yet have iteration " << iterationCount+1 << "\n");

      addBlockedOpen(OpenInst, OpenProgress);

      Start = VCNull;
      return true;

    }
    else {

      Start = make_vc(L->getHeader()->begin(), nextIter);
      return true;

    }

  }

  return false;

}

int64_t IntegrationAttempt::tryGetIncomingOffset(Value* V) {

  CallInst* CI = cast<CallInst>(V);

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return it->second.incomingOffset + it->second.readSize;
  else {
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

void IntegrationAttempt::setNextUser(CallInst* CI, ValCtx U) {

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end()) {

    it->second.NextUser = U;

  }
  else {

    DenseMap<CallInst*, SeekFile>::iterator it = resolvedSeekCalls.find(CI);
    if(it != resolvedSeekCalls.end()) {

      it->second.NextUser = U;

    }
    else {

      assert(0 && "CI wasn't resolved after all?");

    }

  }

}

void IntegrationAttempt::setNextUser(OpenStatus& OS, ValCtx U) {

  if(OS.FirstUser == VCNull)
    OS.FirstUser = U;
  else
    OS.LatestResolvedUser.second->setNextUser(cast<CallInst>(OS.LatestResolvedUser.first), U);

}

bool IntegrationAttempt::vfsCallBlocksOpen(CallInst* VFSCall, ValCtx OpenInst, ValCtx LastReadInst, OpenStatus& OS, bool& isVfsCall, bool& shouldRequeue) {
  
  // Call to read(), one of the seek family or close()?
  
  isVfsCall = false;
  shouldRequeue = false;
  
  Function* Callee = getCalledFunction(VFSCall);
  if(!Callee)
    return false;

  StringRef CalleeName = Callee->getName();
  if(CalleeName == "read") {
    
    const FunctionType *FT = Callee->getFunctionType();
    if (FT->getNumParams() != 3 || !FT->getParamType(0)->isIntegerTy(32) ||
	!FT->getParamType(1)->isPointerTy() || !FT->getParamType(2)->isIntegerTy() ||
	!FT->getReturnType()->isIntegerTy()) {
      LPDEBUG("Assuming call to " << *Callee << " is not 'read' due to its weird signature\n");
      return false;
    }
    
    isVfsCall = true;
    
    Value* readFD = VFSCall->getArgOperand(0);
    if(isUnresolved(readFD)) {
      
      LPDEBUG("Can't forward open because FD argument of " << itcache(*VFSCall) << " is unresolved\n");
      shouldRequeue = true;
      return true;
      
    }
    else if(getReplacement(readFD) != OpenInst) {
      
      LPDEBUG("Ignoring " << itcache(*VFSCall) << " which references a different file\n");
      return false;
      
    }
    
    Value* readBytes = VFSCall->getArgOperand(2);
    ConstantInt* intBytes = dyn_cast_or_null<ConstantInt>(getConstReplacement(readBytes));
    if(!intBytes) {
      LPDEBUG("Can't push " << itcache(OpenInst) << " further: read amount uncertain\n");
      shouldRequeue = true;
      return true;
    }

    return true;
    
  }
  
  else if(CalleeName == "close") {
    const FunctionType *FT = Callee->getFunctionType();
    if(FT->getNumParams() != 1 || !FT->getParamType(0)->isIntegerTy(32)) {
      LPDEBUG("Assuming call to " << itcache(*Callee) << " is not really 'close' due to weird signature\n");
      return false;
    }
    
    isVfsCall = true;
    
    Value* closeFD = VFSCall->getArgOperand(0);
    if(isUnresolved(closeFD)) {
      shouldRequeue = true;
      return true;
    }
    else if(getReplacement(closeFD) != OpenInst) {
      return false;
    }
    
    LPDEBUG("Successfully forwarded to " << itcache(*VFSCall) << " which closes the file\n");
    return true;
    
  }
  else if(CalleeName == "llseek" || CalleeName == "lseek" || CalleeName == "lseek64") {
    
    const FunctionType* FT = Callee->getFunctionType();
    if(FT->getNumParams() != 3 || (!FT->getParamType(0)->isIntegerTy(32)) || (!FT->getParamType(1)->isIntegerTy()) || (!FT->getParamType(2)->isIntegerTy(32))) {
      LPDEBUG("Assuming call to " << itcache(*Callee) << " is not really an [l]lseek due to weird signature\n");
      return false;
    }
    
    isVfsCall = true;
    
    Value* seekFD = VFSCall->getArgOperand(0);
    if(isUnresolved(seekFD)) {
      shouldRequeue = true;
      return true;
    }
    else if(getReplacement(seekFD) != OpenInst) {
      return false;
    }
    
    Constant* whence = getConstReplacement(VFSCall->getArgOperand(2));
    Constant* newOffset = getConstReplacement(VFSCall->getArgOperand(1));
    
    if((!newOffset) || (!whence)) {
      LPDEBUG("Unable to push " << itcache(OpenInst) << " further due to uncertainty of " << itcache(*VFSCall) << " seek offset or whence");
      shouldRequeue = true;
      return true;
    }

    return true;
    
  }
  
  return false;
  
}

bool IntegrationAttempt::setVFSSuccessor(CallInst* VFSCall, ValCtx OpenInst, ValCtx LastReadInst, OpenStatus& OS) {

  Function* Callee = getCalledFunction(VFSCall);
  StringRef CalleeName = Callee->getName();
  const FunctionType *FT = Callee->getFunctionType();

  if(CalleeName == "read") {
    // OK, we know what this read operation does. Record that and queue another exploration from this point.
    int64_t incomingOffset;
    if(LastReadInst == OpenInst)
      incomingOffset = 0;
    else {
      incomingOffset = LastReadInst.second->tryGetIncomingOffset(LastReadInst.first);
    }

    Value* readBytes = VFSCall->getArgOperand(2);
    ConstantInt* intBytes = cast<ConstantInt>(getConstReplacement(readBytes));
    
    int cBytes = (int)intBytes->getLimitedValue();

    struct stat file_stat;
    if(::stat(OS.Name.c_str(), &file_stat) == -1) {
      
      LPDEBUG("Failed to stat " << OS.Name << "\n");
      return false;
      
    }
    
    int bytesAvail = file_stat.st_size - incomingOffset;
    if(cBytes > bytesAvail) {
      LPDEBUG("Desired read of " << cBytes << " truncated to " << bytesAvail << " (EOF)\n");
      cBytes = bytesAvail;
    }

    // OK, we know what this read operation does. Record that and queue another exploration from this point.

    LPDEBUG("Successfully forwarded to " << itcache(*VFSCall) << " which reads " << cBytes << " bytes\n");
    
    resolveReadCall(VFSCall, ReadFile(&OS, incomingOffset, cBytes));
    ValCtx thisReader = make_vc(VFSCall, this);
    setNextUser(OS, thisReader);
    OS.LatestResolvedUser = thisReader;
    pass->queueOpenPush(OpenInst, thisReader);
    
    // Investigate anyone that refs the buffer
    investigateUsers(VFSCall->getArgOperand(1));
    
    // The number of bytes read is also the return value of read.
    setReplacement(VFSCall, const_vc(ConstantInt::get(Type::getInt64Ty(VFSCall->getContext()), cBytes)));
    investigateUsers(VFSCall);
    
    return true;

  }
  else if(CalleeName == "close") {

    ValCtx ThisCall = make_vc(VFSCall, this);
    setNextUser(OS, ThisCall);
    OS.LatestResolvedUser = ThisCall;
    resolvedCloseCalls[VFSCall] = CloseFile(&OS);
    
    setReplacement(VFSCall, const_vc(ConstantInt::get(FT->getReturnType(), 0)));
    investigateUsers(VFSCall);
    
    return true;

  }
  else if(CalleeName == "llseek" || CalleeName == "lseek" || CalleeName == "lseek64") {

    Constant* whence = getConstReplacement(VFSCall->getArgOperand(2));
    Constant* newOffset = getConstReplacement(VFSCall->getArgOperand(1));

    uint64_t intOffset = cast<ConstantInt>(newOffset)->getLimitedValue();
    int32_t seekWhence = (int32_t)cast<ConstantInt>(whence)->getSExtValue();
    
    switch(seekWhence) {
    case SEEK_CUR:
      {
	int64_t incomingOffset;
	if(LastReadInst == OpenInst)
	  incomingOffset = 0;
	else {
	  incomingOffset = LastReadInst.second->tryGetIncomingOffset(LastReadInst.first);
	}      
	intOffset += incomingOffset;
      }
      break;
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

    LPDEBUG("Successfully forwarded to " << itcache(*VFSCall) << " which seeks to offset " << intOffset << "\n");

    // Seek's return value is the new offset.
    setReplacement(VFSCall, const_vc(ConstantInt::get(FT->getParamType(1), intOffset)));
    investigateUsers(VFSCall);
    
    resolveSeekCall(VFSCall, SeekFile(&OS, intOffset));
    
    ValCtx seekCall = make_vc(VFSCall, this);
    setNextUser(OS, seekCall);
    OS.LatestResolvedUser = seekCall;
    pass->queueOpenPush(OpenInst, seekCall);
    
    return true;

  }

  assert(0 && "Bad callee in setnextvfsuser");
  return false;

}

ValCtx IntegrationAttempt::getNextVFSUser(CallInst* CI) {

  DenseMap<CallInst*, ReadFile>::iterator it = resolvedReadCalls.find(CI);
  if(it != resolvedReadCalls.end())
    return it->second.NextUser;

  DenseMap<CallInst*, SeekFile>::iterator it2 = resolvedSeekCalls.find(CI);
  if(it2 != resolvedSeekCalls.end())
    return it2->second.NextUser;

  return VCNull;

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

void IntegrationAttempt::addBlockedOpen(ValCtx OpenInst, ValCtx ReadInst) {

  CFGBlockedOpens.push_back(std::make_pair(OpenInst, ReadInst));

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

