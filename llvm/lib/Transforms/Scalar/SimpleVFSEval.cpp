//===- SimpleVFSEval.cpp - Statically evaluate VFS-related syscalls--------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass executes VFS operations which are trivially executable.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "simplevfseval"
#include "llvm/Pass.h"
#include "llvm/Instructions.h"
#include "llvm/BasicBlock.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Support/VFSGraph.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"

#include <deque>
#include <string>
#include <algorithm>

#include <stdio.h>
#include <errno.h>
#include <string.h>

using namespace llvm;

static cl::opt<std::string> GraphOutputDirectory("simplevfs-graphout", cl::init(""));

namespace {
  
  class SimpleVFSPass : public FunctionPass {

  public:
    explicit SimpleVFSPass(char& ID) : FunctionPass(ID) { }
    bool runOnFunction(Function &F);
    virtual void getAnalysisUsage(AnalysisUsage &AU) const { }

  protected:
    virtual bool processOpenAt(CallInst* CI, VFSGraph*) = 0;

  private:

    VFSGraph* buildOpenAtGraph(CallInst* CI);

  };

  class SimpleVFSGraphs : public SimpleVFSPass {

  public:

    explicit SimpleVFSGraphs() : SimpleVFSPass(ID) { }

    static char ID; // Pass identification, replacement for typeid
    bool processOpenAt(CallInst* CI, VFSGraph*);

  };

  char SimpleVFSGraphs::ID = 0;

  class SimpleVFSEval : public SimpleVFSPass {

    bool getFileBytes(Value*, Value*, ConstantInt*, std::vector<Constant*>&, LLVMContext&, std::string&);

  public:

    explicit SimpleVFSEval() : SimpleVFSPass(ID) { }

    static char ID; // Pass identification, replacement for typeid
    bool processOpenAt(CallInst* CI, VFSGraph*);

  };

  char SimpleVFSEval::ID = 0;

  class SimpleVFSLoops : public SimpleVFSPass {

  public:

    explicit SimpleVFSLoops() : SimpleVFSPass(ID) { }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const { 

      AU.addRequired<LoopInfo>();
      AU.setPreservesAll();
      
    }

    static char ID;
    bool processOpenAt(CallInst* CI, VFSGraph*);

    void print(raw_ostream &OS, const Module*) const;

  private:

    llvm::SmallVector<std::pair<std::string, bool>, 8> unrollHeaders;

  };

  char SimpleVFSLoops::ID = 0;

}

// createSimpleVFSEvalPass - The public interface to this file...
Pass *llvm::createSimpleVFSEvalPass() {
  return new SimpleVFSEval();
}

Pass *llvm::createSimpleVFSGraphsPass() {
  return new SimpleVFSGraphs();
}

Pass *llvm::createSimpleVFSLoopsPass() {
  return new SimpleVFSLoops();
}

INITIALIZE_PASS(SimpleVFSEval, "simplevfseval", "Simple VFS Evaluation", false, false);
INITIALIZE_PASS(SimpleVFSGraphs, "simplevfsgraphs", "Simple VFS Graphs", false, false);
INITIALIZE_PASS(SimpleVFSLoops, "simplevfsloops", "Determine loops to peel for VFS eval", false, false);

VFSGraph* SimpleVFSPass::buildOpenAtGraph(CallInst* CI) {
  
  llvm::SmallSet<BasicBlock*, 10> interestingBlocks;
  llvm::SmallSet<Instruction*, 10> interestingInstructions;
  BasicBlock* startBlock = CI->getParent();

  interestingBlocks.insert(startBlock);
  interestingInstructions.insert(CI);

  VFSGraph* retGraph = new VFSGraph(CI);

  for(Value::use_iterator UI = CI->use_begin(), UE = CI->use_end(); UI != UE; UI++) {
    Instruction* I = cast<Instruction>(*UI);
    interestingBlocks.insert(I->getParent());
    interestingInstructions.insert(I);
    retGraph->nameNode(I);
  }
  
  for(Value::use_iterator UI = CI->use_begin(), UE = CI->use_end(); UI != UE; UI++) {

    Instruction* I = cast<Instruction>(*UI);
    llvm::SmallSet<BasicBlock*, 10> visitedBlocks;
    std::deque<BasicBlock*> toVisit;
    bool firstTime = true;
    
    toVisit.push_back(I->getParent());
    // But don't put it in visitedBlocks, so we'll inspect it again if the start block can loop back to itself

    DEBUG(dbgs() << "Trying to find predecessors for " << *I << "\n");

    while(!toVisit.empty()) {

      BasicBlock* nextBlock = toVisit.front(); toVisit.pop_front();

      DEBUG(dbgs() << "Searching block " << *nextBlock << "\n");
      BasicBlock::iterator BI(nextBlock->end());
      if(firstTime)
	BI = BasicBlock::iterator(I);

      bool foundDep = false;

      while(BI != nextBlock->begin()) {
	
	Instruction* testInstruction = --BI;
	DEBUG(dbgs() << "Considering instruction " << *testInstruction << "\n");
	if(interestingInstructions.count(testInstruction)) {
	  retGraph->addLink(testInstruction, I);
	  DEBUG(dbgs() << "Hit!\n");
	  foundDep = true;
	  break;
	}

      }

      if(!foundDep) {
	if(!((nextBlock == startBlock) && !firstTime)) {
	  DEBUG(dbgs() << "No deps in this block, adding predecessors to search\n");
	  for (pred_iterator PI = pred_begin(nextBlock), E = pred_end(nextBlock); PI != E; ++PI) {
	    BasicBlock* visitBlock = cast<BasicBlock>(*PI);
	    if(!visitedBlocks.count(visitBlock)) {
	      toVisit.push_back(visitBlock);
	      visitedBlocks.insert(visitBlock);
	    }
	  }
	}
      }

      firstTime = false;

    }

  }

  return retGraph;

}

bool SimpleVFSGraphs::processOpenAt(CallInst* CI, VFSGraph* depGraph) {

  // Check for a fixed filename
  std::string Filename;
  if (!GetConstantStringInfo(CI->getArgOperand(0), Filename))
    return false;

  std::string graphTitle;
  raw_string_ostream graphStream(graphTitle);
  graphStream << "VFS Graph for " << *CI;

  if(GraphOutputDirectory.empty())
    WriteGraph(depGraph, graphTitle);
  else {
    std::string error;
    sys::Path graphPath(GraphOutputDirectory);
    graphPath.makeUnique(false, &error);
    if(!error.empty()) {
      errs() << "Failed to create a unique path: " << error << "\n";
      return false;
    }
    raw_fd_ostream os(graphPath.c_str(), error);
    WriteGraph(os, depGraph, false, "", graphTitle);
    if(!error.empty())
      errs() << "Failure writiing to " << graphPath.str() << ": " << error << "\n";
  }

  return false;

}

bool SimpleVFSEval::getFileBytes(Value* fileName, Value* filePosition, ConstantInt* nBytes, std::vector<Constant*>& arrayBytes, LLVMContext& Context, std::string& errors) {

  std::string strFileName;
  if(!GetConstantStringInfo(fileName, strFileName)) {
    errors = "Filename not a constant";
    return false;
  }

  ConstantInt* filePosInt = cast<ConstantInt>(filePosition);
  uint64_t realFilePos = filePosInt->getLimitedValue();

  ConstantInt* bytesInt;
  uint64_t realBytes;
  if((bytesInt = dyn_cast<ConstantInt>(nBytes)))
    realBytes = bytesInt->getLimitedValue();
  else {
    errors = "Read length not a constant";
    return false;
  }

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
  const Type* charType = IntegerType::get(Context, 8);
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

bool SimpleVFSEval::processOpenAt(CallInst* CI, VFSGraph* depGraph) {

  VFSGraphNode* currentNode = &depGraph->instructionNodes[CI];
  bool modified = false;
  while(1) {

    if(currentNode->succs.empty()) {
      DEBUG(dbgs() << "Deleting unused open call " << *CI << ": fixed file descriptor leak??\n");
      modified = true;
      CI->removeFromParent();
      break;
    }
    else if(currentNode->succs.size() != 1) {
      DEBUG(dbgs() << "Can't process " << *CI << " further as it has multiple possible successors\n");
      break;
    }

    VFSGraphNode* succNode = currentNode->succs[0];
    Instruction* succ = succNode->I;
    if(succNode->preds.size() != 1) {
      DEBUG(dbgs() << "Can't optimize " << *CI << " further because its successor " << *succ << " has more than one possible predecessor\n");
      break;
    }
    CallInst* Caller;
    if((Caller = dyn_cast<CallInst>(succ))) {

      LLVMContext& Context = CI->getParent()->getParent()->getContext();
      IRBuilder<> Builder(Context);
	
      Function* Callee = Caller->getCalledFunction();
      if (Callee == 0 || !Callee->isDeclaration() ||
	  !(Callee->hasExternalLinkage() || Callee->hasDLLImportLinkage())) {
	DEBUG(dbgs() << "Can't optimize " << *CI << " further: call to non-external function\n");
	break;
      }
      StringRef CalleeName = Callee->getName();
      if(CalleeName == "read") {

	const FunctionType *FT = Callee->getFunctionType();
	if (FT->getNumParams() != 3 || !FT->getParamType(0)->isIntegerTy(32) ||
	    !FT->getParamType(1)->isPointerTy() || !FT->getParamType(2)->isIntegerTy() ||
	    !FT->getReturnType()->isIntegerTy()) {
	  DEBUG(dbgs() << "Can't optimize " << *CI << " further: call to weird 'read' function\n");
	  break;
	}
	Value* readBuffer = Caller->getArgOperand(1);
	Value* readBytes = Caller->getArgOperand(2);

	ConstantInt* intBytes = dyn_cast<ConstantInt>(readBytes);
	if(!intBytes) {
	  DEBUG(dbgs() << "Can't optimize " << *CI << " further: read amount uncertain\n");
	  break;
	}

	std::string errors;
	Value* fileName = CI->getArgOperand(0);
	Value* filePosition = CI->getArgOperand(2);
	std::vector<Constant*> arrayBytes;
	if(!getFileBytes(fileName, filePosition, intBytes, arrayBytes, Context, errors)) {
	  DEBUG(dbgs() << "Can't optimize " << *CI << " further: failed reading file: (" << errors << ")\n");
	  break;
	}

	modified = true;

	Builder.SetInsertPoint(Caller->getParent(), Caller);
	int i;
	std::vector<Constant*>::iterator I, E;
	Instruction* lastInsert = Caller;
	for(I = arrayBytes.begin(), E = arrayBytes.end(), i = 0; I != E; I++, i++) {
	  lastInsert = cast<Instruction>(Builder.CreateConstInBoundsGEP1_32(readBuffer, i));
	  lastInsert = cast<Instruction>(Builder.CreateStore(*I, lastInsert));
	}
	CI->removeFromParent();
	CI->insertAfter(lastInsert);
	uint64_t oldFilePosition = (cast<ConstantInt>(filePosition))->getLimitedValue();
	ConstantInt* newFilePosition = ConstantInt::get(IntegerType::get(Context, 64), arrayBytes.size() + oldFilePosition, false);
	CI->setArgOperand(2, newFilePosition);
	ConstantInt* realLength = ConstantInt::get(IntegerType::get(Context, 64), arrayBytes.size(), true);
	Caller->replaceAllUsesWith(realLength);
	Caller->eraseFromParent();
	    
      }
      else if(CalleeName == "close") {
	const FunctionType *FT = Callee->getFunctionType();
	if(FT->getNumParams() != 1 || !FT->getParamType(0)->isIntegerTy(32)) {
	  DEBUG(dbgs() << "Can't optimize " << *CI << " further: call to weird 'close' function\n");
	  break;
	}

	Caller->replaceAllUsesWith(ConstantInt::get(IntegerType::get(Context, 32), 0, true));
	Caller->eraseFromParent();
	CI->eraseFromParent();
	modified = true;
	break;

      }
      else {
	DEBUG(dbgs() << "Can't optimize " << *CI << " further: call to unknown external function " << CalleeName << "\n");
	break;
      }
    }
    else {
      DEBUG(dbgs() << "Can't optimize " << *CI << " further: non-call user\n");
      break;
    }

    currentNode = currentNode->succs[0];

  }

  return modified;

}

bool SimpleVFSLoops::processOpenAt(CallInst* CI, VFSGraph* depGraph) {

  VFSGraphNode* currentNode = &depGraph->instructionNodes[CI];
  LoopInfo &LI = getAnalysis<LoopInfo>();
  Loop* openLoop = LI.getLoopFor(CI->getParent());
  bool couldEvalNow = false;
  
  while(1) {

    if(currentNode->succs.empty()) {
      DEBUG(dbgs() << "Ran out of successors for " << *CI << "\n");
      return false;
    }
    else if(currentNode->succs.size() != 1) {
      DEBUG(dbgs() << *CI << " is blocked because " << *(currentNode->I) << " has multiple possible successors\n");
      break;
    }

    VFSGraphNode* succNode = currentNode->succs[0];
    Instruction* succ = succNode->I;
    if(succNode->preds.size() != 1) {

      DEBUG(dbgs() << *CI << " is blocked by " << *succ << " which has more than one possible predecessor\n");
      if(!isa<CallInst>(succ)) {
	DEBUG(dbgs() << "Ignoring because it isn't a call instruction\n");
	return false;
      }

      Loop* userLoop = LI.getLoopFor(succ->getParent());
      if((!userLoop) || (openLoop == userLoop)) {
	DEBUG(dbgs() << "Ignoring because it's in the same loop as the open call, or isn't in a loop at all\n");
	return false;
      }
      
      while(userLoop && (openLoop != userLoop)) {
	Loop* parentLoop = userLoop->getParentLoop();
	if((!parentLoop) || (parentLoop == openLoop)) {
	  BasicBlock* Header = userLoop->getHeader();
	  if(!Header)
	    DEBUG(dbgs() << "Can't record loop " << *userLoop << " because it has no header!\n");
	  else
	    unrollHeaders.push_back(std::make_pair(Header->getName(), couldEvalNow));
	  return false;
	}
      }

      // Unreachable
      return false;
    }

    couldEvalNow = true;
    currentNode = currentNode->succs[0];

  }

  return false;

}

void SimpleVFSLoops::print(raw_ostream &OS, const Module*) const {

  for(llvm::SmallVector<std::pair<std::string, bool>, 8>::const_iterator I = unrollHeaders.begin(), E = unrollHeaders.end(); I != E; I++) {
    OS << (I->second ? "Could" : "Should") << " peel " << I->first << "\n";
  }

}

/// runOnFunction - This is the main transformation entry point for a function.
bool SimpleVFSPass::runOnFunction(Function& F) {

  std::vector<std::pair<CallInst*, VFSGraph*> > openAts;

  for (Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ) {

    BasicBlock& BB = *(FI++);

    for(BasicBlock::iterator BI = BB.begin(), BE = BB.end(); BI != BE;) {

      Instruction* I = &*(BI++);
      if (CallInst *CI = dyn_cast<CallInst>(I)) {
	if (Function *F = CI->getCalledFunction()) {
	  switch (F->getIntrinsicID()) {
	  case Intrinsic::openat:
	    {
	      VFSGraph* graph = buildOpenAtGraph(CI);
	      openAts.push_back(std::make_pair(CI, graph));
	      break;
	    }
	  default:
	    break;
	  }
	}
      }
    }
  }

  bool Changed = false;

  for(std::vector<std::pair<CallInst*, VFSGraph*> >::iterator OI = openAts.begin(), OE = openAts.end(); OI != OE; OI++) {
    Changed |= processOpenAt(OI->first, OI->second);
    delete OI->second;
  }

  return Changed;
}

