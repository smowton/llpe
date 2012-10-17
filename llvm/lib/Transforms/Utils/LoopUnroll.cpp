//===-- UnrollLoop.cpp - Loop unrolling utilities -------------------------===//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements some loop unrolling utilities. It does not define any
// actual pass or policy, but provides a single function to perform loop
// unrolling.
//
// It works best when loops have been canonicalized by the -indvars pass,
// allowing it to determine the trip counts of loops easily.
//
// The process of unrolling can produce extraneous basic blocks linked with
// unconditional branches.  This will be corrected in the future.
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "loop-unroll"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/BasicBlock.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

// TODO: Should these be here or in LoopUnroll?
STATISTIC(NumCompletelyUnrolled, "Number of loops completely unrolled");
STATISTIC(NumUnrolled,    "Number of loops unrolled (completely or otherwise)");

/// RemapInstruction - Convert the instruction operands from referencing the
/// current values into those specified by VMap.
static inline void RemapInstruction(Instruction *I,
                                    ValueMap<const Value *, Value*> &VMap) {
  DEBUG(dbgs() << "Apply remap: " << *I);
  for (unsigned op = 0, E = I->getNumOperands(); op != E; ++op) {
    Value *Op = I->getOperand(op);
    ValueMap<const Value *, Value*>::iterator It = VMap.find(Op);
    if (It != VMap.end())
      I->setOperand(op, It->second);
  }
  DEBUG(dbgs() << " --> " << *I << "\n");
}

/// FoldBlockIntoPredecessor - Folds a basic block into its predecessor if it
/// only has one predecessor, and that predecessor only has one successor.
/// The LoopInfo Analysis that is passed will be kept consistent.
/// Returns the new combined block.
static BasicBlock *FoldBlockIntoPredecessor(BasicBlock *BB, LoopInfo* LI) {
  // Merge basic blocks into their predecessor if there is only one distinct
  // pred, and if there is only one distinct successor of the predecessor, and
  // if there are no PHI nodes.
  BasicBlock *OnlyPred = BB->getSinglePredecessor();
  if (!OnlyPred) return 0;

  if (OnlyPred->getTerminator()->getNumSuccessors() != 1)
    return 0;

  DEBUG(dbgs() << "Merging: " << *BB << "into: " << *OnlyPred);

  // Resolve any PHI nodes at the start of the block.  They are all
  // guaranteed to have exactly one entry if they exist, unless there are
  // multiple duplicate (but guaranteed to be equal) entries for the
  // incoming edges.  This occurs when there are multiple edges from
  // OnlyPred to OnlySucc.
  FoldSingleEntryPHINodes(BB);

  // Delete the unconditional branch from the predecessor...
  OnlyPred->getInstList().pop_back();

  // Move all definitions in the successor to the predecessor...
  OnlyPred->getInstList().splice(OnlyPred->end(), BB->getInstList());

  // Make all PHI nodes that referred to BB now refer to Pred as their
  // source...
  BB->replaceAllUsesWith(OnlyPred);

  std::string OldName = BB->getName();

  // Erase basic block from the function...
  LI->removeBlock(BB);
  BB->eraseFromParent();

  // Inherit predecessor's name if it exists...
  if (!OldName.empty() && !OnlyPred->hasName())
    OnlyPred->setName(OldName);

  return OnlyPred;
}

struct pendingPhiFixup { 
  PHINode* node; BasicBlock* pred; Value* val;
  pendingPhiFixup(PHINode* n, BasicBlock* p, Value* v) : node(n), pred(p), val(v) { }
};

Loop* llvm::cloneLoop(Loop* oldLoop, std::map<Loop*, Loop*>& oldToNewMap) {

  DEBUG(dbgs() << "Cloning loop " << *oldLoop << "\n");
  Loop* newLoop = new Loop();
  oldToNewMap[oldLoop] = newLoop;
  for(Loop::iterator it = oldLoop->begin(); it != oldLoop->end(); it++)
    newLoop->addChildLoop(cloneLoop(*it, oldToNewMap));
  return newLoop;

}

BasicBlock* splitEdge(BasicBlock* fromBlock, TerminatorInst* fromInst, BasicBlock* toBlock, Twine blockName, bool addPHIs) {
  
  BasicBlock *newBlock = BasicBlock::Create(fromBlock->getContext(), blockName, fromBlock->getParent(), toBlock);
  for(BasicBlock::iterator it = toBlock->begin(); isa<PHINode>(*it) && it != toBlock->end(); it++) {
    PHINode* PN = cast<PHINode>(it);
    int idx = PN->getBasicBlockIndex(fromBlock);
    PN->setIncomingBlock(idx, newBlock);
    if(addPHIs) {
      PHINode* newPHI = PHINode::Create(PN->getType(), PN->getName() + ".lcssa", newBlock);
      newPHI->addIncoming(PN->getIncomingValue(idx), fromBlock);
      PN->setIncomingValue(idx, newPHI);
    }
  }
  BranchInst::Create(toBlock, newBlock);

  for(unsigned i = 0; i < fromInst->getNumSuccessors(); ++i) {
    if(fromInst->getSuccessor(i) == toBlock)
      fromInst->setSuccessor(i, newBlock);
  }

  return newBlock;
  
}

static void replaceTerminatorEdges(TerminatorInst* TI, BasicBlock* FromBB, BasicBlock* ToBB) {

  for(unsigned i = 0; i < TI->getNumSuccessors(); ++i) {
    if(TI->getSuccessor(i) == FromBB)
      TI->setSuccessor(i, ToBB);
  }

}

// TI passed by ref because we might replace it.
static void removeTerminatorEdges(TerminatorInst*& TI, BasicBlock* ToBB) {

  // Count the edges going elsewhere and see if we now have a unique destination.
  unsigned keepEdges = 0;
  BasicBlock* UniqueDest = 0;
  bool noUniqueDest = false;

  BasicBlock* TermBB = TI->getParent();

  for(unsigned i = 0; i < TI->getNumSuccessors(); ++i) {

    if(TI->getSuccessor(i) != ToBB) {
      keepEdges++;
      if(!noUniqueDest) {
	if(!UniqueDest)
	  UniqueDest = ToBB;
	else {
	  UniqueDest = 0;
	  noUniqueDest = true;
	}
      }
    }

  }

  if((!UniqueDest) && !noUniqueDest) {

    // This leaves broken CFG: when working on loops without an exiting latch, our caller must make
    // sure they route away from this block.
    TI->eraseFromParent();
    TI = new UnreachableInst(TermBB->getContext(), TermBB);    

  }
  else if(UniqueDest) {

    TI->eraseFromParent();
    TI = BranchInst::Create(UniqueDest, TermBB);

  }
  else {

    // At least 2 outgoing destinations remain! Must be a switch, or else we were asked to remove
    // a destination that never occurs.
    SwitchInst* SI = cast<SwitchInst>(TI);
    if(SI->getDefaultDest() == ToBB) {

      // Must have a default edge, but our chosen one is no good! Just default
      // to one of the other edges that won't be deleted.
      for(unsigned i = 0; i < TI->getNumSuccessors(); ++i) {

	BasicBlock* Succ = TI->getSuccessor(i);
	if(Succ != ToBB) {
	  TI->setSuccessor(0, Succ);
	  break;
	}

      }

    }

    for(unsigned i = 1; i < TI->getNumSuccessors(); ++i) {

      if(TI->getSuccessor(i) == ToBB) {

	SI->removeCase(i);
	--i;

      }
      
    }

  }

}

/// Unroll the given loop by Count. The loop must be in LCSSA form. Returns true
/// if unrolling was succesful, or false if the loop was unmodified. Unrolling
/// can only fail when the loop's latch block is not terminated by a conditional
/// branch instruction. However, if the trip count (and multiple) are not known,
/// loop unrolling will mostly produce more code that is no faster.
///
/// The LoopInfo Analysis that is passed will be kept consistent.
///
/// If a LoopPassManager is passed in, and the loop is fully removed, it will be
/// removed from the LoopPassManager as well. LPM can also be NULL.
///
/// If doPeel is true, the loop will be peeled rather than unrolled: it will be preceded
/// by Count copies of its own body.
///
/// If CompletelyUnroll is true, complete unrolling (straightening) will be done even if
/// the loop can't easily be proven to have a small finite iteration count.
///
/// If allowNonCondLatch is true, the loop will be unrolled even if the latch->header edge
/// is unconditional. This may leave an 'unreachable' in the last loop latch which our
/// caller must clean up.
///
/// If keepLatchExits is true, exit edges stemming from the latch block will be treated
/// like any other exit, rather than being eliminated when we think we're certain
/// the loop will iterate this time. The latch->header edge will be amended as usual.

bool llvm::UnrollLoop(Loop *L, unsigned Count, LoopInfo* LI, LPPassManager* LPM, bool doPeel, bool CompletelyUnroll, bool allowNonCondLatch, bool keepLatchExits, std::vector<ValueMap<const Value *, Value*>* >* Iterations) {
  BasicBlock *Preheader = L->getLoopPreheader();
  if (!Preheader) {
    DEBUG(dbgs() << "  Can't unroll; loop preheader-insertion failed.\n");
    return false;
  }

  BasicBlock *LatchBlock = L->getLoopLatch();
  if (!LatchBlock) {
    DEBUG(dbgs() << "  Can't unroll; loop exit-block-insertion failed.\n");
    return false;
  }

  BasicBlock *Header = L->getHeader();
  TerminatorInst* TI = LatchBlock->getTerminator();
  BranchInst *BI = dyn_cast<BranchInst>(TI);
  
  if ((!BI || BI->isUnconditional()) && !allowNonCondLatch) {
    // The loop-rotate pass can be helpful to avoid this in many cases.
    DEBUG(dbgs() <<
             "  Can't unroll/peel; loop not terminated by a conditional branch.\n");
    return false;
  }
  
  if(BI && BI->isUnconditional()) {
    BI = 0;
  }

  // Notify ScalarEvolution that the loop will be substantially changed,
  // if not outright eliminated.
  if(LPM) {
    if (ScalarEvolution *SE = LPM->getAnalysisIfAvailable<ScalarEvolution>())
      SE->forgetLoop(L);
  }

  unsigned TripCount = 0;
  unsigned TripMultiple = 0;
  unsigned BreakoutTrip = 0;

  if(!doPeel) {

    if(CompletelyUnroll) {

      // Suppose the loop lasts for Count iterations.
      TripCount = Count;

    }
    else {

      // Find trip count
      TripCount = L->getSmallConstantTripCount();
      // Find trip multiple if count is not available
      TripMultiple = 1;
      if (TripCount == 0)
	TripMultiple = L->getSmallConstantTripMultiple();
      
      if (TripCount != 0)
	DEBUG(dbgs() << "  Trip Count = " << TripCount << "\n");
      if (TripMultiple != 1)
	DEBUG(dbgs() << "  Trip Multiple = " << TripMultiple << "\n");

      // Effectively "DCE" unrolled iterations that are beyond the tripcount
      // and will never be executed.
      if (TripCount != 0 && Count > TripCount)
	Count = TripCount;

      assert(Count > 0);
      assert(TripMultiple > 0);
      assert(TripCount == 0 || TripCount % TripMultiple == 0);

      // Are we eliminating the loop control altogether?
      CompletelyUnroll = Count == TripCount;

    }

    // If we know the trip count, we know the multiple...
    BreakoutTrip = 0;
    if (TripCount != 0) {
      BreakoutTrip = TripCount % Count;
      TripMultiple = 0;
    } else {
      // Figure out what multiple to use.
      BreakoutTrip = TripMultiple =
	(unsigned)GreatestCommonDivisor64(Count, TripMultiple);
    }

    if (CompletelyUnroll) {
      DEBUG(dbgs() << "COMPLETELY UNROLLING loop %" << Header->getName()
	    << " with trip count " << TripCount << "!\n");
    } else {
      DEBUG(dbgs() << "UNROLLING loop %" << Header->getName()
	    << " by " << Count);
      if (TripMultiple == 0 || BreakoutTrip != TripMultiple) {
	DEBUG(dbgs() << " with a breakout at trip " << BreakoutTrip);
      } else if (TripMultiple != 1) {
	DEBUG(dbgs() << " with " << TripMultiple << " trips per branch");
      }
      DEBUG(dbgs() << "!\n");
    }

  } // if(!doPeel)
  else {
    DEBUG(dbgs() << "PEELING loop %" << Header->getName() << " by " << Count << "\n");
  }

  std::vector<BasicBlock*> LoopBlocks = L->getBlocks();
  std::vector<Loop*> SubLoops = L->getSubLoops();
  SmallVector<BasicBlock*, 8> ExitingBlocks;
  L->getExitingBlocks(ExitingBlocks);
  SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8> ExitingEdges;
  L->getExitEdges(ExitingEdges);
  
  std::vector<BasicBlock*> LatchExitBlocks;
  for(unsigned i = 0; i < TI->getNumSuccessors(); ++i) {
    BasicBlock* Succ =  TI->getSuccessor(i);
    if(!L->contains(Succ))
      LatchExitBlocks.push_back(Succ);
  }
  
  // For the first iteration of the loop, we should use the precloned values for
  // PHI nodes.  Insert associations now.
  typedef ValueMap<const Value*, Value*> ValueToValueMapTy;
  ValueToValueMapTy LastValueMap;
  std::vector<PHINode*> OrigPHINode;
  for (BasicBlock::iterator I = Header->begin(); isa<PHINode>(I); ++I) {
    PHINode *PN = cast<PHINode>(I);
    OrigPHINode.push_back(PN);
    if (Instruction *I = 
                dyn_cast<Instruction>(PN->getIncomingValueForBlock(LatchBlock)))
      if (L->contains(I))
        LastValueMap[I] = I;
  }

  std::vector<BasicBlock*> Headers;
  std::vector<BasicBlock*> Latches;
  Headers.push_back(Header);
  Latches.push_back(LatchBlock);

  // Step 1: Clone loop structures such that nested loops are created to accommodate loop body duplication.
  std::vector<std::map<Loop*, Loop*> > IterLoops;
  {
    std::vector<Loop*> NewLoops;
    for (unsigned i = 1; i < Count; i++) {
      DEBUG(dbgs() << "Cloning outer loop " << *L << "\n");
      // Are the newly cloned blocks to be members of the original loop or its parent loop/function?
      bool newBlocksInLoop = (!CompletelyUnroll) && ((!doPeel) || i == Count - 1); 
      IterLoops.push_back(std::map<Loop*, Loop*>());
      std::map<Loop*, Loop*>& oldToNewLoops = IterLoops.back();
      Loop* target = 0;
      if(newBlocksInLoop)
	target = L;
      else
	target = L->getParentLoop();
      oldToNewLoops[L] = target;
      // If no parent, then the new loops are top-level
      for(Loop::iterator it = L->begin(); it != L->end(); it++) {
	Loop* newLoop = cloneLoop(*it, oldToNewLoops);
	if(target) {
	  if(target == L) 
	    // Can't add these now or they'll get caught in future clone operations
	    NewLoops.push_back(newLoop);
	  else
	    target->addChildLoop(newLoop);
	}
	else
	  LI->addTopLevelLoop(newLoop);
      }
    }
    for(std::vector<Loop*>::iterator it = NewLoops.begin(); it != NewLoops.end(); it++) {
      L->addChildLoop(*it);
    }
  }

  for (unsigned It = 1; It != Count; ++It) {
    std::vector<BasicBlock*> NewBlocks;
    std::vector<pendingPhiFixup> pendingPhiFixups;
    std::map<Loop*, Loop*>& oldToNewLoops = IterLoops[It-1];

    // Decide the nature of the new block
    // Should the new header keep its PHI nodes?
    bool newHeaderHasMultiplePredecessors = false;
    if(doPeel && It == Count - 1)
      newHeaderHasMultiplePredecessors = true;
    // Could we break before or after this iteration?
    bool thisLatchCouldBreak = true;
    if((!doPeel) && !keepLatchExits) {
      // If we know the trip count or a multiple of it, we can safely use an
      // unconditional branch for some iterations.
      if (It != Count - 1 && (It + 1) != BreakoutTrip && (TripMultiple == 0 || (It + 1) % TripMultiple != 0)) {
	thisLatchCouldBreak  = false;
      }
    }
    
    for (std::vector<BasicBlock*>::iterator BB = LoopBlocks.begin(),
         E = LoopBlocks.end(); BB != E; ++BB) {
      ValueToValueMapTy VMap;

      // Clone the block
      BasicBlock *New = CloneBasicBlock(*BB, VMap, "." + Twine(It));
      NewBlocks.push_back(New);
      Header->getParent()->getBasicBlockList().push_back(New);

      Loop* innermostLoop = LI->getLoopFor(*BB);
      if(oldToNewLoops[innermostLoop]) {
	DEBUG(dbgs() << "Added block " << *New << " to loop " << *(oldToNewLoops[innermostLoop]) << "\n");
	oldToNewLoops[innermostLoop]->addBasicBlockToNewLoop(New, LI->getBase());
	// Make this block a loop header if appropriate. It is the header of 0 or 1 loops, and if it
	// is a header at all it is the header of the innermost loop. This is because we require
	// LoopSimplify, which requires that loop headers have exactly 2 predecessors: the latch and the preheader.
	// Thus it is not the header of two loops, or it would have two backedges and 3 predecessors.
	if(innermostLoop != L && innermostLoop->getHeader() == *BB)
	  oldToNewLoops[innermostLoop]->moveToHeader(New);
      }
      // Else the new block is not in a loop

      // Wire the new header's PHIs to use previous iteration values if we'll have one predecessor
      // or save the needed incoming value if we'll have many, to apply in the fixup stage later
      if (*BB == Header)
        for (unsigned i = 0, e = OrigPHINode.size(); i != e; ++i) {
	  PHINode *NewPHI = cast<PHINode>(VMap[OrigPHINode[i]]);
	  Value *InVal = NewPHI->getIncomingValueForBlock(LatchBlock);
	  if (Instruction *InValI = dyn_cast<Instruction>(InVal))
	    if (It > 1 && L->contains(InValI))
	      InVal = LastValueMap[InValI];
	  if(!newHeaderHasMultiplePredecessors) {
	    // This block now has one predecessor -- kill the PHI.
	    VMap[OrigPHINode[i]] = InVal;
	    New->getInstList().erase(NewPHI);
	  }
	  else {
	    // This block has two predecessors: the previous iteration and its own latch block.
	    // Record the predecessor now but apply it after renaming has taken place.
	    pendingPhiFixups.push_back(pendingPhiFixup(NewPHI, Latches.back(), InVal));
	  }
        }

      // Update our running map of newest clones
      LastValueMap[*BB] = New;
      for (ValueToValueMapTy::iterator VI = VMap.begin(), VE = VMap.end();
           VI != VE; ++VI) {
	DEBUG(dbgs() << "Remap " << *(VI->first) << " --> " << *(VI->second) << "\n");
        LastValueMap[VI->first] = VI->second;
      }

      // Keep track of new headers and latches as we create them, so that
      // we can insert the proper branches later.
      if (*BB == Header)
        Headers.push_back(New);
      if (*BB == LatchBlock)
        Latches.push_back(New);

    }
    
    // Remap all instructions in the most recent iteration,
    // i.e. reassociate references to refer to the most recent iteration.
    for (unsigned i = 0; i < NewBlocks.size(); ++i)
      for (BasicBlock::iterator I = NewBlocks[i]->begin(),
           E = NewBlocks[i]->end(); I != E; ++I)
        RemapInstruction(I, LastValueMap);

    for(std::vector<BasicBlock*>::iterator it = NewBlocks.begin(); it != NewBlocks.end(); it++) {
      DEBUG(dbgs() << "New block after renaming: " << **it << "\n");
    }

    // Add to external PHIs to reflect the new loop iteration.
    for(SmallVector<BasicBlock*, 8>::iterator it = ExitingBlocks.begin(); it != ExitingBlocks.end(); it++) {
      if (*it != LatchBlock || thisLatchCouldBreak)
        for (Value::use_iterator UI = (*it)->use_begin(), UE = (*it)->use_end();
             UI != UE;) {
          Instruction *UseInst = cast<Instruction>(*UI);
          ++UI;
          if (isa<PHINode>(UseInst) && !L->contains(UseInst) && std::find(NewBlocks.begin(), NewBlocks.end(), UseInst->getParent()) == NewBlocks.end()) {
            PHINode *phi = cast<PHINode>(UseInst);
	    DEBUG(dbgs() << "User " << *phi << " in basic block " << *(phi->getParent()) << " augmented: ");
            Value *Incoming = phi->getIncomingValueForBlock(*it);
	    if(Instruction* IncomingI = dyn_cast<Instruction>(Incoming))
	      if(L->contains(IncomingI))
		Incoming = LastValueMap[IncomingI];
            phi->addIncoming(Incoming, cast<BasicBlock>(LastValueMap[*it]));
	    DEBUG(dbgs() << "Yielded " << *phi << "\n");
          }
        }
    }

    // Apply any PHIs that needed to refer to the previous iteration
    for(std::vector<pendingPhiFixup>::iterator it = pendingPhiFixups.begin(); it != pendingPhiFixups.end(); it++) {
      DEBUG(dbgs() << "Fixing up PHI node "  << *(it->node) << "...");
      it->node->removeIncomingValue(Preheader, false);
      it->node->addIncoming(it->val, it->pred);
      DEBUG(dbgs() << "Turned it into " << *(it->node) << "\n");
    }

    for(std::vector<BasicBlock*>::iterator it = NewBlocks.begin(); it != NewBlocks.end(); it++) {
      DEBUG(dbgs() << "New block after fixups: " << **it << "\n");
    }

    // If our caller wants to know the mappings from iteration to iteration, let them know.
    // Note full copy of the map:

    if(Iterations) {
      Iterations->push_back(new ValueMap<const Value*, Value*>());
      DEBUG(dbgs() << "Values for iteration " << It << ":\n");
      for(ValueMap<const Value*, Value*>::iterator VI = LastValueMap.begin(), VE = LastValueMap.end(); VI != VE; ++VI) {

	if(isa<Instruction>(VI->first)) {
	  DEBUG(dbgs() << "Inst " << *(VI->first) << " -> " << *(VI->second) << "\n");
	}
	else {
	  DEBUG(dbgs() << "Block " << VI->first->getName() << " -> " << VI->second->getName() << "\n");
	}

      }
      Iterations->back()->insert(LastValueMap.begin(), LastValueMap.end());
    }

  }

  // Fix the first (original) iteration:
  // 1. Fix exit PHIs that draw from the first iteration's latch if we know it can't exit
  bool firstIterationCanBreak = doPeel || BreakoutTrip == 1 || TripMultiple == 1 || keepLatchExits;
  if ((!firstIterationCanBreak)) {
    for(unsigned i = 0; i < LatchExitBlocks.size(); ++i) {
      BasicBlock* BB = LatchExitBlocks[i];
      for(BasicBlock::iterator I = BB->begin(), IE = BB->end(); I != IE && isa<PHINode>(*I); I++) {
	PHINode* PN = cast<PHINode>(I);
	PN->removeIncomingValue(LatchBlock, false);
      }
    }
  }

  // 2. Fix first iteration's header PHIs if it's no longer a loop header,
  //    or rewire them to use the last iteration's equivalent value otherwise.
  for (unsigned i = 0, e = OrigPHINode.size(); i != e; ++i) {
    PHINode *PN = OrigPHINode[i];
    if (CompletelyUnroll || doPeel) {
      PN->replaceAllUsesWith(PN->getIncomingValueForBlock(Preheader));
      Header->getInstList().erase(PN);
    }
    else {
      Value* V = PN->removeIncomingValue(LatchBlock, false);
      if(Instruction* I = dyn_cast<Instruction>(V))
	if(L->contains(I))
	  V = LastValueMap[I];
      PN->addIncoming(V, Latches.back());
    }
  }

  // 3. Remove the first iteration from the Loop descriptor if it's no longer in the loop
  // (reparent with the next loop out if necessary)
  if(CompletelyUnroll || doPeel) {

    Loop* parent = L->getParentLoop();

    // Reparent the loops that sat directly within L:
    for(std::vector<Loop*>::iterator it = SubLoops.begin(), it2 = SubLoops.end(); it != it2; ++it) {

      Loop* SubL = *it;

      Loop::iterator SubLI = L->begin();
      while((*SubLI) != SubL)
	++SubLI;

      L->removeChildLoop(SubLI);
      if(parent) {

	parent->addChildLoop(SubL);

      }
      else {

	LI->addTopLevelLoop(SubL);

      }

    }

    // Reparent original blocks not in a subloop.

    for(std::vector<BasicBlock*>::iterator it = LoopBlocks.begin(); it != LoopBlocks.end(); it++) {

      if(LI->getLoopFor(*it) != L)
	continue;

      DEBUG(dbgs() << "Removed block " << (*it)->getName() << " from loop " << *L << "\n");
      LI->removeBlock(*it);
      if(parent) {
	DEBUG(dbgs() << "Added block " << (*it)->getName() << " to loop " << *parent << "\n");
	parent->addBasicBlockToNewLoop(*it, LI->getBase());
      }

    }

    if(!CompletelyUnroll)
      L->moveToHeader(Headers.back());
    else {
      // Remove the loop from the LoopPassManager if it's completely removed.
      if(LPM)
	LPM->deleteLoopFromQueue(L);
    }
  }

  // Rewire every iteration's exit branch to point to the next iteration:
  for(unsigned i = 0; i < Latches.size(); i++) {
    // Wire the previous iteration's jump to this block
    BasicBlock* thisLatch = Latches[i];
    TerminatorInst* latchTerm = thisLatch->getTerminator();

    if ((!keepLatchExits) && (!doPeel) && (i+1) != BreakoutTrip && (TripMultiple == 0 || (i+1) % TripMultiple != 0)) {

      // Destroy any edges currently targeted outside the loop.
      for(unsigned i = 0; i < LatchExitBlocks.size(); ++i) {

	removeTerminatorEdges(latchTerm, LatchExitBlocks[i]);

      }

    }

    if(i == Latches.size() - 1) {
      if(!doPeel) {
	if(CompletelyUnroll) {
	  
	  removeTerminatorEdges(latchTerm, Headers[i]);

	}
	else {

	  replaceTerminatorEdges(latchTerm, Headers[i], Header);

	}
      }
      else {
	// For peeling the final iteration should be left alone
	continue;
      }
    }
    else {

      // Non-final iteration:
      replaceTerminatorEdges(latchTerm, Headers[i], Headers[i+1]);

    }

  }

  // If we're doing loop peeling, do a name switcheroo such that the last unfolded iteration is named after the original first.
  // This is purely to match the user's idea of preceding the loop with copies of its body.

  if(doPeel) {
    for(std::vector<BasicBlock*>::iterator it = LoopBlocks.begin(); it != LoopBlocks.end(); it++) {
      BasicBlock* firstIterBlock = *it;
      BasicBlock* lastIterBlock = cast<BasicBlock>(LastValueMap[firstIterBlock]);
      std::string tmp = lastIterBlock->getNameStr();
      lastIterBlock->takeName(firstIterBlock);
      firstIterBlock->setName(tmp);
    }
  }

  // Finally, fix LoopSimplify: if we're peeling the loop, we've certainly added branches from outside the loop
  // to the loop exit blocks, and we've broken the preheader by virtue of preceding the loop with the previous iteration's latch

  {
    std::vector<BasicBlock*> newBlocks;
    if(doPeel) {

      for(SmallVector<std::pair<BasicBlock*, BasicBlock*>, 8>::iterator it = ExitingEdges.begin(); it != ExitingEdges.end(); it++) {
	BasicBlock* ExitingBlock = cast<BasicBlock>(LastValueMap[it->first]);
	TerminatorInst *ExitInst = ExitingBlock->getTerminator();
	BasicBlock* ExitBlock = it->second;
	newBlocks.push_back(splitEdge(ExitingBlock, ExitInst, ExitBlock, ExitBlock->getName() + ".peelexit", true));
      }
      // ...and now insert a preheader between the last peel and the loop.
      BasicBlock* LastPeeledLatch = Latches[Latches.size() - 2];
      TerminatorInst* EnterInst = LastPeeledLatch->getTerminator();
      BasicBlock* NewHeader = Headers.back();
      newBlocks.push_back(splitEdge(LastPeeledLatch, EnterInst, NewHeader, NewHeader->getName() + ".peelpreheader", false));
    }
    for(std::vector<BasicBlock*>::iterator it = newBlocks.begin(); it != newBlocks.end(); it++) {
      if(Loop* parent = L->getParentLoop()) {
	parent->addBasicBlockToNewLoop(*it, LI->getBase());
      }
    }
  }
    
  if(!CompletelyUnroll) {
    DEBUG(dbgs() << "Operand loop after unrolling/peeling:\n" << *L << "\n");
    DEBUG(dbgs() << "Function loops after unrolling/peeling:\n");
    DEBUG(LI->print(dbgs()));

    // At this point, the code is well formed.  We now do a quick sweep over the
    // inserted code, doing constant propagation and dead code elimination as we
    // go.
    // Should this be here? Shouldn't IC do this?

    // Don't do this if our caller expects a map of values to peeled values, since this
    // complicates the situation.

    if(!Iterations) {

      const std::vector<BasicBlock*> &NewLoopBlocks = L->getBlocks();
      for (std::vector<BasicBlock*>::const_iterator BB = NewLoopBlocks.begin(),
	     BBE = NewLoopBlocks.end(); BB != BBE; ++BB) {
	for (BasicBlock::iterator I = (*BB)->begin(), E = (*BB)->end(); I != E; ) {
	  Instruction *Inst = I++;
	
	  if (isInstructionTriviallyDead(Inst))
	    (*BB)->getInstList().erase(Inst);
	  else if (Constant *C = ConstantFoldInstruction(Inst)) {
	    Inst->replaceAllUsesWith(C);
	    (*BB)->getInstList().erase(Inst);
	  }
	}
      }

    }

  }
    
  NumCompletelyUnrolled += CompletelyUnroll;
  ++NumUnrolled;
  
  return true;
}
