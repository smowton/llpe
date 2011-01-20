//===-- LoopUnroll.cpp - Loop unroller pass -------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass implements a simple loop peeler
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "loop-unroll"
#include "llvm/IntrinsicInst.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include <climits>

using namespace llvm;

static cl::opt<unsigned>
PeelCount("peel-count", cl::init(0), cl::Hidden,
  cl::desc("How many iterations to peel"));

static cl::opt<unsigned>
PeelDepthLimit("peel-depth-limit", cl::init(0), cl::Hidden,
	       cl::desc("Loop depth above which we won't do any peeling"));

namespace {
  class LoopPeel : public LoopPass {
  public:
    static char ID; // Pass ID, replacement for typeid
    LoopPeel() : LoopPass(ID) {}

    /// A magic value for use with the Threshold parameter to indicate
    /// that the loop unroll should be performed regardless of how much
    /// code expansion would result.
    static const unsigned NoThreshold = UINT_MAX;

    bool runOnLoop(Loop *L, LPPassManager &LPM);

    /// This transformation requires natural loop information & requires that
    /// loop preheaders be inserted into the CFG...
    ///
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.addRequired<LoopInfo>();
      AU.addPreserved<LoopInfo>();
      AU.addRequiredID(LoopSimplifyID);
      AU.addPreservedID(LoopSimplifyID);
      AU.addRequiredID(LCSSAID);
      AU.addPreservedID(LCSSAID);
      AU.addPreserved<ScalarEvolution>();
      // FIXME: Loop unroll requires LCSSA. And LCSSA requires dom info.
      // If loop unroll does not preserve dom info then LCSSA pass on next
      // loop will receive invalid dom info.
      // For now, recreate dom info, if loop is unrolled.
      AU.addPreserved<DominatorTree>();
    }
  };
}

char LoopPeel::ID = 0;
INITIALIZE_PASS(LoopPeel, "loop-peel", "Peel loops", false, false);

Pass *llvm::createLoopPeelPass() { return new LoopPeel(); }

/// ApproximateLoopSize - Approximate the size of the loop.
//static unsigned ApproximateLoopSize(const Loop *L, unsigned &NumCalls) {
//  CodeMetrics Metrics;
//  for (Loop::block_iterator I = L->block_begin(), E = L->block_end();
//       I != E; ++I)
//    Metrics.analyzeBasicBlock(*I);
//  NumCalls = Metrics.NumCalls;
//  return Metrics.NumInsts;
//}

bool LoopPeel::runOnLoop(Loop *L, LPPassManager &LPM) {
  LoopInfo *LI = &getAnalysis<LoopInfo>();

  unsigned Count = PeelCount;
  unsigned DepthLimit = PeelDepthLimit;

  if(PeelDepthLimit != 0 && L->getLoopDepth() > PeelDepthLimit) {
    DEBUG(dbgs() << "Won't peel loop " << *L << " because of depth limit " << DepthLimit << "\n");
    return false;
  }
  // Peel the loop.
  if(Count > 1) {
   
    BasicBlock *Header = L->getHeader();
    DEBUG(dbgs() << "Loop Peel: F[" << Header->getParent()->getName()
	  << "] Loop %" << Header->getName() << "\n");
    (void)Header;

    if (!UnrollLoop(L, Count, LI, &LPM, true))
      return false;

  }
  else {

    DEBUG(dbgs() << "Not peeling loop because count is " << Count << "\n");

  }

  Function *F = L->getHeader()->getParent();

  // FIXME: Reconstruct dom info, because it is not preserved properly.
  if (DominatorTree *DT = getAnalysisIfAvailable<DominatorTree>())
    DT->runOnFunction(*F);
  return true;
}
