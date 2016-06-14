//===- TLDump.cpp ---------------------------------------------------------===//
//
// The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/LLPE.h"

// Debugging functions that dunp the state of the tentative-load or dead-store analysis code.

namespace llvm {

  void TLDump(IntegrationAttempt* IA) {

    for(uint32_t i = IA->BBsOffset, ilim = IA->BBsOffset + IA->nBBs; i != ilim; ++i) {

      ShadowBB* BB = IA->getBB(i);
      if(!BB)
	continue;

      PeelAttempt* LPA;
      if(BB->invar->naturalScope && 
	 BB->invar->naturalScope->headerIdx == BB->invar->idx &&
	 (LPA = IA->getPeelAttempt(BB->invar->naturalScope)) &&
	 LPA->isTerminated()) {

	for(uint32_t j = 0, jlim = LPA->Iterations.size(); j != jlim; ++j) {

	  TLDump(LPA->Iterations[j]);

	}

	while(i != ilim && BB->invar->naturalScope->contains(IA->getBBInvar(i)->naturalScope))
	  ++i;
	--i;
	continue;

      }

      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	ShadowInstruction* SI = &BB->insts[j];
	errs() << IA->SeqNumber << " / " << itcache(SI) << ": " << SI->isThreadLocal << "\n";

	if(InlineAttempt* Child = IA->getInlineAttempt(SI))
	  TLDump(Child);

      }

    }

  }

  void DSEDump(IntegrationAttempt* IA) {

    for(uint32_t i = IA->BBsOffset, ilim = IA->BBsOffset + IA->nBBs; i != ilim; ++i) {

      ShadowBB* BB = IA->getBB(i);
      if(!BB)
	continue;

      PeelAttempt* LPA;
      if(BB->invar->naturalScope && 
	 BB->invar->naturalScope->headerIdx == BB->invar->idx &&
	 (LPA = IA->getPeelAttempt(BB->invar->naturalScope)) &&
	 LPA->isTerminated()) {

	for(uint32_t j = 0, jlim = LPA->Iterations.size(); j != jlim; ++j) {

	  DSEDump(LPA->Iterations[j]);

	}

	while(i != ilim && BB->invar->naturalScope->contains(IA->getBBInvar(i)->naturalScope))
	  ++i;
	--i;
	continue;

      }

      for(uint32_t j = 0, jlim = BB->insts.size(); j != jlim; ++j) {

	ShadowInstruction* SI = &BB->insts[j];
	errs() << IA->SeqNumber << " / " << itcache(SI) << ": " << SI->dieStatus << "\n";

	if(InlineAttempt* Child = IA->getInlineAttempt(SI))
	  DSEDump(Child);

      }

    }

  }

}
