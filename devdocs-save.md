---
layout: page
title: Developer Documentation - Emitting Specialised Code
permalink: /devdocs-save/
---

Once LLPE's various analyses have completed, we know which instructions have been resolved to constants or known symbolic pointers, which have been shown to be useless in the specialised program, which require runtime checks to ensure that they match expectations, and so on. At this point we can emit a specialised variant of the user's specialisation root function and rewrite the surrounding object to use it.

Instructions which have been resolved to an LLVM `Constant` can simply be replaced entirely at runtime. Those which have been resolved to pointers are replaced by direct references to the allocation instruction, perhaps with a `getelementptr` instruction and cast, if they are needed at runtime. Similarly file descriptors that are needed at runtime become direct references to the `open` instruction that generated the symbolic file descriptor.

If an allocation instruction belongs to a disabled specialisation context (an `InlineAttempt` or `PeelIteration` which won't generate specialised code), it cannot be directly referenced since there won't be a unique instruction that corresponds to the allocation. The main analysis phase prevents us from referring to it in this case (see `squashUnavailableObjects`). However if a particular instruction can be shown to load that pointer it can serve as a replacement (see `replaceUnavailableObjects`) which can be used in lieu of the actual allocation instruction. 

One difficult task for the save phase is to generate unspecialised code variants when a runtime check might fail and so it is necessary to retain a general version of the function. This requires us to generate phi nodes unifying the specialised and unspecialised variants of incoming dataflow edges, and/or add to existing top-of-block phi nodes.

It must also decide how to divide the specialised code up into residual functions. The simple cases of emitting a single massive function or emitting a residual function per `InlineAttempt` are both unsatisfactory, because the former chokes conventional LLVM optimisation passes that assume reasonably-sized functions and the latter chokes the inliner, which does not expect to find large numbers of small functions with single callers and callees. Therefore it tries to find moderately-sized chunks of code to emit as separate functions, although its hand is forced at varargs functions which require a function entry point so that varargs instructions will work as expected.

This introduces a problem when referring to allocation instructions that end up residualised into a different function. This is worked around by storing such remotely-referenced allocations into a global variable and loading from that global at each 'remote' reference (see `fixNonLocalUses`). Alternatively we could have simply allowed the pointer to make its way to the consuming load instruction as in the original program; however this would have required us to rerun all the dead code analyses.

Code which is emitted out-of-line and which contains runtime checks must signal to its caller that it has failed a check, so the caller should also branch to unspecialised code. This is achieved by replacing the function's return type with a structure containing an additional boolean indicating whether a check failure has occurred. Code which is emitted inline with its parent context simply returns via a different residual block when a check has failed.

The commit phase doesn't wait until the whole main analysis has run, but rather commits specialisation contexts as soon as we know we won't need to reanalyse them (in straight-line code, on function exit). This means that we may end up committing code that refers to some external artefact (e.g. an allocation) before the code that defines it. In this case we add a *patch* request that asks the outside context to supply an argument once it becomes available. See `addPatchRequest`.

Files to look at if you want to get into the save / commit phase in detail:

* `Save.cpp`: code that commits specialised code variants, tries to produce concrete synthesis of symbolic pointers, introduces value checks when required by user assertions or thread interference checks, etc.
* `ConditionalSpec.cpp`: code that clones unspecialised basic blocks and generates / augments phi nodes to accomodate branches from specialised to unspecialised code.
* `SaveSplit.cpp`: code that decides how to split the committed code into residual functions.

