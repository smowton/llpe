---
layout: page
title: Developer Documentation - Dead Store Elimination
permalink: /devdocs-dse/
---

In addition to its main task of eliminating instructions that can be resolved to constants during specialisation, LLPE also looks to remove store instructions that are no longer necessary because all of the loads that they would feed have themselves gone away. To this end, LLPE maintains another store object, parallel to the main symbolic memory store, which records the store instructions that have contributed to different objects and different offsets within them in symbolic memory. Like the conventional symbolic store, the DSE store is copied (using CoW data structures to reduce the cost) when control flow diverges, and stores are merged at control flow convergence.

Store instructions overwrite this store (called the DSE store) with a reference to themselves; load and other memory-writing instructions that are not resolved to constants during specialisation will be executed at runtime, so they mark any store instruction they may draw from as *needed*. Stores which are eliminated from the DSE store by overwriting, or by an object scope ending, are eliminated from the specialised program.

The same system also eliminates other instructions that write to memory: it determines whether file reads performed during specialisation need to turn into a memcpy-from-constant at runtime, or can be eliminated entirely, and similarly whether user `memset`, `memcpy` and other memory writing operations can be eliminated.

Dead store elimination is frustrated somewhat in the presence of disabled specialisation contexts: those which were analysed, but will not generate specialised code variants in the specialised program. The memory-reading instructions in a disabled context will happen at specialisation time, even if we know what their results will be in advance, so the stores must remain too. Other barriers to dead store elimination include any instruction that might branch to unspecialised code (for example, a load that has to be checked against possible thread interference, or a block with a user-specified path condition), or by anything with unknown side-effects, such as a call to an external function.

DSE is usually executed at the same time as the main LLPE analysis, examining each instruction after the main pass has. However when dealing with unbounded loops (i.e. loops where we're examining a general iteration instead of individually analysing each iteration), DSE is run over the whole loop after the main analysis has found a fixed point solution.

If you're looking to understand DSE in more depth or improve it, you should mainly be looking at `DSE.cpp`.

#### Dead Instruction Elimination

Eliminating stores might leave some other instructions un-needed, such as pointer calculations. These are eliminated by the dead instruction elimination analysis, which runs over a context in *reverse* topological order immediately before specialised code is generated. In theory this is identical to LLVM's built-in dead code elimination pass, but in practice it is too expensive to generate and then immediately eliminate so much code.