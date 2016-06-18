---
layout: page
title: Developer Documentation - Overview
permalink: /devdocs-overview/
---

LLPE analyses an LLVM bitcode program and generates a variant specialised with respect to some user-specified assumptions. These might be command-line arguments, intermediate values computed during specialisation, or input data read from files or standard input. This document gives a high-level overview of the important methods and data structures used by LLPE.

## Source Tree Layout

* At top level, only the `llpe` and `lliowd` directories are currently relevant. Most others contain examples and documentation, or old code that is pending either removal or re-integration.
* Important headers are in `llpe/include/llvm/Analysis/LLPE`.	       
* LLPE's main analyses are implemented in `llpe/main`.
* The GUI and driver are implemented in `llpe/driver`.
* Utilities for preparing and post-processing specialised programs are in `llpe/utils`.
* `lliowd` implements a file-watcher daemon for use with specialised programs.

## Top-level overview

The main LLPE analysis is implemented as an LLVM `ModulePass` called `LLPEAnalysisPass`, mainly implemented in `llpe/main/TopLevel.cpp`. It creates a tree of *specialisation contexts*, which are instances of either `InlineAttempt`, representing a particular function call, or `PeelAttempt` and `PeelIteration`, representing an iteration of a loop. The contexts roughly follow the expected flow of execution in the specialised program -- so for example, if `f` calls `g` which in turn calls `h` within a loop, we'd expect to see a tree `f -> g -> Loop 1`, with Loop 1 having an array of child loop iterations and an `h` call hanging off each.

LLPE represents the program using *shadow objects* that roughly align with LLVM's `Function`, `BasicBlock`, `Instruction` and so on. `BasicBlock`, for example, gives LLVM's representation of a particular block; `ShadowBBInvar` gives a digested view of the block in general (for example, it describes the block's successors and predecessors), and `ShadowBB` represents a particular instance of the block (for example, it indicates which predecessor and successor edges are live in a particular context). Thus for one `BasicBlock` we will create one `ShadowBBInvar` the first time we need to describe that block but many `ShadowBB` instances, one for each `InlineAttempt` or `PeelIteration` that deals with the block. Similarly, LLVM's `Instruction` is shadowed by `ShadowInstructionInvar`, which gives arguments and users in a cheaper, more usable format than LLVM's `use_iterator` et al, and `ShadowInstruction`, which stores the instruction's result, whether it is dead or alive, and so on for a particular dynamic instance of the instruction.

When analysing a particular specialisation context, LLPE assigns each argument and instruction an `ImprovedValSet`. This is usually a set of `ImprovedVal` objects, which can in turn represent a plain old `Constant`, a symbolic pointer and offset, a symbolic file descriptor, a set of any of these (e.g. "global `x` or stack-allocated object `y` or `null`), or rarely, using `ImprovedValSetMulti`, a concatenation of them (for example, a file descriptor and a constant in the high and low words of an `int64`). Ideally we want to assign instructions *definite* values, but since not all information is available during specialisation sometimes we will resolve them to a pointer with a known target but an unknown offset, or even an "Overdef" value indicating the instruction could have any result at all.

Allocation, load, store and other memory operations are executed against a symbolic store which is copied and merged following the structure of the control-flow graph (implemented in `LoadForward.cpp`). Similar symbolic store objects are used to track when stores are needed in the specialised program (`DSE.cpp`), when memory contents may have been perturbed due to multi-threading (`TentativeLoads.cpp`), and to maintain a symbolic file descriptor table when specialising with respect to file contents (`VFSOps.cpp`).

After a given context has been analysed it is emitted as specialised bitcode (see `Save.cpp`), omitting instructions and control-flow decisions that could be resolved for certain during specialisation and retaining those which are still unknown and must be evaluated at runtime. The specialised program may contain runtime checks that specialised code is usable -- e.g. if user input matches assumptions made at specialisation time, or that thread interference hasn't invalidated our results. In this case LLPE will clone (part of) the unspecialised program, and specialised code will branch into it when aruntime checks fail. Code for dealing with this eventuality is mostly found in `ConditionalSpec.cpp`.

## Walking the basic block graph

The top-level CFG-walking code is implemented in `MainLoop.cpp`; terminator instruction evaluation is in `CFGEval.cpp`, and ordinary instruction evaluation is in `Eval.cpp`.

LLPE starts by creating an `InlineAttempt` representing the specialisation root function, which is `main` per default but can be set with the `-llpe-root` command-line argument. It then considers the basic blocks in that function one by one, in topological order. 

LLPE tracks which blocks are *certain* to be entered when the given specialisation assumptions hold. A block is marked certain when its predecessor is certain and its terminator branch is unconditional, or can be resolved to a single target during specialisation.

When it finds a call instruction within a block, a new `InlineAttempt` is usually created representing the new call context, and analysis continues within the new function. However if the calling block is not certain to be reached, and the call would be recursive (i.e. the same callee is already somewhere on the current stack), an `InlineAttempt` is not created and the call is assumed to have arbitrary result and side-effects.

Similarly, upon encountering a loop, if the entry block is certain to be reached LLPE creates a `PeelAttempt` and a first `PeelIteration`, representing the first iteration of the loop, and analyses each iteration in turn. If no `PeelAttempt` was created due to uncertainty, or the loop's iteration count cannot be established (i.e. for some iteration we find both an exit edge and the latch edge feasible) then the general case of the loop body is analysed in the parent specialisation context.

This treatment of loops and recursion is a little asymmetrical -- calls are always explored until unbounded recursion is shown to be possible but when it is a maximally pessimistic assumption is made, whilst investigating each loop iteration individually is not even attempted unless the loop is certain to be entered, but when it isn't (or when it fails), the general-case analysis might achieve a useful bound on its side-effects. A useful future development of LLPE would be to generalise the treatment of re-entrant code to remove this asymmetry.

The trickiest part of specialisation happens when we can't be certain of control flow at specialisation time -- for example, when a conditional branch depends on the system time, or something else we can't know until runtime. In this case both successor blocks are analysed and the symbolic store objects are (notionally) copied. When control flow converges again, phi instructions are assigned result sets rather than single concrete results, and the symbolic store objects are merged, possibly resulting in sets or wholly unkown values at certain positions in memory. Any instruction with anything but a single concrete result will be evaluated at runtime, but partial information such as a set of possible values will be used to determine future control flow among other things.