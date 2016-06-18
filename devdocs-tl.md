---
layout: page
title: Developer Documentation - Handling Multithreading
permalink: /devdocs-tl/
---

LLPE can specialise code which operates in the presence of multiple threads, but where the principle flow of control is single-threaded. That is, it cannot meaningfully analyse inter-thread communication, but it can produce appropriately checked specialisations that remain correct even when there is unexpected interference by another thread.

The most pessimistic solution would simply suppose that whenever, according to the LLVM memory model, another thread might overwrite the contents of memory, we should discard all of symbolic memory. However, since thread yield points are quite frequent this would probably produce an unacceptably poor specialisation. LLPE improves on this by tracking when our knowledge about symbolic memory has potentially been corrupted.

We maintain another symbolic store object (a `TLLocalStore` object) alongside the main store, which tracks which symbolic objects, and which offsets within them, have been checked since the last potential thread interference, and therefore which are *known good* as of a particular point in execution.

Thread interference might happen whenever we find a memory operation that has a memory ordering attribute, or that has the `volatile` attribute, or on an explicit `fence` instruction. At this point the entire TLStore must be cleared to indicate that arbitrary data may have been overwritten. Then a load instruction with a known source address will result in a runtime check (and so a possible branch to unspecialised code), and can note that the checked bytes are known good for the time being. A subsequent load from the same address would not need checking, since the check would be redundant.

Note that in practice a second check could actually fail, because the results of the other thread's memory operations may become visible *sooner* than the memory model requires -- however it is legal for us to assume they do not.

`TLLocalStore` objects are copied, forked and merged just like the symbolic memory store and the dead-store-elimination store. Since they are effectively just boolean per-byte flags indicating whether a check has been made recently or not, a merged store is simply the intersection of the known-good sets of its predecessors.

The main constant propagation analysis proceeds on the assumption that a check against thread interference finds no change -- thus LLPE is generally *optimistic* that a thread yield point has no relevant effects (compare it is *pessimistic* that a call to an unknown external function will have relevant side-effects and responds by clearing symbolic memory). If this is not appropriate, the user can annotate particular functions as pessimistic yields instead.

LLPE makes a couple of further steps to limit the number of runtime checks that are needed by maintaining a list of locations that are known to be thread local as of a particular instruction or basic block instance. Locations are tagged thread-local when allocated, and potentially-global when their address is written to memory. Thread local objects naturally cannot be overwritten by another thread and so are exempt from checking for the time being.

Like the dead store elimination passlet, in straight line code the tentative load store gets updated immediately after each instruction is analysed, but when analysing the general case of a loop body the whole loop (and its children) are analysed after value analysis has reached a fixed-point solution.

The implementation for all of this can be found in `TentativeLoads.cpp`.