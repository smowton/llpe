---
layout: page
title: Developer Documentation - Symbolic Memory
permalink: /devdocs-memory/
---

When programs under investigation execute allocation instructions, including `alloca` which allocates stack memory and `malloc` and others which allocate heap memory, symbolic memory locations are created and henceforth propagated with control flow and operated on by `load`, `store` and other memory operations.

The symbolic store as a whole is represented by `OrdinaryLocalStore`, which consists of a list of stack frames and a global heap (which also contains locations representing global variables, and other special locations). The store as a whole is a copy-on-write object, so sharing it during loops or other control flow divergences is cheap if they don't actually operate on memory. Stack frames are created and destroyed as calls are entered and exited; they may also be extended due to variable-length arrays on the stack, user `alloca` calls and similar. The heap is appended to whenever `malloc` or a user-annotated allocator is encountered.

Each memory location is represented by an `ImprovedValSet`. This can be an `ImprovedValSetSingle` (capable of representing a set of values such as `{ i32 0, i32 5 }`) or `ImprovedValSetMulti` (a list of `ImprovedValSetSingle` instances, so it can represent e.g. struct types). To make sparse alterations to large allocations cheap, `ImprovedValSetMulti` is itself copy-on-write, and can have a *base object* that it shadows -- for example, if a simple struct like `struct X { int a; int b; int c; int d; }` was initially zeroed, resulting in representation `[ i32 0, i32 0, i32 0, i32 0 ]`, then only the third member was overwritten with a 1, it can be represented as `[ 8-12 i32 1 ] -> [ i32 0, i32 0, i32 0, i32 0 ]`, where `8-12` is the top object's offset and `->` indicates the base object pointer.

The `ImprovedValSet` objects themselves consist of `ImprovedVal` instances; these finally are a `ShadowValue` plus an optional offset field, used to indicate pointer offsets. `ShadowValue` can represent many different types of data as enumerated by `ShadowValType`:

* `SHADOWVAL_CI8`, `_CI16` et al: raw constant integers. These are not stored as `ConstantInt` because that class is both considerably larger than a plain integer, and cannot be deleted, so using it to represent intermediate values would result in prohibitive memory usage. This did require some copy-and-pasting of the LLVM constant folder, however.
* `SHADOWVAL_OTHER`: any other `Constant`, such as a floating-point constant. In theory these have the same problem as `ConstantInt`, but in LLPE's practical use so far the problem has not come up.
* `SHADOWVAL_PTRIDX`: a (frame index, object index) pair identifying a stack frame and object. If the stack frame is -1, object index refers to the heap.
* `SHADOWVAL_FDIDX` and `SHADOWVAL_FXIDX64`: 32-bit and 64-bit symbolic file descriptors, respectively. They refer to the block-local `FDStore`, which is maintained similarly to the symbolic store.

`ShadowValue` can also refer to some other types of value which cannot be stored in memory: `SHADOWVAL_ARG`, `_INST` and `_GV` are used to note instruction def-use chains, and are not relevant to symbolic memory.

Thus to sum up the memory objects:

* `ShadowValue` can describe "constant integer 1" or "the second allocation in my parent function"
* `ImprovedVal` adds an offset field, irrelevant to constants but able to describe "offset 16 in the second allocation in my parent function"
* `ImprovedValSetSingle` is a set of those, so it can describe `{ global X offset 0, parent-allocation-2 offset 16 }`
* `ImprovedValSetMulti` is a list of Singles, so it can describe a struct with many pointer fields, for example.

One important thing to note about the symbolic store: the LLVM type system is almost entirely irrelevant to its implementation. Struct members and similar are described by byte offsets, not field numbers, and operations such as casting pointers to and from `uint64` are entirely invisible, as are reinterpreting for example a byte array as a single large byte array or floating-point number. Some casts will be impossible to evaluate however, such as taking the top 32 bits of a pointer and combining it with a constant (we can't know ahead of time what the constant result would be, and it is meaningless as a pointer). Certain comparisons are also impossible, such as whether a pointer is numerically greater than an independently-allocated object. A special function `integrator_same_object` is provided to allow user-supplied models to replace the common use case `x >= base && x < base + offset` used to determine whether `x` belongs to a particular object `base`.

Useful files to read when investigating / improving the symbolic memory implementation:

* `include/llvm/Analysis/SharedTree.h`: implementation of the copy-on-write store and frame-lists that compose the symbolic store.
* `main/LoadForward.cpp`: functions that read and write the symbolic store, called on executing load, store, allocation and other instructions.
* `main/MainLoop.cpp`: logic that passes the symbolic store between basic blocks, into and out of called functions and loops, forks / merges it when necessary, and so on.