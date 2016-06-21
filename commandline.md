---
layout: page
title: Command-line options
permalink: /commandline/
---

This is a full listing of LLPE's command-line arguments. Note various of these need you to name basic blocks, for which the `nameblocks` pre-pass will likely be required (see, for example, the conditional specialisation usage example).

#### Input

* `-llpe-root fname`: start analysis at function `fname` entry point (default `main`).
* `-llpe-target-stack fname,bbname,index`: construct a target stack that constitutes the region of interest for specialisation. For example, I might want to specialise function `h` specifically for the case when it is called via the path `f -> g -> h`, and could specify this using the directive `-llpe-root f -llpe-target-stack f,1,2 -llpe-target-stack g,3,4`, where function `f` block `1` instruction 2 is a call to `g` and `g` block `3` instruction 4 is a call to `h`. By contrast with simply using `-llpe-root h` we will be able to assume the calling environment implied by `f` and `g`. Any path that would miss the target call(s) will lead immediately to unspecialised code. When a target stack is in use, path condition directives (see below) may specify an integer stack index instead of a function name to provide a path condition about a specific specialisation context instead of every invocation of a particular function.
* `-spec-env idx,envfile`: load key=value file `envfile` and pass it to the specialisation root argument `idx` as an `environ` style `char**`.
* `-spec-argv argc_idx,argv_idx,argfile`: similarly, load line-delimited `argfile` and pass appropriate `argc` and `argv` values to the specialisation root function.
* `-spec-param idx,value`: unconditionally set specialisation root argument `idx` to `value`, where `value` can be an integer, constant string or function name. No runtime check is produced.
* `-int-spec-stdin filename`: specialise assuming that reads from `stdin` yield the contents of file `filename`.
* `-llpe-use-global-initialisers`: Assume all globals have their initialiser values when the specialisation root is entered.
* `-llpe-force-noalias-arg N`: Assume that specialisation root function argument `N` does not alias any global or other pointer argument to the root function.


#### Output

* `-integrator-accept-all`: Don't show the GUI; just accept whatever specialisation decisions would have been taken per default.
* `-llpe-graphs-dir DIR`: Set where to output `dot` and `png` files for the GUI / for subsequent user reference.
* `-llpe-verbose-overdef`: Report on stderr when an analysed instruction causes us to clear symbolic memory, usually because it wrote to an unknown address.
* `-llpe-verbose-path-conditions`: Output a program that reports on stderr when specialised code is entered and exited, and for what reason.
* `-llpe-prelude-fn fname`: Nominates a particular function to have the `lliowd_init` call added that initiates communication with LLPE's file-watcher daemon, for the case where file contents were read during specialisation. For example, it might be profitable to do this at the top of `main` rather than re-check our connection every time specialised code is entered. Default: the specialisation root.
* `-llpe-prelude-stackidx index`: as above, but specify a stack index when `llpe-target-stack` is in use instead of naming a function.
* `-llpe-write-llio-conf pathname`: Write a configuration file suitable for LLPE's file-watcher daemon as `pathname`. Default: write to stdout.
* `-llpe-stats-file pathname`: Report summary statistics concerning specialisation to `pathname`.
* `-llpe-omit-checks`: Omit path condition checks, checks against thread interference, checks against concurrent modification of files. This effectively makes all specialisation unconditional, and thus unly correct if you can externally verify them before and/or during execution of the specialised code produced.
* `-llpe-omit-malloc-checks`: Also omit checks against `malloc` et al failing at runtime. The resulting program's behaviour if allocation does fail is unpredictable.
* `-llpe-force-split fname`: When dividing the output program into residual functions, force LLPE to start a new function at any specialisation context concerning function `fname`. If no split points are specified, LLPE will try to emit output functions of roughly 10,000 instructions each.
* `-llpe-emit-fake-debug`: Write dummy debug information attributing each target instruction to a specialisation context number and basic block name. Useful for tracking back from a faulting specialised program to the context that generated the code.

#### Specialisation directives

* `-llpe-always-inline function`: Always create a new specialisation context for `function`, even if it appears to be a recursive call. This might produce an infinite specialisation tree if it can in fact recurse indefinitely.
* `-llpe-always-explore function`: Always act as if the given function is certain to be entered (i.e. explore child calls and loops in detail).
* `-llpe-optimistic-loop fname,bb1,bb2`: If we're investigating a loop in function `fname` and the edge `bb1 -> bb2` is shown unreachable, investigate another iteration. In other words, assume that the loop will always exit using that edge, or at least an exit using that edge will terminate specialisation.
* `-llpe-always-iterate fname,header`: Always keep investigating iterations for loop `header` in function `fname` until the latch edge is shown unreachable.
* `-llpe-assume-edge fname,bb1,bb2`: Assume that edge `bb1 -> bb2` in function `fname` will be taken for the purposes of deciding whether to explore loops and recursive functions in detail. Normally only loops that are certain to be entered given the specialisation assumptions will be explored in detail; now if `bb1` might branch to another target `bb3`, the successor `bb2` will be treated as if it was also in straight-line code.
* `-llpe-ignore-loop fname,header`: Don't create per-iteration specialisation contexts for loop `header` in function `fname`, even if it is certain to be entered given the specialisation assumptions. Child loops may be investigated in detail however. May be broken as of LLVM 3.6.
* `-llpe-ignore-loop-children fname,header`: as above, but don't investigate child loops either.
* `-llpe-loop-max N`: stop exploring any loop that would iterate more than `N` times; investigate the general case of the loop body instead in this case.
* `-llpe-malloc-alignment BYTES`: Assume anything allocated by `malloc` is aligned to `BYTES` granularity
* `-llpe-stop-after N`: Create at most N specialisation contexts.
* `-llpe-special-location fname,size`: Mark function `fname` as returning a single `size`-byte object that does not alias any visible global, stack or heap allocation. Effectively the function is treated as an extra global; this may be useful for some implementations of `errno`, for example, to avoid having to analyse thread-local storage. Note multiple calls to the annotated function return the *same* object (i.e. it is not an allocator).
* `-llpe-model-function realf,modelf`: Mark `realf` as modelled by `modelf`: whenever a call to `realf` is encountered `modelf` will be analysed instead. For example, `realf` could be a hard-to-analyse efficient implementation (for example, one that depends on memory alignment) and `modelf` could be a simpler implementation that has the same side-effects. `modelf` may call `malloc` to indicate that `realf` introduces some new object (i.e. one that doesn't alias any other visible object).
* `-llpe-allocator-fn mallocname,mallocarg,freename,freearg`: Annotate function `mallocname`, which takes an allocation size as parameter `mallocarg`, and `freename`, which takes a pointer to free as parameter `freearg`, to be treated analogous to `malloc` and `free`. For example, functions `myalloc` and `myfree` with the same prototypes as `malloc` and `free` could be specified: `-llpe-allocator-fn myalloc,0,myfree,0`
* `-llpe-allocator-fn-const allocname,allocsize,freename,freearg,reallocname,reallocptrarg,reallocsizearg`: similar to above, but `allocname` doesn't take a size as a parameter but instead always returns objects of size `allocsize`. `reallocname` works like `realloc`, taking a pointer as `reallocptrarg` and a size argument `reallocsizearg`.
* `-llpe-never-inline fname`: Never create a specialisation context for `fname`; just treat it as a barrier with unknown side-effects.
* `-int-elim-read-checks`: Try to eliminate redundant checks against concurrent file modification, assuming it is only necessary to check again after a thread yield point. The resulting program may be incorrect if another process alters a specialised file.

#### Concurrency annotations

* `-llpe-single-threaded`: Assume there is only one thread of control, including due to signal handlers, which in this case must not interact with the path under specialisation. Checks that would otherwise be required at apparent yield points are omitted.
* `-llpe-yield-function fname`: Mark `fname` as a function that shouldn't be analysed, which may alter any memory, but is *expected* not to. Thus it is treated the same as a thread yield point, after which the specialised program will need to check against possible side-effects, but more optimistically than an undefined function, where we pessimistically drop all knowledge regarding symbolic memory. This could be useful to annotate a mutex-unlock function, for example.
* `-llpe-simple-volatile-load fname,bbname,index`: mark `volatile` load instruction in function `fname` / block `bbname` / position `index` as *simple*, meaning that the `volatile` modifier only implies that the loaded value itself may be unrepeatable (e.g. for a mapped hardware register), not that general thread interference might have occurred. Unannotated volatiles are treated as thread yield points which may corrupt any memory.
* `-llpe-lock-domain fname,bbname,index,global1[,global2[,global3...]]`: mark the call at function `fname` / block `bbname` / position `index` as acquiring a lock that controls access to the given list of globals only (thus only those globals need to be checked for concurrent modification after it is acquired). Unannotated locks may govern access to any memory, so a global recheck becomes necessary.
* `-llpe-pessimistic-lock fname,bbname,index`: mark the call at function `fname` / block `bbname` / position `index` as acquiring a lock that is *expected* to have been held by other threads since it was last acquired. Thus the lock's domain (or all memory, if no domain is given) is cleared in symbolic memory, rather than just being marked for re-checking as in the default, optimistic case.

#### Path conditions

Path conditions specify that we are to make some assumption about a particular value or memory location as of some point in the program. A runtime check will be emitted to ensure that this is truly the case (and branch to unspecialised code otherwise), and specialisation will proceed using the assumption.

Their arguments have the general format `targetFunction,targetBB,targetIndex,assumption,assumeFunction,assumeBB[,offset]`, which means: assume that `targetFunction` block `targetBB` instructionn #`targetIndex` takes value `assumption` as of the top of `assumeFunction` block `assumeBB`. The optional `offset` applies to the target instruction, and only makes sense when it is pointer-typed. For example, `llpe-path-condition-str "f,1,0,Hello world!,f,2,16" would mean to assume that if `f` block `1` begins with `%x = alloca [ 128 x i8 ]`, assume that `(char*)(x + 16)` contains C-string `Hello world!` as of `f` block `2`. The specific arguments affect the nature of the assumption.

The target block can be special value `__args__`, in which case `targetIndex` specifies an argument, or `__globals__`, in which case `targetIndex` should be replaced with a global name.

* `-llpe-path-condition-int`: target is an integer-typed instruction; assumption is an integer; offset is not applicable.
* `-llpe-path-condition-fptr`: target is an function-pointer-typed instruction; assumption is a function name; offset is not applicable.
* `-llpe-path-condition-str`: target is an pointer-typed instruction; assumption is a string.
* `-llpe-path-condition-intmem`: target is an pointer-to-integer-typed instruction; assumption is an integer (written with width relating to the type of the target).
* `-llpe-path-condition-fptrmem`: target is a pointer-typed instruction; assumption is a function name.
* `-llpe-path-condition-stream`: target is an instruction with the same type as a file descriptor; assumption is filename containing the data that the file descriptor will yield from this point on.
* `-llpe-path-condition-global-unmodified`: target is a global; assumption is ignored; the global will be assumed to retain its initialiser value from the specified assumption point.

The following special path condition is also possible:

* `-llpe-path-condition-func targetFunction,targetBlock,assumeFunction,verifyFunction[,arg1Function,arg1Block,arg1Index[,arg2Function...]]`: at the top of `targetFunction` block `targetBlock`, execute `assumeFunction` during specialisation to make some arbitrary writes to memory or other side-effects expressing an assumption, and then `verifyFunction` at runtime to check that the assumption holds. `argNFunction`, `Block` and `Index` specify values to be passed to both the assume and verify functions. For example, the assume function might set up some complex data structure and then the verify function check that it is as expected.

#### Sub-passes

* `-skip-benefit-analysis`: disable automatic guessing of which contexts should and shouldn't be enabled (emitted as specialised code).
* `-skip-llpe-die`: skip dead instruction analysis.
* `-skip-check-elim`: skip eliminating redundant checks against thread interference.
* `-llpe-enable-sharing`: share function specialisation contexts when possible. Almost certainly bit-rotted beyond use at the moment.
* `-llpe-verbose-sharing`: report when function sharing happens.
* `-int-skip-post-commit`: skip the last optimisation stage, when e.g. basic blocks with a single predecessor and successor are merged. Useful if you want to know the original block name for a particular instruction.












