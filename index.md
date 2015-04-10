---
layout: page
title: About LLPE
permalink: /about/
---

LLPE is a partial evaluator for LLVM bitcode. It is suitable for specialising programs written in C, C++, FORTRAN, or any other language that can be compiled to LLVM intermediate representation. Specialisation can used to pare un-needed code from general programs, or to introduce staging to existing programs without manual modification. LLPE is designed to speicalise aggressively with minimal manual input.

Features
--------

* Supports a very large subset of LLVM intermediate representation, including specialising programs that use inter-thread communication, interact with the operating system and partial support for exceptions. It has near-perfect support for the C language, and apart from the exception limitations it has broad C++ support.
* Specialisation can eliminate direct arithmetic operations, control flow, memory operations and memory allocations.
* Specialises programs even when the premises of specialisation may be falsified at runtime (e.g. due to unexpected system call results or interference by other threads); guards are introduced when necessary to ensure correctness by only running specialised code when the premises are satisfied.
* Supports specialisation with respect to expected command-line parameters, file contents or inter-process communication results (where the latter are expressed in terms of the Linux system call API).
* Supports specialisation across translation unit and library boundaries. When used with a C library built as LLVM bitcode (e.g. uClibc can be built this way) this amounts to whole-program specialisation.

Status
------

LLPE is "feature complete" but unstable. It is currently (April 2015) undergoing code cleanup and documentation pending an initial release. As such it is suitable for experimental use (though pending documentation you are likely to need to consult the mailing lists to find your way around), but not for production use.

Other limitations 

Related Software
----------------

LLPE is most obviously applied to specialise C programs. The most prominent existing C partial evaluators are [C-Mix](http://www.diku.dk/OLD/forskning/topps/activities/PartialEvaluation.html) and [Tempo](http://phoenix.inria.fr/software/past-projects/tempo), neither of which are still maintained. Both are offline partial evaluators, which means they prove that a particular program point is suitable for specialisation ''before'' considering the particular values that will be supplied; LLPE is an online partial evaluator, which functions more like an interpreter over partial programs. This should result in more accurate but less efficient specialisation.

Both C-Mix and Tempo are limited by the C language: they require significant user effort to function across translation unit and library boundaries, and are stymied by common operations that are not defined by the language specification (they are ''implementation-defined''), such as casting between pointer and integer types. LLPE inherits support for specialisation across unit boundaries from the LLVM infrastructure, which was designed for whole-program transformations from the outset, and can handle implementation-defined operations because by the time a C program has been lowered to LLVM IR the compiler has cjhosen their machine-level meaning; LLPE simply follows his choice.

To my knowledge C++ partial evaluation has not been significantly tackled before now. Since the C++ frontend compiler has already lowered all of the language's complex features into simple machine-level constructs, LLPE provides strong C++ support (and indeed hybrid C/C++ support) with very little extra effort on top of its treatment of C. The one missing piece is exception support, since parts of exception propagation depend on introspecting on the program binary. Nonetheless LLPE can specialise C++ programs that use exceptions so long as the path the should be specialised does not involve exception propagation (i.e. all exceptions must represent deviations from the desired path).

