---
layout: page
title: Tutorial
permalink: /tutorial/
---

You will need: a [built](/build) LLPE library and a C-to-LLVM compiler (e.g. [clang](http://clang.llvm.org/))

Here we'll specialise a simple program to see LLPE's basic capabilities and ways of working. LLPE is run using LLVM's <tt>opt</tt> tool, which runs one or more analysis or optimisation passes over the source program. It requires that all loops in the source program have been placed in canonical form (having a unique preheader, header and latch) and dataflow out of the loop is represented in loop-closed SSA form; thus the standard invocation to prepare and specialise a program is:

```
opt -load /path/to/llpe/build/main/libLLVMLLPEMain.so -load /path/to/llpe/build/driver/libLLVMLLPEDriver.so -loop-simplify -lcssa -llpe unspecialised.bc -o specialised.bc
```

In the example below I will abbreviate this <tt>$LLPE_OPT unspecialised.bc -o specialised.bc</tt>

Rarely, loops cannot be represented in canonical form, usually because <tt>goto</tt> statements are used to enter and exit the loop in several places. LLPE will warn you that manual intervention is necessary in this case.

## LLPE as an interpreter

The very simplest case: we'll feed LLPE a program that has a predictable constant result, but which pointlessly recomputes that result every time it is run.

The source program:

```
int main(int argc, char** argv) {

    int ret = 0;
    for(int i = 0; i < 100; ++i)
    	ret += i;
    return ret;

}
```

We can have LLPE interpret the program using:

```
clang source.c -c -emit-llvm -o source.bc
$LLPE_OPT source.bc -o spec.bc
```

LLPE's GUI will appear, showing on the left a tree of the contexts LLPE explored and on the right a graphical representation of the selected context. In this case we just see the root function and an expandable node showing each loop iteration that LLPE explored. It shows a some columns of data for each such context:

* Inst: the number of instructions in a particular context.
* Elim: of which, eliminated through specialisation.
* Use?: checkboxes that could be used to instruct LLPE to discard a particular specialisation and use the unmodified loop or function concerned.
* Barrier: Warnings of particular severe problems encountered, such as writes that may alter any object in memory.

Note the program's instructions are highlighted green (resolved to a constant) or red (un-needed in the specialised program) and are annotated with constant results, and the basic blocks are highlighted in yellow (certain to be executed) or green (certain to be executed, and not within any loop). Control flow edges are drawn in grey when proven unreachable; unreachable blocks are not usually drawn at all but can be shown or hidden by clicking File -> Brief.

When you're done inspecting the results, click File -> Exit. The specialised bitcode file will be written to <tt>spec.bc</tt>. The GUI phase can also be skipped entirely by passing <tt>-integrator-accept-all</tt> on the command line.

View the specialised bitcode using <tt>llvm-dis spec.bc -o -</tt>. As well as the original <tt>main</tt> function, renamed <tt>main.old</tt>, there is a new variant:

```
define i32 @main(i32 %argc, i8** %argv) {
  ret i32 4950
}
```

The specialised bitcode can now be compiled, linked and run the usual way:

```
clang spec.bc -o spec
./spec
```

In this particular example, it was important not to run <tt>clang</tt> with any optmisation flags, or it would have achieved the same simplification for us! LLPE comes into its own, however, when the input programs are sufficiently complex that Clang's or LLVM's conventional optimisers cannot fully exploit the opportunities available.

