---
layout: page
title: Customising specialisation paths
permalink: /specpaths/
---

This example will show how to specialise in detail a code path which isn't certain to be reached.

Consider this example program:

```cpp
int get_chksum(const char* ptr, int kind) {

  int chksum;
  
  if(kind) {
    for(chksum = 0; *ptr; ++ptr)
      chksum += *ptr;
  }
  else {
    for(chksum = 1; *ptr; ++ptr)
      chksum *= *ptr;
  }

  return chksum;

}

int main(int argc, char** argv) {

  return get_chksum(argv[1], argc >= 3);

}
```

If we try to specialise `get_chksum` giving a value for `ptr` but not `kind`, the results will be poor. For example, first compile and name blocks:

```
clang paths.c -c -emit-llvm -o paths.bc
opt -load /path/to/llpe/utils/libLLVMLLPEUtils.so -nameblocks paths.bc -o paths_names.bc
```

Then try to specialise:

```
$LLPE_OPT -llpe paths_names.bc -o pathsspec.bc -llpe-root get_chksum -spec-param 0,Hello
```

We've given an (unconditional) value for `ptr` with the `spec-param` argument, but if you look at the specialiser GUI you'll see the loop body is not unrolled, and the instructions within the loop are not evaluated, because neither loop was certain to be entered given our specialisation assumptions (in particular, the test on the argument `kind` makes it uncertain which loop will run).

However if we add this argument (assuming the `kind` test block is named `1` and one of its successors is named `2`):

```
-llpe-assume-edge get_chksum,1,2
```

Then re-running specialisation will show that the loop is expanded per-iteration as if it was certain to be executed. Note the orange highlights on the basic blocks reached in this way, indicating that an assume-edge directive was necessary to get them investigated in detail.

You could also specify `-llpe-assume-edge get_chksum,1,3` (where `3` is the name I get for the *other* loop's preheader) to force it to explore *both* loops.