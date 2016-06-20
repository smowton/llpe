---
layout: page
title: Unconditional Parameter Specialisation
permalink: /uncondspec/
---

This example will show how to unconditionally specialise a particular function with respect to a parameter. In particular we'll use this simple example program:

```cpp
int f(int x) {
  return x * x;
}

int main(int argc, char** argv) {
  return f(1) + f(2);
}
```

We can replace `f` with a version that assumes x is always 2 by running:

```
clang test.c -c -emit-llvm -o test.bc
$LLPE_OPT -llpe test.bc -o spec.bc -llpe-root f -spec-param 0,2
```

As usual, the definition of `LLPE_OPT` is taken from the tutorial. That `spec-param` parameter sets argument 0 (here `int x`) to integer 2.

If we run llvm-dis on `spec.bc` we'll find the new and old `f` functions:

```
define i32 @f.old(i32 %x) #0 {
  %1 = alloca i32, align 4
  store i32 %x, i32* %1, align 4
  %2 = load i32, i32* %1, align 4
  %3 = load i32, i32* %1, align 4
  %4 = mul nsw i32 %2, %3
  ret i32 %4
}

define i32 @f(i32 %x) #0 {
entry:
  ret i32 4
}
```

Then if we compile and run the whole program:

```
clang spec.bc -o spec
./spec
```

We'll find it returns 8 instead of 5 as expected. This is because we have produced an unconditional specialisation -- the new `f` *always* assumes that its argument is 2, rather than checking that specialised code is appropriate at runtime. This sort of specialisation is thus only appropriate if we can externally guarantee that our specialisation assumption holds; otherwise you want conditional specialisation, which performs runtime assumption checking.

In addition to setting integer parameters, the `spec-param` parameter can also supply string constants and function pointers (e.g. `-spec-param 0,HelloWorld` or `-spec-param 0,f` if the type of the argument was `const char* x` or `int (*x)(int)` respectively.