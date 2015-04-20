---
layout: page
title: Conditional Specialisation
permalink: /conditionalspec/
---

This example will teach how to create a conditional specialisation: a specialised function that checks for a particular situation (e.g. particular argument values) and runs specialised code if the check passes.

Here is our input program:

```
int my_strlen(const char* s) {

    int ret = 0;
    
    while(*(s++))
        ++ret;
    
    return ret;

}

char cksum(const char* input) {

    char check = 0;
    for(int i = 0, ilim = my_strlen(input); i != ilim; ++i)
        check ^= input[i];
    return check;

}
```

<tt>cksum</tt> computes a simple bytewise XOR check value of an input string. We will create a specialised version of <tt>cksum</tt> for the particular input <tt>"Hello"</tt>. The specialised function will still work correctly when fed other input, using unspecialised code to handle this case.

We provide our own implementation of <tt>strlen</tt> here to avoid having to build the C standard library as LLVM IR, which we'll get to in a later tutorial.

We're going to need to refer to LLVM basic blocks in order to specify our specialisation. By default Clang doesn't name its basic blocks, so we should compile and assign names as follows:

```
clang -c -emit-llvm cksum.c -o cksum.bc
opt -load /path/to/llpe/utils/libLLVMLLPEUtils.so -nameblocks cksum.bc -o cksum_names.bc
```

Run llvm-dis and find the <tt>cksum</tt> entry block's name: in this example it has been named "1":

```
llvm-dis cksum_names.bc -o -

...
define i8 @cksum(i8* %input) {
"1":
  %0 = alloca i8*, align 8
...
```

If you see a name like <tt>&lt;label&gt;:4</tt> or no name at all, check you ran <tt>nameblocks</tt> successfully.

Now we can run the specialisation itself (using the same definition of $LLPE_OPT as in the [tutorial](/tutorial/)):

```
$LLPE_OPT -llpe-root cksum \
	  -llpe-force-noalias-arg 0 \
	  -llpe-path-condition-str cksum,__args__,0,Hello,cksum,1 \
	  -llpe-verbose-path-conditions \
	  cksum_names.bc \
	  -o cksum_spec.bc
```

* <tt>llpe-root</tt> picks the function where specialisation will begin (default <tt>main</tt>)
* <tt>llpe-force-noalias-arg 0</tt> specifies that the first parameter to <tt>cksum</tt> does not alias any other pointers (e.g. globals, other arguments).
* <tt>llpe-path-condition-str</tt> says that we should specialise assuming <tt>cksum</tt>'s first argument (<tt>__args__,0</tt>) holds the string <tt>Hello</tt> starting in function <tt>cksum</tt> block <tt>1</tt> (its entry block, the start of the function). Instead of <tt>__args__</tt> we could have named a basic block to make an assumption about an instruction, or <tt>__globals__</tt> to assume about a global variable. We could also have specified a different function and block for the last two arguments to indicate that the assumption, and thus specialisation based upon it, should not begin until the specified program point.
* <tt>llpe-verbose-path-conditions</tt> says to insert helpful print statements indicating when specialised code is entered and left and for what reason.

If we use <tt>llvm-dis</tt> to examine the specialised code, we will find it begins something like this:

```
entry1:
  %0 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([37 x i8]* @0, i32 0, i32 0))
  %1 = call i32 @strcmp(i8* getelementptr inbounds ([6 x i8]* @spec_env_str, i32 0, i32 0), i8* %input)
  %2 = icmp eq i32 %1, 0
  br i1 %2, label %3, label %6

; <label>:3                                       ; preds = %entry1
  %4 = call i8* @llvm.stacksave()
  call void @llvm.stackrestore(i8* %4)
  %5 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([49 x i8]* @2, i32 0, i32 0))
  ret i8 66
```

Aside from the <tt>printf</tt> calls that provide debugging information because we used the <tt>verbose-path-conditions</tt> option, we see a <tt>strcmp</tt> call to verify our specialisation assumption (that the argument <tt>input</tt> points to the string <tt>Hello</tt>). The specialised path starting at <tt>%3</tt> returns the checksum <tt>66</tt> right away, whilst starting at <tt>%6</tt> we will find a complete unspecialised version of <tt>cksum</tt> ready to handle any other input.

If we write a <tt>main.c</tt> that calls <tt>cksum</tt> with a few different values, then link and run, we will see debugging output telling us when specialised code was used. Here my <tt>main</tt> function called <tt>cksum</tt> with <tt>"Hello"</tt> and then <tt>"World"</tt>:

```
clang cksum_spec.bc main.c -o cksum_test
./cksum_test

Entering specialised function cksum
Successfully exiting specialised function cksum
Entering specialised function cksum
Failed path condition String PC: "Hello" -> i8* %input in block 1 / 0
...
```

