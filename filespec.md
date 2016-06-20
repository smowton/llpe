---
layout: page
title: Specialising with respect to file contents
permalink: /filespec/
---

In this example we'll specialise a program that reads a file so that it does the actual reading and consequent computation at specialisation time, and simply checks against possible modifications at runtime. We'll use conditional specialisation so that the program runs correctly when it deals with a different file than the one expected, too.

Here's our input program:

```cpp
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdlib.h>

int cksum_file(const char* fname) {

  int cksum = 0;
  char buf[1024];
  int r;
  int fd = open(fname, O_RDONLY);
  if(fd == -1)
    exit(1);

  while((r = read(fd, buf, sizeof(buf))) > 0) {

    for(int i = 0; i < r; ++i)
      cksum += buf[i];
      
  }

  return cksum;
  
}

int main(int argc, char** argv) {

  return cksum_file(argv[1]);

}
```

This program is a potential problem since it makes system calls (`open` et al) and calls libc functions (`exit`). Fortunately, LLPE natively understands (some of) the Linux VFS system calls, and the prototype for `exit` is annotated `noreturn`, so while we would need a bitcode-compiled libc if we were to use `stdio` instead of direct system calls, in this case it won't be necessary.

We need compile and then name the bitcode blocks, much as in the conditional specialisation example:

```
clang -c -emit-llvm filespec.c -o filespec.bc
opt -load /path/to/llpe/utils/libLLVMLLPEUtils.so -nameblocks filespec.bc -o filespec_names.bc
```

Let's make a test input file to consume:

```
yes | head -n 10000 > /tmp/test.in
```

Then we can specialise, giving a path condition that asserts we're checksumming that file:

```
$LLPE_OPT -llpe
	  -llpe-root cksum_file
	  -llpe-path-condition-str cksum_file,__args__,0,/tmp/test.in,cksum_file,1
	  -llpe-force-noalias-arg 0
	  -llpe-write-llio-conf /tmp/test.conf
	  -llpe-verbose-path-conditions
	  filespec_names.bc
	  -o filespec_test.bc
```

This is very similar to the invocation in the [conditional specialisation example](/conditionalspec/), except that it writes an `lliowd` configuration file that gives the name, modification time and hash of the file consumed during specialisation.

If we look at the disassembly (`llvm-dis filespec_test.bc -o -`) we'll see a call to `lliowd_init` at the start of `cksum_file` and calls to `lliowd_ok` at regular intervals -- these communicate with the `lliowd` daemon to check against concurrent file modification invalidating the results of specialisation.

We'll need to build against the LLIO client library which provides these functions:

```
clang filespec_test.bc $LLPE_ROOT/lliowd/clientlib.c -o filespec_test
```

We'll also need to amend the `lliowd` configuration written to `/tmp/test.conf`, adding the fully qualified path to the `filespec_test` binary at the beginning, producing a file like this:

```
/tmp/filespec_test
	/tmp/test.in 1466427977 854a94787dd96152db5e6b4c06822e7e9973e1a4
```

Let's try running the specialised program without the `lliowd` daemon running:

```
/tmp/filespec_test /etc/passwd
Entering specialised function cksum_file
Failed path condition String PC: "/tmp/test.in" -> i8* %fname in block 1 / 0
```

As expected the path condition fails, since we're not reading `/tmp/test.in`, and so unspecialised code is used.

```
/tmp/filespec_test /tmp/test.in
Entering specialised function cksum_file
Denied permission to use specialised files reading /tmp/test.in in 
```

This time the path condition passed, but the `lliowd` daemon couldn't be contacted, so again the specialised codepath wasn't used. Let's build and run it:

```
make -C $LLPE_ROOT/lliowd lliowd
$LLPE_ROOT/lliowd /tmp/test.conf &
Adding program /tmp/filespec_test
...

/tmp/filespec_test /tmp/test.in
Entering specialised function cksum_file
Successfully exiting specialised function cksum_file
```

Hurrah! We used the specialised path. But then if we modify the file:

```
echo "Hello world!" >> /tmp/test.in
/tmp/filespec_test /tmp/test.in
Entering specialised function cksum_file
Denied permission to use specialised files reading /tmp/test.in in 
```

The alteration was detected, and again we used the unspecialised path.