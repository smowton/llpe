#!/bin/bash

/usr/bin/llvm-gcc-uclibc -std=gnu99   -g -O2 -Wl,--as-needed  -o date date.o libver.a ../lib/libcoreutils.a  ../lib/libcoreutils.a -Wl,--plugin-opt,also-emit-llvm,-u,__uClibc_main_spec
