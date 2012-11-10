#!/bin/bash
opt -internalize -internalize-public-api-list=__uClibc_main -std-compile-opts date-opt.bc -o date-opt-int.bc
~/dragonegg-binutils/ld ../../../libs/libc/install-llvm/usr/lib/crtspec.o ../../../libs/libc/install-llvm/usr/lib/crti.o date-opt-int.bc ../../../libs/libc/install-llvm/usr/lib/libc.a ../../../libs/libc/install-llvm/usr/lib/crtn.o -o date-opt
