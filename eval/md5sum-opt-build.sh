#!/bin/bash
opt -internalize -internalize-public-api-list=__uClibc_main -std-compile-opts md5sum-opt.bc -o md5sum-opt-int.bc
~/dragonegg-binutils/ld ../../../libs/libc/install-llvm/usr/lib/crtspec.o ../../../libs/libc/install-llvm/usr/lib/crti.o md5sum-opt-int.bc ../../../libs/libc/install-llvm/usr/lib/libc.a ../../../libs/libc/install-llvm/usr/lib/crtn.o -o md5sum-opt
