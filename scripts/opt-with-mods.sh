#!/bin/bash

# Just run opt with my modules

/usr/bin/opt -load /home/chris/integrator/release_32/Release+Debug/lib/LLVMDataStructure.so -load /home/chris/integrator/llvm-3.2.src/Release+Debug/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm-3.2.src/Release+Debug/lib/IntegratorTransforms.so $@
