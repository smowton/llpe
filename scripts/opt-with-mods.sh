#!/bin/bash

# Just run opt with my modules

/usr/bin/opt -load /home/chris/integrator/llvm/Release+Debug/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm/Release+Debug/lib/IntegratorTransforms.so $@
