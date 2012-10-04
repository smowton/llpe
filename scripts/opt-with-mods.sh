#!/bin/bash

# Just run opt with my modules

opt -load /home/chris/integrator/llvm/Debug+Asserts/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm/Debug+Asserts/lib/IntegratorTransforms.so $@
