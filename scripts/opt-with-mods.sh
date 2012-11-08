#!/bin/bash

# Just run opt with my modules

opt -load /home/chris/integrator/llvm/Release/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm/Release/lib/IntegratorTransforms.so $@
