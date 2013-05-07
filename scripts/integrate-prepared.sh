#!/bin/bash

opt -load /home/chris/integrator/llvm-3.2.src/Release+Debug/lib/IntegratorAnalyses.so -load /home/chris/integrator/llvm-3.2.src/Release+Debug/lib/IntegratorTransforms.so -integrator -jump-threading "$@"
