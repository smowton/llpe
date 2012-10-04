#!/bin/bash

~/integrator/scripts/integrate-prepared.sh date-pre.bc -o date-opt.bc --spec-env=3,../../spec_env --spec-param=0,main --spec-param=4,0 --spec-param=5,0 --intheuristics-root=__uClibc_main_spec $@
