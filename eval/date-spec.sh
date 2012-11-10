#!/bin/bash

~/integrator/scripts/integrate-prepared.sh date-pre.bc -o date-opt.bc --spec-env=3,../../spec_env --spec-argv=1,2,../../spec_argv --spec-param=0,main --spec-param=4,0 --spec-param=5,0 --int-optimistic-loop=strftime_case_,328,330 --int-assume-edge=strftime_case_,96,65 --intheuristics-root=__uClibc_main_spec $@
