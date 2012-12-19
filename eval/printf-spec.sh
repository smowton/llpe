#!/bin/bash

~/integrator/scripts/integrate-prepared.sh printf-pre.bc -o printf-opt.bc --spec-env=3,../../spec_env --spec-argv=1,2,../../printf_spec_argv --spec-param=0,main --spec-param=4,0 --spec-param=5,0 --intheuristics-root=__uClibc_main_spec --int-optimistic-loop=_vfprintf_internal,17,23.loopexit2 --int-optimistic-loop=vasnprintf,50,627 --int-ignore-loop=_charpad,4 --int-loop-max=vasnprintf,484,0 --int-loop-max=vasnprintf,484.outer,0 --int-ignore-loop=_stdlib_strto_l_l,16.outer $@
