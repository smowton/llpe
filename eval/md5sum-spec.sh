#!/bin/bash

~/integrator/scripts/integrate-prepared.sh md5sum-pre.bc -o md5sum-opt.bc --spec-env=3,../../md5_spec_env --spec-argv=1,2,../../md5_spec_argv --spec-param=0,main --spec-param=4,0 --spec-param=5,0 --intheuristics-root=__uClibc_main_spec --int-malloc-alignment=4 --int-ignore-loop=_charpad,4 --int-optimistic-loop=_vfprintf_internal,17,23.loopexit2 $@
