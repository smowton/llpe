#!/bin/bash
~/integrator/scripts/integrate-prepared.sh xml-pre.bc -o xml-opt.bc --spec-env=3,xml_spec_env --spec-argv=1,2,xml_spec_argv --spec-param=0,main --spec-param=4,0 --spec-param=5,0 --intheuristics-root=__uClibc_main_spec --int-assume-edge=xmlFreeDoc,36,36.37_crit_edge --int-assume-edge=xmlFreeDoc,36,38.thread --int-always-explore=__xmlRaiseError
