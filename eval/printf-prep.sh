#!/bin/bash

~/integrator/scripts/opt-with-mods.sh -define-exts -null-symbol __h_errno_location -null-symbol __pthread_initialize_minimal -null-symbol __preinit_array_start -null-symbol __preinit_array_end -null-symbol __init_array_start -null-symbol __init_array_end printf.bc -o printf-elim.bc
~/integrator/scripts/prepare-int.sh printf-elim.bc -o printf-pre.bc
