#!/bin/bash

~/integrator/scripts/opt-with-mods.sh -define-exts -null-symbol __h_errno_location date.bc -null-symbol __pthread_initialize_minimal -null-symbol __preinit_array_start -null-symbol __preinit_array_end -null-symbol __init_array_start -null-symbol __init_array_end -o date-elim.bc
~/integrator/scripts/prepare-int.sh date-elim.bc -o date-pre.bc
