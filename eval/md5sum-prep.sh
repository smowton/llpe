#!/bin/bash

~/integrator/scripts/opt-with-mods.sh -define-exts -null-symbol __h_errno_location -null-symbol __pthread_initialize_minimal -null-symbol __preinit_array_start -null-symbol __preinit_array_end -null-symbol __init_array_start -null-symbol __init_array_end md5sum.bc -functionattrs -o md5sum-elim.bc
~/integrator/scripts/prepare-int.sh md5sum-elim.bc -o md5sum-pre.bc
