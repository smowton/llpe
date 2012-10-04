#!/bin/bash

~/integrator/scripts/opt-with-mods.sh -define-exts -null-symbol __h_errno_location date.bc -o date-elim.bc
~/integrator/scripts/prepare-int.sh date-elim.bc -o date-pre.bc
