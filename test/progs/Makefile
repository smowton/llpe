
include Makefile.config

TARGETS = arrayloop deepnesting dependent_loops elim_if inline inline-nested inline-siblings \
	  nested_loops nonconstarrayloop partial_nested_loops pass-pointer-in nonconstglobal \
          invariants def-function def-skip-function defloop defskiploop loadundef memops \
	  small-write-large-load large-write-small-load nonconstmemcpy memcpy-cases \
	  memcpy-cases-nonconst struct-const struct-global reinterpret fp fpreinterpret \
	  fpalign read read-indirect-fd varargs varargs-param varargs-copy

LLVM_TARGETS = load-struct load-array switch-loop

LLVM_TARGETS_SOURCE = $(patsubst %,%.lls,$(LLVM_TARGETS))
LLVM_TARGETS_ASM = $(patsubst %,%.s,$(LLVM_TARGETS))
LLVM_TARGETS_OBJ = $(patsubst %,%.o,$(LLVM_TARGETS))

BC_TARGETS = $(patsubst %,%.bc,$(TARGETS))
LL_TARGETS = $(patsubst %,%.ll,$(TARGETS))

ALL_TARGETS = $(TARGETS) $(LLVM_TARGETS)

OPT_BC_TARGETS = $(patsubst %,%-opt.bc,$(ALL_TARGETS))
OPT_TARGETS = $(patsubst %,%-opt,$(ALL_TARGETS))

.PHONY: all clean

all: $(TARGETS) $(BC_TARGETS) $(LL_TARGETS) $(LLVM_TARGETS) $(OPT_BC_TARGETS) $(OPT_TARGETS)

% : %.c
	gcc -std=c99 $< -o $@

%.ltemp : %.c
	$(LLVM_GCC) -std=c99 $< -o $@

%.bc : %.ltemp
	opt -mem2reg -loopsimplify -lcssa $< -o $@

%.bc : %.lls
	llvm-as $< -o $@

%.ll : %.bc
	llvm-dis $<

% : %.o
	gcc $< -o $@

%.s : %.lls
	llc $< -o $@

%.s : %.bc
	llc $< -o $@

%.o : %.s
	as $< -o $@

%-opt.bc: %.bc
	opt -load $(PLUGINS_PATH)/IntegratorAnalyses.so -load $(PLUGINS_PATH)/IntegratorTransforms.so -loop-rotate -instcombine -jump-threading -loopsimplify -lcssa -integrator -integrator-accept-all -jump-threading $< -o $@

clean:
	-rm -f $(TARGETS)
	-rm -f $(LLVM_TARGETS)
	-rm -f $(BC_TARGETS)
	-rm -f $(LL_TARGETS)
	-rm -f $(OPT_BC_TARGETS)
	-rm -f $(OPT_TARGETS)
