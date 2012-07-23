
include Makefile.config

TARGETS = arrayloop deepnesting dependent_loops elim_if inline inline-nested inline-siblings \
	  nested_loops nonconstarrayloop partial_nested_loops pass-pointer-in nonconstglobal \
          invariants def-function def-skip-function defloop defskiploop loadundef memops \
	  small-write-large-load large-write-small-load nonconstmemcpy memcpy-cases \
	  memcpy-cases-nonconst struct-const struct-global reinterpret

BC_TARGETS = $(patsubst %,%.bc,$(TARGETS))
LL_TARGETS = $(patsubst %,%.ll,$(TARGETS))

.PHONY: all clean

all: $(TARGETS) $(BC_TARGETS) $(LL_TARGETS)

% : %.c
	gcc -std=c99 $< -o $@

%.ltemp : %.c
	$(LLVM_GCC) -std=c99 $< -o $@

%.bc : %.ltemp
	opt -mem2reg -loopsimplify -lcssa $< -o $@

%.ll : %.bc
	llvm-dis $<

clean:
	-rm -f $(TARGETS)
	-rm -f $(BC_TARGETS)
	-rm -f $(LL_TARGETS)
