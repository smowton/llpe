
include Makefile.config

TARGETS = arrayloop deepnesting dependent_loops elim_if inline inline-nested inline-siblings \
	  nested_loops nonconstarrayloop partial_nested_loops pass-pointer-in

BC_TARGETS = $(patsubst %,%.bc,$(TARGETS))

.PHONY: all clean

all: $(TARGETS) $(BC_TARGETS)

% : %.c
	gcc -std=c99 $< -o $@

%.ll : %.c
	$(LLVM_GCC) -std=c99 $< -o $@

%.bc : %.ll
	opt -mem2reg -loopsimplify -lcssa $< -o $@

clean:
	-rm -f $(TARGETS)
	-rm -f $(BC_TARGETS)
	-rm -f $(patsubst %, %.ll, $(TARGETS))
