
include Makefile.config

TARGETS = read

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
