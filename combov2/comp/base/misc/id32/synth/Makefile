# makefile to synthesize component

MODULE=id_comp_mi32_norec

.PHONY: all doc xst precision clean

MAIN=Makefile.main

# Default: XST
xst: $(MODULE).ngc

precision: $(MODULE).edf

%.ngc: FORCE
	@echo $(MOD)
	$(MAKE) -f $(MAIN) $@ SYNTH=xst

%.edf: FORCE
	$(MAKE) -f $(MAIN) $@ SYNTH=precision SYNTHFLAGS="-shell -file" SYNTHFILES=Precision.tcl

FORCE:

clean:
	$(MAKE) -f $(MAIN) $@

doc:
	$(MAKE) -f $(MAIN) vhdocl
