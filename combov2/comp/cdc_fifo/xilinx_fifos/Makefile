# Makefile: Makefile for Xilinx FIFOs
# Author(s): Ondrej Lengal <lengal@liberouter.org>
#
# $Id$

COREGEN=coregen

TARGET_NGCS=$(patsubst %.xco, %.ngc, $(wildcard */*.xco))

.PHONY: all

all: $(TARGET_NGCS)

%.ngc: %.xco
	cp $< $<.bak
	cd $(dir $<) && \
		$(COREGEN) -b $(notdir $<)
	mv $<.bak $<
	cp $@ .

clean:
	rm -rf */tmp
	rm -rf */xlnx_auto_0_xdb
	rm -rf */*.pdf */*.cgc */*.cgp */*.log */*.tcl */*.xise */*.vho */*.vhd */*.gise */*.txt */*.asy

distclean: clean
	rm -f $(TARGET_NGCS)
	rm -f *.ngc
