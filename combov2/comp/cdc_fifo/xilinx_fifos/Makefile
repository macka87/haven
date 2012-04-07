# Makefile: Makefile for Xilinx FIFOs
# Author(s): Ondrej Lengal <lengal@liberouter.org>
#
# $Id$

COREGEN=coregen

TARGET_NGCS=$(patsubst %.xco, %.ngc, $(wildcard */*.xco))
TARGET_VHDS=$(patsubst %.xco, %.vhd, $(wildcard */*.xco))

.PHONY: all clean distclean

all: $(TARGET_NGCS) $(TARGET_VHDS)

%.ngc: %.xco
	cp $< $<.bak
	cd $(dir $<) && \
		$(COREGEN) -b $(notdir $<)
	mv $<.bak $<
	cp $@ .

%.vhd: %.ngc
	cp $@ .

clean:
	rm -rf */tmp
	rm -rf */xlnx_auto_0_xdb
	rm -rf */*.pdf */*.cgc */*.cgp */*.log */*.tcl */*.xise */*.vho */*.gise */*.txt */*.asy

distclean: clean
	rm -f $(TARGET_NGCS)
	rm -f *.ngc
	rm -f *.vhd
