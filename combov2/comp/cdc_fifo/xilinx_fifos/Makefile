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
	rm -f $(TARGET_NGCS)
