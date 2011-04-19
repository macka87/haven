# Makefile: Makefile for Xilinx FIFOs
# Author(s): Ondrej Lengal <lengal@liberouter.org>
#
# $Id$
#

XILINX_VERSION=xilinx123
COREGEN=coregen

all: $(patsubst %.xco, %.ngc, $(wildcard *.xco))

%.ngc: %.xco
	cp $< $<.bak
	. $(XILINX_VERSION)
	$(COREGEN) -b $<
	mv $<.bak $<

clean:
	rm -rf tmp/ _xmsgs/ xlnx_auto_0_xdb/
	rm -f *.ngc *.asy *.gise *.vhd *.vho *.xise *_flist.txt *_xmdf.tcl
	rm -f coregen.cgc coregen.cgp coregen.log
	rm -f fifo_generator_readme.txt fifo_generator_ug175.pdf
