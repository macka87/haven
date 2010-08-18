# Makefile: Example of Makefile usable in working directories
# Copyright (C) 2003 CESNET, Liberouter project
# Author: Rudolf Cejka <cejkar@fit.vutbr.cz>
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the OpenIPCore Hardware General Public
# License as published by the OpenIPCore Organization; either version
# 0.20-15092000 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# OpenIPCore Hardware General Public License for more details.
#
# You should have received a copy of the OpenIPCore Hardware Public
# License along with this program; if not, download it from
# OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
#
# $Id: Makefile 6011 2008-10-21 09:19:23Z korcek $
#

#variable BASE must be set to one folder bellow vhdl_design
BASE   = ../../../../..

PRECISIONBIN = .
ifeq ($(SYNTHESIS),precision)
	SYNTH ?= precision
	SYNTHFLAGS ?= -shell -file
	SYNTHFILES ?= Precision.tcl
else
	SYNTH ?= xst
	SYNTHFLAGS ?= -ifn
	SYNTHFILES ?= XST.xst
endif

#TOP vhd file with top level entity
TOP = ../mi32tobm.vhd

#UCF ucf file
FPGAUCF = $(BASE)/../combo6x/chips/fpga_u5.ucf

#SRC vhdl files with architecture 
SRC = ../mi32tobm.vhd

#when you don't want to use top level entity of fpga write this
NGDBUILDFLAGS = -aul

all: $(SRC:.vhd=.mcs)

include $(BASE)/../base/Makefile.fpga.inc
