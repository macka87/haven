# Makefile: Makefile for LED demo design
# Copyright (C) 2005 CESNET, Liberouter project
# Author: Stepan Friedl <friedl@liberouter.org>
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
# $Id: Makefile 13798 2010-05-20 12:47:34Z xfried00 $
#

BASE = ../../../../..

ifeq ($(SYNTHESIS),xst)
	SYNTH ?= xst
	SYNTHFLAGS ?= -ifn
	SYNTHFILES ?= XST.xst
else
	SYNTH ?= precision
	SYNTHFLAGS ?= -shell -file
	SYNTHFILES ?= Precision.tcl
endif

TOP = $(BASE)/cards/combov2/chips/fpga_u16.vhd
SRC = sp3.vhd

#UCF ucf file
FPGAUCF = fpga_u16.ucf 

FPGAPART = 3s1200e
FPGAPROCESS = 4
FPGAPACKAGE = fg320
FPGAUCF = fpga_u16.ucf
#NGDBUILDFLAGS = -aul -bm test_top.bmm -sd cs -sd mb
NGDBUILDFLAGS = -aul -sd cs -sd mb

MAPFLAGS = -w -timing -ol high -register_duplication
PARFLAGS = -w -ol high
BITGENFLAGS = -w -g UnusedPin:PullNone -g DriveDone:Yes 
PROMGENFLAGS = -w -p mcs -c FF -bpi_dc parallel -d 3FFFFFF

SIMF =
SIMT =

all: $(SRC:.vhd=.mcs)

#data2mem -bm test_top_bd.bmm -bt sp3.bit -bd blink.elf tag microblaze_0  -o b sp3_mb.bit

include $(BASE)/build/Makefile.fpga.inc
