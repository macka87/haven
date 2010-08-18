# Makefile: Example of Makefile usable in working directories
# Copyright (C) 2003 CESNET, Liberouter project
# Author: Rudolf Cejka <cejkar@fit.vutbr.cz>
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in
#    the documentation and/or other materials provided with the
#    distribution.
# 3. Neither the name of the Company nor the names of its contributors
#    may be used to endorse or promote products derived from this
#    software without specific prior written permission.
#
# This software is provided ``as is'', and any express or implied
# warranties, including, but not limited to, the implied warranties of
# merchantability and fitness for a particular purpose are disclaimed.
# In no event shall the company or contributors be liable for any
# direct, indirect, incidental, special, exemplary, or consequential
# damages (including, but not limited to, procurement of substitute
# goods or services; loss of use, data, or profits; or business
# interruption) however caused and on any theory of liability, whether
# in contract, strict liability, or tort (including negligence or
# otherwise) arising in any way out of the use of this software, even
# if advised of the possibility of such damage.
#
# $Id: Makefile 14 2007-07-31 06:44:05Z kosek $
#

#variable BASE must be set to one folder bellow vhdl_design
BASE   = ../../..
#SYNTHESIS = precision

PRECISIONBIN = .
ifeq ($(SYNTHESIS),precision)
	SYNTH ?= precision
	SYNTHFLAGS ?= -shell -file
	SYNTHFILES ?= Precision.tcl
    ADDUCF = ./fpga_precision.ucf
else
	SYNTH ?= xst
	SYNTHFLAGS ?= -ifn 
	SYNTHFILES ?= XST.xst
    ADDUCF = ./fpga_xst.ucf
endif

#TOP vhd file with top level entity
#TOP = $(BASE)/../combo6x/chips/fpga_u5.vhd
TOP = fpga_u5.vhd

#UCF ucf file
#FPGAUCF = $(BASE)/../combo6x/chips/fpga_u5.ucf
FPGAUCF = fpga_u5.ucf

#SRC vhdl files with architecture 
SRC = combo6x.vhd

#when you don't want to use top level entity of fpga write this
NGDBUILDFLAGS = -aul 

# Set PAR high effort 
#MAPFLAGS = -timing -ol high
#PARFLAGS = -w -ol high

all: $(SRC:.vhd=.mcs)

include $(BASE)/../base/Makefile.fpga.inc
