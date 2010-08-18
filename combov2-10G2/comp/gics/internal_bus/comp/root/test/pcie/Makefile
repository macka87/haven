# 
# Makefile:
# Copyright (C) 2009 CESNET
# Author(s): Pavol Korcek <korcek@liberouter.org>
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
# $Id: Makefile 11949 2009-11-10 14:25:42Z xvozen00 $

# FIRMWARE base directory
BASE=../../../../../../..

#SYNTHESIS=precision

export FPGA_TYPE=xc5vlx50t

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
TOP = ml555.vhd

#UCF ucf file
FPGAUCF = $(BASE)/cards/ml555/chips/ml555.ucf
ADDUCF += ml555.ucf 

XILINX_PCIE_CORE=/home/data/sklep/ipcores/pcie_ebp/test/ml555-lx50t/v1.11.0

#SRC vhdl files with architecture 
SRC = ml555_arch.vhd

#when you don't want to use top level entity of fpga write this
NGDBUILDFLAGS = -aul -sd $(XILINX_PCIE_CORE)

#MAPFLAGS = -w -ol high -detail -smartguide combov2_core.map_guide.ncd
#PARFLAGS = -w -ol high -smartguide combov2_core.par_guide.ncd

MAPFLAGS = -ol high
#MAPFLAGS = -ol high -xe n -global_opt speed -logic_opt on -register_duplication on -w 
PARFLAGS = -ol high
#PARFLAGS = -ol high -xe n 

PROMGENFLAGS = -w -p mcs -u 0 

MCS_DEPENDS = $(SRC:.vhd=.mcs)


all: $(MCS_DEPENDS) 

mcs: $(MCS_DEPENDS)
	@echo "$(SRC:.vhd=.mcs) has been successfully built"
	@cat ml555_arch.par.par | grep "All constraints were met."

include $(BASE)/build/Makefile.fpga.inc
