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
# $Id: Makefile 13490 2010-04-11 15:32:18Z korcek $

# FIRMWARE base directory
BASE=../../../../../../..
TRN_ASYNC_PATH=$(BASE)/cards/combov2/chips/comp/pci/asfifo
EBP_WRAPPER_PATH=$(BASE)/cards/combov2/chips/comp/pci/ebp_wrapper/synth
CHIPSCOPE_PATH=/home/current/korcek/combov2_speedup/chipscope

#USE_CHIPSCOPE=YES
#SYNTHESIS=precision

#export FPGA_TYPE=xc5vlx110t
export FPGA_TYPE=xc5vlx155t-2
#export FPGA_TYPE=xc5vfx100t

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
TOP = fpga_u0.vhd

#UCF ucf file
FPGAUCF = combov2_u0.ucf
ADDUCF += combov2.ucf 

# FPGA type specific UCF file & PCIe core
ifeq ($(FPGA_TYPE),xc5vlx110t)
   ADDUCF += xc5vlx110t.ucf 
   PCIE_CORE_PATH=/home/data/sklep/ipcores/pcie_ebp/test/combov2-lx110t/v1.13.0_250
endif
ifeq ($(FPGA_TYPE),xc5vlx155t-2)
   ADDUCF += xc5vlx155t.ucf 
   PCIE_CORE_PATH=/home/data/sklep/ipcores/pcie_ebp/test/combov2-lx155t/v1.13.0_250
endif
ifeq ($(FPGA_TYPE),xc5vfx100t)
   ADDUCF += xc5vfx100t.ucf 
   PCIE_CORE_PATH=/home/data/sklep/ipcores/pcie_ebp/test/combov2-fx100t/v1.13.0_250
endif

# Exporting for use in wrapper Modules.tcl 
export PCIE_CORE_PATH $(PCIE_CORE_PATH)

SRC = combov2_arch.vhd

ifeq ($(USE_CHIPSCOPE), YES)
	NGDBUILDFLAGS = -aul -sd $(EBP_WRAPPER_PATH) -sd $(TRN_ASYNC_PATH) -sd $(CHIPSCOPE_PATH)
else
	NGDBUILDFLAGS = -aul -sd $(EBP_WRAPPER_PATH) -sd $(TRN_ASYNC_PATH)
endif

#MAPFLAGS = -ol high
MAPFLAGS = -ol high -xe n -global_opt speed -logic_opt on -register_duplication on -w 
#PARFLAGS = -ol high
PARFLAGS = -ol high -xe n 


PROMGENFLAGS = -w -p mcs -u 0 

MCS_DEPENDS = trn_async ebp_wrapper $(SRC:.vhd=.mcs)


all: $(MCS_DEPENDS) 

mcs: $(MCS_DEPENDS)
	@echo "$(SRC:.vhd=.mcs) has been successfully built"
	@cat combov2_arch.par.par | grep "All constraints were met."

# Xilinx asfifos - generate with coregen
trn_async: $(TRN_ASYNC_PATH)/rx_asfifo_bram.ngc $(TRN_ASYNC_PATH)/tx_asfifo_bram.ngc

$(TRN_ASYNC_PATH)/rx_asfifo_bram.ngc $(TRN_ASYNC_PATH)/tx_asfifo_bram.ngc:
	cd $(TRN_ASYNC_PATH) ; make

# Xilinx endpoint block plus core
ebp_wrapper: $(EBP_WRAPPER_PATH)/ebp_wrapper.ngc

$(EBP_WRAPPER_PATH)/ebp_wrapper.ngc:
	cd $(EBP_WRAPPER_PATH) ; make


include $(BASE)/build/Makefile.fpga.inc
