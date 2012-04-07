# Makefile: Makefile to compile ComboV2 design
# Copyright (C) 2007 CESNET
# Author: Viktor Pus <pus@liberouter.org>
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
# $Id: Makefile 14956 2010-08-10 08:20:32Z xspinl00 $
#

# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
# See https://www.liberouter.org/trac/netcope/wiki/Makefile for more info
# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

##############################################################################
# NIC specific parameters
##############################################################################

# Use Chipscope : YES or NO
# Make your choice in ../../pkg/combov2_core_const.vhd (GENERATE_CHIPSCOPE)

# Use timestamp unit : YES or NO
# Synchronize your choice with ../../pkg/combov2_user_const.vhd (TIMESTAMP_UNIT)
USE_TIMESTAMP=NO

# Path to user modules
CHIPSCOPE_PATH=$(FIRMWARE_BASE)/comp/debug
FL_TRANSFORMER_PATH=$(FIRMWARE_BASE)/comp/fl_tools/flow/transformer/synth
FL_WATCH_PATH=$(FIRMWARE_BASE)/comp/fl_tools/debug/watch/synth
IB_EP_PATH=$(FIRMWARE_BASE)/comp/gics/internal_bus/comp/endpoint/synth
IB_SWITCH_PATH=$(FIRMWARE_BASE)/comp/gics/internal_bus/comp/switch/synth
IB_ASYNC_PATH=$(FIRMWARE_BASE)/comp/ics/internal_bus/comp/ib_async/synth
TSU_ASYNC_PATH=$(FIRMWARE_BASE)/comp/tsu/tsu_async/synth

# User modules names
CHIPSCOPE_ICON=icon3.ngc
CHIPSCOPE_ILA72=ila72.ngc
CHIPSCOPE_ILA73=ila73.ngc
CHIPSCOPE_ILA144=ila144.ngc
FL_TRANSFORMER_128TO64=fl_transformer_128to64.ngc
FL_TRANSFORMER_64TO128=fl_transformer_64to128.ngc
FL_WATCH_2=fl_watch_2.ngc
FL_WATCH_2_HDR=fl_watch_2_hdr.ngc
IB_EP=ib_endpoint_synth.ngc
IB_SWITCH=ib_switch_slave_synth.ngc
IB_ASYNC=ib_asfifo_64b.ngc
TSU_ASYNC=tsu_async.ngc

FIFO_PATH=$(FIRMWARE_BASE)/comp/cdc_fifo/xilinx_fifos
FIFO_NGCS=$(FIFO_PATH)/asfifo_lut_1.ngc \
          $(FIFO_PATH)/asfifo_lut_8.ngc \
          $(FIFO_PATH)/asfifo_lut_9.ngc \
          $(FIFO_PATH)/asfifo_lut_71.ngc \
          $(FIFO_PATH)/asfifo_lut_136.ngc


##############################################################################
# Translation parameters 
##############################################################################

# Synthesis tool: precision or XST
SYNTHESIS = xst

# Synthesis from sources (0) or edif and sources (1)
MODS = 1

# Set according to your card
#FPGA_TYPE = xc5vlx155t
FPGA_TYPE = xc5vlx155t-2
#FPGA_TYPE = xc5vlx110t
#FPGA_TYPE = xc5vlx110t-2
#FPGA_TYPE = xc5vfx100t

# Synthetized modules types: xst or precision
DMA_MOD_SYNTH = xst
NETWORK_MOD_SYNTH = xst
NETCOPE_ICS_SYNTH = xst
PCIE_MOD_SYNTH = xst
PCIE_CORE_WRAPPER_SYNTH = xst
TS_SYNTH = xst
MDIO_SYNTH = xst

##############################################################################
# Advanced translation parameters 
##############################################################################

# Base directory
FIRMWARE_BASE = ../..
NETCOPE = $(FIRMWARE_BASE)/cards/combov2/netcope/eth-10G2

USEGUIDE = 0

APPLICATION=RXTX_1
#APPLICATION=RXTX_2_GEN
#APPLICATION=RXTX_2_PAC

# for sze left blank
DMA_TYPE=
# Synthetized modules names
ifeq ($(APPLICATION),RXTX_1)
   DMA_MOD_NAME=dma_mod_1x64b_rxtx
endif
ifeq ($(APPLICATION),RXTX_1_GEN)
   DMA_MOD_NAME=dma_mod_1x64b_rxtx_gen
endif
ifeq ($(APPLICATION),RXTX_2)
   DMA_MOD_NAME=dma_mod_2x64b_rxtx
endif
ifeq ($(APPLICATION),RXTX_2_GEN)
   DMA_MOD_NAME=dma_mod_2x64b_rxtx_gen
endif
ifeq ($(APPLICATION),RXTX_2_PAC)
   DMA_MOD_NAME=dma_mod_2x64b_rxtx_pac
   DMA_TYPE="-pac"
endif

NETWORK_MOD_NAME=network_mod_10g2_64

export APPLICATION $(APPLICATION)

PCIE_CORE_BASE=$(FIRMWARE_BASE)/comp/external/ip_cores/pcie

# PCIE Endpoint: card identification and endpoint version
ifeq ($(FPGA_TYPE),xc5vlx155t-2)
   PCIE_CORE_PATH=$(PCIE_CORE_BASE)/combov2-lx155t/v1.14.1_250
endif

# Exporting for use in wrapper Modules.tcl 
export PCIE_CORE_PATH $(PCIE_CORE_PATH)

# Architecture
SRC = combov2_core.vhd

APP_MCS_DEPENDS = 

APP_MODULES=$(CHIPSCOPE_PATH)/$(CHIPSCOPE_ICON) \
	$(CHIPSCOPE_PATH)/$(CHIPSCOPE_ILA72) \
	$(CHIPSCOPE_PATH)/$(CHIPSCOPE_ILA73) \
	$(CHIPSCOPE_PATH)/$(CHIPSCOPE_ILA144) \
	$(FIFO_NGCS) \


ifeq ($(MODS),1)
	APP_MODULES += \
		$(IB_EP_PATH)/$(IB_EP) \
		$(IB_SWITCH_PATH)/$(IB_SWITCH) \
		$(IB_ASYNC_PATH)/$(IB_ASYNC) \
		$(TSU_ASYNC_PATH)/$(TSU_ASYNC)
endif

APP_MODULES += $(FL_TRANSFORMER_PATH)/$(FL_TRANSFORMER_128TO64) \
		$(FL_TRANSFORMER_PATH)/$(FL_TRANSFORMER_64TO128) \
		$(FL_WATCH_PATH)/$(FL_WATCH_2) \
		$(FL_WATCH_PATH)/$(FL_WATCH_2_HDR) \


# Application specific flags
APP_MAPFLAGS = -xe n -ol high -register_duplication on
APP_PARFLAGS = -xe n -ol high

ADDUCF = nic.ucf

##############################################################################
# NIC specific Makefile
##############################################################################

# Main target
all: modules
	export XIL_MAP_ALWAYS_RETARGET_FDDR=1 && $(MAKE) mcs DISABLE_SYNTH=1 

# NetCOPE Makefile specification
include $(NETCOPE)/Makefile.netcope.inc

