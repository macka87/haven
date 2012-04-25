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
# $Id$
#

# Export all variables to sub-makes
export

# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
# See https://www.liberouter.org/trac/netcope/wiki/Makefile for more info
# !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

# Makefile example:
# # Base directory
# FIRMWARE_BASE = ../..
# NETCOPE = $(FIRMWARE_BASE)/cards/combov2/netcope/eth-10G2
#
# #Translation parameters
# SYNTHESIS ?= xst
# MODS ?= 1
# FPGA_TYPE ?= xc5vlx155t-2
#
# DMA_MOD_NAME=dma_mod_2x64b_rxtx
# NETWORK_MOD_NAME=network_mod_10g2
#
# SRC=combov2_core.vhd
# 
# APP_MODULES=../../comp/debug/icon3.ngc
#
# all: modules
#	$(MAKE) -e mcs DISABLE_SYNTH=1
#
# include $(NETCOPE)/Makefile.netcope.inc

##############################################################################
# Basic translation parameters 
##############################################################################

# Synthesis tool: precision or XST (default)
SYNTHESIS ?= xst

# Synthesis from sources (0) or edif and sources (1) (default)
MODS ?= 1

# Set according to your card
FPGA_TYPE ?= xc5vlx155t-2

# Default synthetized modules types: precision or xst (default)
DMA_MOD_SYNTH ?= xst
NETWORK_MOD_SYNTH ?= xst
NETCOPE_ICS_SYNTH ?= xst
PCIE_MOD_SYNTH ?= xst
PCIE_CORE_WRAPPER_SYNTH ?= xst
TS_SYNTH ?= xst
MDIO_SYNTH ?= xst

##############################################################################
# Advanced translation parameters 
##############################################################################

# Create the design according to last build: 0(default) or 1 (experimental)
USEGUIDE ?= 0

# Project MUST set these names
#DMA_MOD_NAME=dma_mod_2x64b_rxtx
#NETWORK_MOD_NAME=network_mod_10g2
# Project may set these names
NETCOPE_ICS_NAME?=netcope_ics
PCIE_MOD_NAME?=cv2_pci
PCIE_CORE_WRAPPER_NAME?=ebp_wrapper
TS_NAME?=tsu_cv2
MDIO_NAME?=mdio_ctrl_top2_mi32

# Architecture + entity
SRC ?= combov2_core.vhd
TOP = $(FIRMWARE_BASE)/cards/combov2/chips/fpga_u0.vhd

# mcs dependencies
MCS_DEPENDS = $(APP_MCS_DEPENDS) $(SRC:.vhd=.mcs) $(SRC:.vhd=.map_guide.ncd) $(SRC:.vhd=.par_guide.ncd)

##############################################################################
# Non-changeable translation parameters 
##############################################################################
PRECISION_MODULE_EXT=edf
XST_MODULE_EXT=ngc

# Synthetized modules paths
DMA_MOD_PATH=$(FIRMWARE_BASE)/comp/proc/dma_mod/$(DMA_MOD_NAME)/synth
NETWORK_MOD_PATH=$(NETCOPE)/comp/network_mod/synth
NETCOPE_ICS_PATH=$(NETCOPE)/comp/netcope_ics/synth
PCIE_MOD_PATH=$(FIRMWARE_BASE)/cards/combov2/chips/comp/pci/synth
PCIE_CORE_WRAPPER_PATH=$(FIRMWARE_BASE)/cards/combov2/chips/comp/pci/ebp_wrapper/synth
TS_PATH=$(FIRMWARE_BASE)/comp/tsu/tsu_cv2/synth
MDIO_PATH=$(FIRMWARE_BASE)/comp/nic/xgmii/mdio/synth

# Synthetized modules full names
ifeq ($(DMA_MOD_SYNTH),precision)
   DMA_MOD_FNAME=$(DMA_MOD_NAME).$(PRECISION_MODULE_EXT)
else
   DMA_MOD_FNAME=$(DMA_MOD_NAME).$(XST_MODULE_EXT)
endif
ifeq ($(NETWORK_MOD_SYNTH),precision)
   NETWORK_MOD_FNAME=$(NETWORK_MOD_NAME).$(PRECISION_MODULE_EXT)
else
   NETWORK_MOD_FNAME=$(NETWORK_MOD_NAME).$(XST_MODULE_EXT)
endif
ifeq ($(NETCOPE_ICS_SYNTH),precision)
   NETCOPE_ICS_FNAME=$(NETCOPE_ICS_NAME).$(PRECISION_MODULE_EXT)
else
   NETCOPE_ICS_FNAME=$(NETCOPE_ICS_NAME).$(XST_MODULE_EXT)
endif
ifeq ($(PCIE_MOD_SYNTH),precision)
   PCIE_MOD_FNAME=$(PCIE_MOD_NAME).$(PRECISION_MODULE_EXT)
else
   PCIE_MOD_FNAME=$(PCIE_MOD_NAME).$(XST_MODULE_EXT)
endif
ifeq ($(PCIE_CORE_WRAPPER_SYNTH),precision)
   PCIE_CORE_WRAPPER_FNAME=$(PCIE_CORE_WRAPPER_NAME).$(PRECISION_MODULE_EXT)
else
   PCIE_CORE_WRAPPER_FNAME=$(PCIE_CORE_WRAPPER_NAME).$(XST_MODULE_EXT)
endif
ifeq ($(TS_SYNTH),precision)
   TS_FNAME=$(TS_NAME).$(PRECISION_MODULE_EXT)
else
   TS_FNAME=$(TS_NAME).$(XST_MODULE_EXT)
endif
ifeq ($(MDIO_SYNTH),precision)
   MDIO_FNAME=$(MDIO_NAME).$(PRECISION_MODULE_EXT)
else
   MDIO_FNAME=$(MDIO_NAME).$(XST_MODULE_EXT)
endif
   
TRN_ASYNC_PATH=$(FIRMWARE_BASE)/cards/combov2/chips/comp/pci/asfifo
TRN_ASYNC_RX=rx_asfifo_bram.ngc
TRN_ASYNC_TX=tx_asfifo_bram.ngc

# FPGA-specific xaui (because of rocketIO)
ifeq ($(FPGA_TYPE),xc5vfx100t)
	XAUI_FNAME=combov2_xaui_fxt.ngc
	XAUI_CORE_PATH=$(FIRMWARE_BASE)/comp/external/ip_cores/xaui_fxt
else
	XAUI_FNAME=combov2_xaui.ngc
	XAUI_CORE_PATH=$(FIRMWARE_BASE)/comp/external/ip_cores/xaui
endif
CV2_XAUI_PATH=$(NETCOPE)/comp/xaui/synth

# PCIE Endpoint core path (should be set in project Makefile!)
PCIE_CORE_PATH?=/home/data/sklep/ipcores/pcie_ebp/nic-10G2/combov2-lx155t/v1.9.4

ifeq ($(MODS),1)
   NETCOPE_MODULES=$(DMA_MOD_PATH)/$(DMA_MOD_FNAME) \
		$(NETWORK_MOD_PATH)/$(NETWORK_MOD_FNAME) \
		$(NETCOPE_ICS_PATH)/$(NETCOPE_ICS_FNAME) \
		$(PCIE_MOD_PATH)/$(PCIE_MOD_FNAME) \
		$(PCIE_CORE_WRAPPER_PATH)/$(PCIE_CORE_WRAPPER_FNAME) \
		$(TRN_ASYNC_PATH)/$(TRN_ASYNC_RX) \
		$(TRN_ASYNC_PATH)/$(TRN_ASYNC_TX) \
		$(TS_PATH)/$(TS_FNAME) \
		$(MDIO_PATH)/$(MDIO_FNAME) \
		$(CV2_XAUI_PATH)/$(XAUI_FNAME) 
else
   NETCOPE_MODULES=$(CV2_XAUI_PATH)/$(XAUI_FNAME) \
		$(TRN_ASYNC_PATH)/$(TRN_ASYNC_RX) \
		$(TRN_ASYNC_PATH)/$(TRN_ASYNC_TX) \
		$(PCIE_CORE_WRAPPER_PATH)/$(PCIE_CORE_WRAPPER_FNAME) 
endif

# Basic Netcope UCF
FPGAUCF = $(NETCOPE)/combov2.ucf

# Synthesis tool-specific UCF
ifeq ($(MODS),0)
   ifeq ($(SYNTHESIS),xst)  # Non-modular, XST
	   ADDUCF += $(NETCOPE)/combov2_xst.ucf
   else                 # Non-modular, Precision
	   ADDUCF += $(NETCOPE)/combov2_precision.ucf
   endif
else
   ifeq ($(PCIE_MOD_SYNTH),xst)  # Modular, cv2_pci in XST
	   ADDUCF += $(NETCOPE)/combov2_xst.ucf
   else                             # Modular, cv2_pci in Precision
	   ADDUCF += $(NETCOPE)/combov2_precision.ucf
   endif
endif

# Card-specific UCF
ifeq ($(FPGA_TYPE),xc5vlx110t)
   ADDUCF += $(NETCOPE)/combov2_lxt110.ucf
else 
   ifeq ($(FPGA_TYPE),xc5vlx155t)
      ADDUCF += $(NETCOPE)/combov2_lxt155.ucf
   else
   	ifeq ($(FPGA_TYPE),xc5vfx100t)
   	   ADDUCF += $(NETCOPE)/combov2_fxt100.ucf
   	else
   	        # Unsupported FPGA_TYPE type: $(FPGA_TYPE)
   	endif
   endif
endif

ifeq ($(USE_TIMESTAMP),YES)
	ADDUCF += $(NETCOPE)/combov2_tsu.ucf
endif

# Synthesis script will need this
export FPGA_TYPE $(FPGA_TYPE)
export MODS $(MODS)

ifeq ($(SYNTHESIS),xst)
	SYNTH = xst
	TOP_MODULE=$(SRC:.vhd=.ngc)
else
	SYNTH = precision
	SYNTHFLAGS = -shell -file
	SYNTHFILES = Precision.tcl
	TOP_MODULE=$(SRC:.vhd=.edf)
endif

#NGDBuild, MAP, PAR flags

NGDBUILDFLAGS = -aul $(APP_NGDBUILDFLAGS)
NGDBUILDFLAGS += -sd $(XAUI_CORE_PATH)
NGDBUILDFLAGS += $(shell $(NETCOPE)/gen_make.sh getsd $(NETCOPE)/Makefile.gen $(APP_MODULES) $(NETCOPE_MODULES))

NGDBUILD_DEPENDS = $(APP_NGDBUILD_DEPENDS)
NGDBUILD_DEPENDS += $(shell $(NETCOPE)/gen_make.sh getdep $(NETCOPE)/Makefile.gen $(APP_MODULES) $(NETCOPE_MODULES))

# No default optimization switches for map and par, every project sets it
# according to its best practices.
# For example, 10G NIC uses something like this:
# APP_MAPFLAGS = -xe n -global_opt speed -ol high -register_duplication on -logic_opt on
# APP_PARFLAGS = -xe n -ol high

ifeq ($(USEGUIDE),1)
	MAPFLAGS = -w $(APP_MAPFLAGS) -smartguide $(SRC:.vhd=.par_guide.ncd)
	PARFLAGS = -w $(APP_PARFLAGS) -smartguide $(SRC:.vhd=.par_guide.ncd)
else
	MAPFLAGS = -w $(APP_MAPFLAGS)
	PARFLAGS = -w $(APP_PARFLAGS)
endif

PROMGENFLAGS = -w -p mcs -u 0

# Simulation specification
SIMF ?= 
SIMT ?= 

%.map_guide.ncd: $(SRC:.vhd=.map.ncd)
	@cp $< $@
	
%.par_guide.ncd: $(SRC:.vhd=.par.ncd)
	@cp $< $@

.PHONY: mcs modules clean_mods clean_makegen $(NETCOPE)/Makefile.gen

mcs: $(MCS_DEPENDS)
	@echo "$(SRC:.vhd=.mcs) has been successfully built"
	@cat combov2_core.par.par | grep "All constraints were met."

MODULES=$(APP_MODULES) $(NETCOPE_MODULES) $(TOP_MODULE)

$(NETCOPE)/Makefile.gen :
	$(NETCOPE)/gen_make.sh gen $(NETCOPE)/Makefile.gen $(MODULES)

modules : $(NETCOPE)/Makefile.gen
	$(MAKE) -f $(NETCOPE)/Makefile.gen

CLEANALL_DEPENDS += clean_mods

clean_mods : $(NETCOPE)/Makefile.gen
	$(MAKE) -f $(NETCOPE)/Makefile.gen clean

CLEAN_DEPENDS += clean_makegen

clean_makegen:
	@rm -f $(NETCOPE)/Makefile.gen

# Translation specification
include $(FIRMWARE_BASE)/build/Makefile.fpga.inc

# How to re-run par:
# par -w -k -ol high combov2_core.par.ncd combov2_core.par.ncd combov2_core.pcf

