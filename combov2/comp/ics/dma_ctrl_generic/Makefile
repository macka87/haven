# Makefile: Makefile to compille Handel-C design
# Copyright (C) 2009 CESNET
# Author: Martin Spinler <xspinl00@stud.fit.vutbr.cz>
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
# $Id: Makefile 14853 2010-08-05 11:18:25Z xspinl00 $
#

# Handel-C files compilation

# Handel-C compilation flags
# Target FPGA family
#
SRC_RX=rx_dma_ctrl.hcc
OUT_RX=rx_dma_ctrl_arch

SRC_TX=tx_dma_ctrl.hcc
OUT_TX=tx_dma_ctrl_arch

DMA_CONST_FILE?=default_const.vhd
TEMP_CONST_FILE=.current_const_temp.vhd

# Target VHDL Sythetizer
DMA_SYNTH=XST
FAMILY=XilinxVirtex5       # Combo2

RX_IFC_COUNT=$(shell ./parse_constant.sh $(DMA_CONST_FILE) RX_IFC_COUNT)
TX_IFC_COUNT=$(shell ./parse_constant.sh $(DMA_CONST_FILE) TX_IFC_COUNT)
RX_BUFFER_SIZE=$(shell ./parse_constant.sh $(DMA_CONST_FILE) RX_BUFFER_SIZE)
TX_BUFFER_SIZE=$(shell ./parse_constant.sh $(DMA_CONST_FILE) TX_BUFFER_SIZE)
RX_BUFFER_ADDR=$(shell ./parse_constant.sh $(DMA_CONST_FILE) RX_BUFFER_ADDR)
TX_BUFFER_ADDR=$(shell ./parse_constant.sh $(DMA_CONST_FILE) TX_BUFFER_ADDR)

ifeq ($(RX_IFC_COUNT), 0)
DMAREQ_WIDTH=64
else
ifeq ($(TX_IFC_COUNT), 0)
DMAREQ_WIDTH=64
else
DMAREQ_WIDTH=32
endif
endif

DEFINE_RX=-DIFC_COUNT=$(RX_IFC_COUNT) -DDMAREQ_WIDTH=$(DMAREQ_WIDTH) -DBUFFER_ADDR=$(RX_BUFFER_ADDR) -DBUFFER_SIZE=$(RX_BUFFER_SIZE)
DEFINE_TX=-DIFC_COUNT=$(TX_IFC_COUNT) -DDMAREQ_WIDTH=$(DMAREQ_WIDTH) -DBUFFER_ADDR=$(TX_BUFFER_ADDR) -DBUFFER_SIZE=$(TX_BUFFER_SIZE)
HANDELC_FLAGS=-I /usr/share/mentor/pdk/hardware/include/ -xl /usr/share/mentor/pdk/hardware/lib/stdlib.hcl -vhdl -O -W -nohierarchy -hdlstyle $(DMA_SYNTH) -f $(FAMILY) -N+piperam -D__VHDL__ 

all: rx tx

check:
	$(shell (diff $(DMA_CONST_FILE) $(TEMP_CONST_FILE) > /dev/null 2>/dev/null || cp $(DMA_CONST_FILE) $(TEMP_CONST_FILE)))

rx: check $(OUT_RX).vhd
tx: check $(OUT_TX).vhd

$(OUT_RX).vhd: $(SRC_RX) $(TEMP_CONST_FILE)
	handelc $(HANDELC_FLAGS) $(DEFINE_RX) -o $(OUT_RX) $(SRC_RX)
	@rm -f $(OUT_RX)_info.xml $(OUT_RX).ucf
	@rm hcc* -f

$(OUT_TX).vhd: $(SRC_TX) $(TEMP_CONST_FILE)
	handelc $(HANDELC_FLAGS) $(DEFINE_TX) -o $(OUT_TX) $(SRC_TX)
	@rm -f $(OUT_TX)_info.xml $(OUT_TX).ucf
	@rm hcc* -f

clean:
	rm -f $(OUT_TX).vhd $(OUT_RX).vhd
