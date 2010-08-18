# Makefile: Makefile to compille Handel-C design
# Copyright (C) 2008 CESNET
# Author: Martin Louda <sandin@liberouter.org>
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
# $Id: Makefile 13333 2010-03-24 14:57:26Z pus $
#

# Handel-C files compilation

# Handel-C compilation flags
# Target FPGA family
#FAMILY= XilinxVirtexIIPro   # Combo6X
FAMILY= XilinxVirtex5       # Combo2

# Target VHDL Sythetizer
#SYNTH= Precision
SYNTH= XST

SRC_TX_OPT= tx_dma_ctrl_opt.hcc
OUT_TX_OPT= tx_dma_ctrl_opt_arch
OUT_TX_OPT_TEMP= tx_dma_ctrl_opt_arch.vhd.temp

SRC_RX_OPT= rx_dma_ctrl_opt.hcc
OUT_RX_OPT= rx_dma_ctrl_opt_arch
OUT_RX_OPT_TEMP= rx_dma_ctrl_opt_arch.vhd.temp

RAM16_COMPONENT= ram16x1d_component.txt
RAMB16_S36_S36= ramb16_s36_s36_component.txt

HANDELC_FLAGS=-I /usr/share/mentor/pdk/hardware/include/ -xl /usr/share/mentor/pdk/hardware/lib/stdlib.hcl -vhdl -O -W -nohierarchy -hdlstyle $(SYNTH) -f $(FAMILY) -N+piperam -D__VHDL__

ARCH_DIR=arch

TX_PATH=$(ARCH_DIR)/$(OUT_TX_OPT)
RX_PATH=$(ARCH_DIR)/$(OUT_RX_OPT)

all: vhdl

tx_opt: $(SRC_TX_OPT)
	handelc -DDMA_DATA_WIDTH=$(DMA_DATA_WIDTH) $(HANDELC_FLAGS) -o $(OUT_TX_OPT) $(SRC_TX_OPT)
	rm -f $(OUT_TX_OPT)_info.xml $(OUT_TX_OPT).ucf
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(OUT_TX_OPT).vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(OUT_TX_OPT).vhd

rx_opt: $(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=$(DMA_DATA_WIDTH) $(HANDELC_FLAGS) -o $(OUT_RX_OPT) $(SRC_RX_OPT)
	rm -f $(OUT_RX_OPT)_info.xml $(OUT_RX_OPT).ucf
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(OUT_RX_OPT).vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(OUT_RX_OPT).vhd

vhdl: vhdl_rx vhdl_tx
	rm -f $(ARCH_DIR)/*.{ucf,xml}

vhdl_rx: vhdl_rx_1 vhdl_rx_2 vhdl_rx_4 vhdl_rx_8 vhdl_rx_16 vhdl_rx_32 vhdl_rx_64

vhdl_tx: vhdl_tx_1 vhdl_tx_2 vhdl_tx_4 vhdl_tx_8 vhdl_tx_16 vhdl_tx_32 vhdl_tx_64

vhdl_rx_1: 	$(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=1 $(HANDELC_FLAGS) -o $(RX_PATH)_1b $(SRC_RX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(RX_PATH)_1b.vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(RX_PATH)_1b.vhd

vhdl_rx_2: 	$(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=2 $(HANDELC_FLAGS) -o $(RX_PATH)_2b $(SRC_RX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(RX_PATH)_2b.vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(RX_PATH)_2b.vhd

vhdl_rx_4: 	$(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=4 $(HANDELC_FLAGS) -o $(RX_PATH)_4b $(SRC_RX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(RX_PATH)_4b.vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(RX_PATH)_4b.vhd

vhdl_rx_8: 	$(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=8 $(HANDELC_FLAGS) -o $(RX_PATH)_8b $(SRC_RX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(RX_PATH)_8b.vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(RX_PATH)_8b.vhd

vhdl_rx_16: $(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=16 $(HANDELC_FLAGS) -o $(RX_PATH)_16b $(SRC_RX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(RX_PATH)_16b.vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(RX_PATH)_16b.vhd

vhdl_rx_32: $(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=32 $(HANDELC_FLAGS) -o $(RX_PATH)_32b $(SRC_RX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(RX_PATH)_32b.vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(RX_PATH)_32b.vhd

vhdl_rx_64: $(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=64 $(HANDELC_FLAGS) -o $(RX_PATH)_64b $(SRC_RX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(RX_PATH)_64b.vhd > $(OUT_RX_OPT_TEMP)
	mv $(OUT_RX_OPT_TEMP) $(RX_PATH)_64b.vhd

vhdl_tx_1: 	$(SRC_RX_OPT)
	handelc -DDMA_DATA_WIDTH=1 $(HANDELC_FLAGS) -o $(TX_PATH)_1b $(SRC_TX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(TX_PATH)_1b.vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(TX_PATH)_1b.vhd

vhdl_tx_2: 	$(SRC_TX_OPT)
	handelc -DDMA_DATA_WIDTH=2 $(HANDELC_FLAGS) -o $(TX_PATH)_2b $(SRC_TX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(TX_PATH)_2b.vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(TX_PATH)_2b.vhd

vhdl_tx_4: 	$(SRC_TX_OPT)
	handelc -DDMA_DATA_WIDTH=4 $(HANDELC_FLAGS) -o $(TX_PATH)_4b $(SRC_TX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(TX_PATH)_4b.vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(TX_PATH)_4b.vhd

vhdl_tx_8: 	$(SRC_TX_OPT)
	handelc -DDMA_DATA_WIDTH=8 $(HANDELC_FLAGS) -o $(TX_PATH)_8b $(SRC_TX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(TX_PATH)_8b.vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(TX_PATH)_8b.vhd

vhdl_tx_16: $(SRC_TX_OPT)
	handelc -DDMA_DATA_WIDTH=16 $(HANDELC_FLAGS) -o $(TX_PATH)_16b $(SRC_TX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(TX_PATH)_16b.vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(TX_PATH)_16b.vhd

vhdl_tx_32: $(SRC_TX_OPT)
	handelc -DDMA_DATA_WIDTH=32 $(HANDELC_FLAGS) -o $(TX_PATH)_32b $(SRC_TX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(TX_PATH)_32b.vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(TX_PATH)_32b.vhd

vhdl_tx_64: $(SRC_TX_OPT)
	handelc -DDMA_DATA_WIDTH=64 $(HANDELC_FLAGS) -o $(TX_PATH)_64b $(SRC_TX_OPT)
	sed '/ARCHITECTURE/r $(RAM16_COMPONENT)' < $(TX_PATH)_64b.vhd > $(OUT_TX_OPT_TEMP)
	mv $(OUT_TX_OPT_TEMP) $(TX_PATH)_64b.vhd
