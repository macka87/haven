# modules.tcl: modules for TSU simulation
# Copyright (C) 2005 CESNET
# Author(s): Jan Pazdera <pazdera@liberouter.org>
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

# Base directories
set VHDL_BASE        "../../../.."
set UNIT_BASE        "$VHDL_BASE/units"
set SCAMPI_BASE      "$VHDL_BASE/projects/scampi_ph2"
set COMMON_BASE      "$VHDL_BASE/units/common"
set MODELS_BASE      "$VHDL_BASE/models"
set TSUADD_BASE      "$UNIT_BASE/tsu"

#Packages

#PLX model
set MOD "$MODELS_BASE/plx_9054/plx_oper.vhd"
set MOD "$MOD $MODELS_BASE/plx_9054/plx_sim.vhd"

#Common components
set MOD "$MOD $COMMON_BASE/asrq2sync/asrq2sync.vhd"
set MOD "$MOD $COMMON_BASE/ad2sd/ad2sd.vhd"

#CLK_GEN component
set MOD "$MOD $SCAMPI_BASE/comp/clk_gen/clk2x.vhd"
set MOD "$MOD $SCAMPI_BASE/comp/clk_gen/clk4x.vhd"
set MOD "$MOD $SCAMPI_BASE/comp/clk_gen/clk_gen.vhd"

#Local bus
set MOD "$MOD $UNIT_BASE/lb/lbconn_mem.vhd"
set MOD "$MOD $UNIT_BASE/lb/lbconn_mem.vhd"
set MOD "$MOD $UNIT_BASE/lb/local_bus.vhd"

#-----------------------------------------
#TSU_ADD
set MOD "$MOD $TSUADD_BASE/tsu_add_fsm.vhd"
set MOD "$MOD $TSUADD_BASE/tsu_add.vhd"

#-----------------------------------------
# Top level
set MOD "$MOD $VHDL_BASE/combo6/chips/fpga.vhd"
set MOD "$MOD $TSUADD_BASE/tsu2pci/tsu2pci.vhd"

