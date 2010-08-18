# Modules.tcl: Network Module local include script
# Copyright (C) 2008 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
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

# Set paths
set COMP_BASE        "$ENTITY_BASE/../../../../../../comp"
set PROJECT_PKG_BASE "$ENTITY_BASE/../../../../../../pkg"
set IBUF_BASE        "$COMP_BASE/nic/xgmii/ibuf"
set OBUF_BASE        "$COMP_BASE/nic/xgmii/obuf"
set GLITCHF_BASE     "$COMP_BASE/base/shreg/glitch_filter"
set LED_CTRL_BASE    "$COMP_BASE/nic/led_ctrl"
set MI_SPLITTER_BASE "$COMP_BASE/gics/internal_bus/comp/base/mi_splitter"

set FIFO_PKG      "$COMP_BASE/base/fifo/fifo_layers/pkg"

# Packages
set PACKAGES      "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
set PACKAGES      "$PACKAGES $COMP_BASE/fl_tools/pkg/fl_pkg.vhd"
set PACKAGES      "$PACKAGES $FIFO_PKG/fifo_pkg.vhd"
set PACKAGES      "$PACKAGES $COMP_BASE/nic/pkg/ibuf_general_pkg.vhd"
set PACKAGES      "$PACKAGES $ENTITY_BASE/network_10g2_const.vhd"
set PACKAGES      "$PACKAGES $ENTITY_BASE/network_10g2_64_const.vhd"
set PACKAGES      "$PACKAGES $ENTITY_BASE/network_10g2_rx_const.vhd"
set PACKAGES      "$PACKAGES $PROJECT_PKG_BASE/combov2_user_const.vhd"

# Local include
set MOD "$MOD $ENTITY_BASE/network_10g2_ent.vhd"
set MOD "$MOD $ENTITY_BASE/network_10g2.vhd"
set MOD "$MOD $ENTITY_BASE/network_10g2_rx_ent.vhd"
set MOD "$MOD $ENTITY_BASE/network_10g2_rx.vhd"
set MOD "$MOD $ENTITY_BASE/network_10g2_64_ent.vhd"
set MOD "$MOD $ENTITY_BASE/network_10g2_64.vhd"

set DMA_IFC_COUNT 4

# instantiations
set IBUF_INST        [list [list "IBUF_I"             "FULL"]]
set OBUF_INST        [list [list "OBUF_I"             "FULL"]]
set LED_CTRL_INST    [list [list "LED_CTRL"           "FULL"]]
set MI_SPLITTER_INST [list [list "MI_SPLITTER_I"      "FULL"]]

# Components
set COMPONENTS [list \
   [ list "PKG_MATH"      $COMP_BASE/base/pkg "MATH"] \
   [ list "IBUF"          $IBUF_BASE        "CRC_INCLUDE" $IBUF_INST ] \
   [ list "OBUF"          $OBUF_BASE        "FULL"        $OBUF_INST ] \
   [ list "GLITCH_FILTER" $GLITCHF_BASE     "FULL" ] \
   [ list "LED_CTRL"      $LED_CTRL_BASE    "FULL"        $LED_CTRL_INST ] \
   [ list "MI_SPLITTER"   $MI_SPLITTER_BASE "FULL"        $MI_SPLITTER_INST ] \
]
