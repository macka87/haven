# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
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

# Paths
set COMP_BASE     "$ENTITY_BASE/../../.."
set FL_BASE       "$COMP_BASE/fl_tools"
set TX_BASE       "$ENTITY_BASE/../sw_txbuf"
set RX_BASE       "$ENTITY_BASE/../sw_rxbuf"
set ICS_BASE      "$COMP_BASE/ics"
set GICS_BASE     "$COMP_BASE/gics"
set IBEP_BASE     "$COMP_BASE/gics/internal_bus/comp/endpoint"
set BM_CONVERTER_BASE "$COMP_BASE/gics/misc/bm_converter"
set TAG_SEQ_BASE "$COMP_BASE/ics/internal_bus/comp/ib_endpoint/tag_sequencer"
set DEC1FN_BASE   "$COMP_BASE/base/logic/dec1fn"
set SPLITTER_BASE "$FL_BASE/flow/splitter"

set PACKAGES  "$PACKAGES $GICS_BASE/internal_bus/pkg/ib_ifc_pkg.vhd"
set PACKAGES  "$PACKAGES $FL_BASE/pkg/fl_pkg.vhd" 

set MOD       "$MOD $ENTITY_BASE/sw_1rx_4tx_buf.vhd"
set MOD       "$MOD $ENTITY_BASE/sw_1rx_4tx_buf_nocb.vhd"

# Full version including all top levels for SW_RXBUF
if { $ARCHGRP == "FULL" } {

   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg  "MATH"] \
      [ list "SW_RXBUF"       $RX_BASE             "BOTH"] \
      [ list "SW_TXBUF"       $TX_BASE             "BOTH"] \
   ]

} elseif { $ARCHGRP == "SIM" } {
   # Simulation only version
   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg  "MATH"] \
      [ list "SW_RXBUF"       $RX_BASE             "SIM"] \
      [ list "SW_TXBUF"       $TX_BASE             "BOTH"] \
   ]
} elseif { $ARCHGRP == "NEWDMA" } {
   # NEW DMA modules

   set MOD       "$MOD $ENTITY_BASE/rxtx_buffers_opt.vhd"
   set MOD       "$MOD $ENTITY_BASE/rxtx_buffers_64b.vhd"
   set MOD       "$MOD $ENTITY_BASE/rx_buffers_64b.vhd"
   set MOD       "$MOD $ENTITY_BASE/rx_buffers_2x64b.vhd"
   set MOD       "$MOD $ENTITY_BASE/rx_buffers_Nx64b.vhd"

   set COMPONENTS [list \
      [ list "DEC1FN"         $DEC1FN_BASE                             "FULL"] \
      [ list "FL_SPLITTER"    $SPLITTER_BASE                           "FULL"] \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg                      "MATH"] \
      [ list "SW_RXBUF"       $RX_BASE                                 "BOTH"] \
      [ list "SW_TXBUF"       $TX_BASE                                 "BOTH"] \
      [ list "DMA_CTRL"       $ICS_BASE/dma_ctrl                       "FULL"] \
      [ list "IB_EP"          $IBEP_BASE                               "FULL"] \
      [ list "BM_CONVERTER"   $BM_CONVERTER_BASE                       "FULL"] \
      [ list "TAG_SEQUENCER"  $TAG_SEQ_BASE                            "FULL"] \
   ]
} elseif { $ARCHGRP == "PACDMA" } {
   # PAC DMA modules

   set MOD       "$MOD $ICS_BASE/dma_ctrl/comp/dma_status_reg.vhd"
   set MOD       "$MOD $ENTITY_BASE/rxtx_buffers_pac.vhd"
   set MOD       "$MOD $ENTITY_BASE/rxtx_buffers_pac_64b.vhd"

   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg                      "MATH"] \
      [ list "SW_RXBUF"       $RX_BASE                                 "BOTH"] \
      [ list "SW_TXBUF"       $TX_BASE                                 "BOTH"] \
      [ list "IB_EP"          $IBEP_BASE                               "FULL"] \
      [ list "PAC_DMA_CTRL"   $ICS_BASE/pac_dma_ctrl                   "FULL"] \
      [ list "BM_CONVERTER"   $BM_CONVERTER_BASE                       "FULL"] \
      [ list "TAG_SEQUENCER"  $TAG_SEQ_BASE                            "FULL"] \
   ]
} else {
   puts "Unsupported ARCHGRP: $ARCHGRP"
   exit 1
}
      #[ list "IB_PIPE"        $GICS_BASE/internal_bus/comp/base/pipe   "FULL"] \
      #[ list "TRIMMER"        $FL_BASE/edit/trimmer                    "FULL"] \
