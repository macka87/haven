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
set ICS_BASE      "$COMP_BASE/ics"
set FIFO_BASE     "$COMP_BASE/base/fifo/fifo"

set PACKAGES   "$PACKAGES $ENTITY_BASE/pkg/sw_txbuf_pkg.vhd"

set MOD       "$MOD $FL_BASE/pkg/fl_pkg.vhd" 
set MOD       "$MOD $ICS_BASE/internal_bus/pkg/ib_pkg.vhd"
set MOD       "$MOD $ENTITY_BASE/sw_txbuf_ent.vhd"

# Source files for the component
if { $ARCHGRP == "FULL" || $ARCHGRP == "BOTH" } {
   set MOD "$MOD $ENTITY_BASE/sw_txbuf_func.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/fifo_ctrl.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/hw_header_sender.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/cu_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/cu.vhd"
   set MOD "$MOD $ENTITY_BASE/sw_txbuf.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/cb_mgmt.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/cb_mgmt_fl16.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/header_rearranger/header_rearranger.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/parser/parser_16b.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/parser/parser_32b.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/parser/parser_64b.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/parser/parser.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/parser_pac/parser_pac.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/fl_reorderer.vhd"

   set MOD "$MOD $ENTITY_BASE/top/sw_txbuf_fl16.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_txbuf_fl16_top4.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_txbuf_fl16_top4_nocb.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_txbuf_pac_top.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_txbuf_top.vhd"

   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg           "MATH"] \
      [ list "MUX"            $COMP_BASE/base/logic/mux     "FULL"] \
      [ list "DEMUX"          $COMP_BASE/base/logic/demux   "FULL"] \
      [ list "DP_BMEM"        $COMP_BASE/base/mem/dp_bmem   "FULL"] \
      [ list "FIFO"           $FIFO_BASE                    "FULL"] \
      [ list "TRANSFORMER"    $FL_BASE/flow/transformer     "FULL"] \
      [ list "DP_DISTMEM"     $COMP_BASE/base/mem/dp_distmem "FULL"] \
      [ list "MEM2NFIFO"      $COMP_BASE/base/buffers/top   "FULL"] \
      [ list "FL_PIPE"        $COMP_BASE/fl_tools/flow/pipe "FULL"] \
      [ list "SH_FIFO"        $COMP_BASE/base/fifo/sh_fifo  "FULL"] \
   ]
   
   # Both full SW_TXBUF architecture and empty architecture
   if {$ARCHGRP == "BOTH" } {
      set MOD "$MOD $ENTITY_BASE/sw_txbuf_empty.vhd"
      set MOD "$MOD $ENTITY_BASE/top/sw_txbuf_fl16_top4_empty.vhd"
      set MOD "$MOD $ENTITY_BASE/top/sw_txbuf_fl16_top4_nocb_empty.vhd"
   }
}

if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/sw_txbuf_empty.vhd"

   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg           "MATH"] \
   ]
}
