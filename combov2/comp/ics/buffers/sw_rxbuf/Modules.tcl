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
set FL_DEC_BASE   "$COMP_BASE/fl_tools/misc/decoder"
set FL_TRIMMER_BASE "$COMP_BASE/fl_tools/edit/trimmer"

# Common files
set MOD        "$MOD $FL_BASE/pkg/fl_pkg.vhd"
set MOD        "$MOD $ICS_BASE/internal_bus/pkg/ib_pkg.vhd"
set MOD        "$MOD $ENTITY_BASE/sw_rxbuf_ent.vhd"

# Source files for the component
if { $ARCHGRP == "FULL" || $ARCHGRP == "BOTH" } {
   set MOD "$MOD $ENTITY_BASE/swr_bmem_ctrl.vhd"
   set MOD "$MOD $ENTITY_BASE/swr_cu.vhd"
   set MOD "$MOD $ENTITY_BASE/swr_fifo_ctrl.vhd"
   set MOD "$MOD $ENTITY_BASE/sw_rxbuf.vhd"
   set MOD "$MOD $ENTITY_BASE/swr_cb_mgmt.vhd"
   set MOD "$MOD $ENTITY_BASE/swr_cb_mgmt_fl16.vhd"
   set MOD "$MOD $ENTITY_BASE/swr_filler.vhd"
   
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_nocb.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_top4.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_pac_top.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_top.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg              "MATH"] \
      [ list "MUX"            $COMP_BASE/base/logic/mux        "FULL"] \
      [ list "DEMUX"          $COMP_BASE/base/logic/demux      "FULL"] \
      [ list "FL_DEC"         $FL_DEC_BASE                     "FULL"] \
      [ list "FL_TRIMMER"     $FL_TRIMMER_BASE                 "FULL"] \
      [ list "DP_BMEM"        $COMP_BASE/base/mem/dp_bmem      "FULL"] \
      [ list "DP_DISTMEM"     $COMP_BASE/base/mem/dp_distmem   "FULL"] \
      [ list "FIFO"           $COMP_BASE/base/fifo/fifo        "FULL"] \
      [ list "NFIFO2MEM"      $COMP_BASE/base/buffers/top      "FULL"] \
      [ list "SH_REG"         $COMP_BASE/base/shreg/sh_reg     "FULL"] \
      [ list "SH_FIFO"        $COMP_BASE/base/fifo/sh_fifo     "FULL"] \
   ]

   # Both full and empty SW_TXBUF architecture
   if {$ARCHGRP == "BOTH" } {
      set MOD "$MOD $ENTITY_BASE/sw_rxbuf_empty.vhd"
      set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_empty.vhd"
      set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_nocb_empty.vhd"
   }
}

# Simulation only version of SW_RXBUF
if { $ARCHGRP == "SIM" } {
   set MOD "$MOD $ENTITY_BASE/sw_rxbuf_sim.vhd"
   set MOD "$MOD $ENTITY_BASE/swr_cb_mgmt.vhd"
   set MOD "$MOD $ENTITY_BASE/swr_cb_mgmt_fl16.vhd"

   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg        "MATH"] \
   ]
   
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_nocb.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_top4.vhd"
   
   set MOD "$MOD $ENTITY_BASE/sw_rxbuf_empty.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_empty.vhd"
   set MOD "$MOD $ENTITY_BASE/top/sw_rxbuf_fl64_nocb_empty.vhd"
}

if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/sw_rxbuf_empty.vhd"

   set COMPONENTS [list \
      [ list "PKG_MATH"       $COMP_BASE/base/pkg        "MATH"] \
   ]
}
