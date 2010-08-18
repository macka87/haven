# Modules.tcl: Local include tcl script
# Copyright (C) 2005 CESNET
# Author: Stepan Friedl <friedl@liberouter.org>
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
set BASE_BASE       "$ENTITY_BASE/../../../base"
set COMP_BASE       "$ENTITY_BASE/../../.."

set ASFIFO_BASE     "$BASE_BASE/fifo/asfifo_bram"
set MI32_ASYNC_BASE "$COMP_BASE/ics/local_bus/comp/lb_endpoint/comp/mi32_async"

# List of packages
set PACKAGES "$ENTITY_BASE/../../../ics/local_bus/pkg/lb_pkg.vhd"
   

# Source files for implemented component
if { $ARCHGRP == "FULL" } {
   # List of components
   set COMPONENTS [list [list "ASFIFO_BRAM"  $ASFIFO_BASE     "FULL"] \
                        [list "MI32_ASYNC"   $MI32_ASYNC_BASE "FULL"] \
                  ]
   set MOD "$MOD $ENTITY_BASE/xgmii_tx.vhd"   
   set MOD "$MOD $ENTITY_BASE/rep_2port_cover.vhd"
   set MOD "$MOD $ENTITY_BASE/rep_2port_top.vhd"
}

# Source files for Combov2
if { $ARCHGRP == "COMBOv2" } {
   # List of components
   set COMPONENTS [list [list "ASFIFO_BRAM"  $ASFIFO_BASE     "FULL"] \
                        [list "MI32_ASYNC"   $MI32_ASYNC_BASE "FULL"] \
                  ]
   set MOD "$MOD $ENTITY_BASE/pckt_fwd.vhd"
   set MOD "$MOD $ENTITY_BASE/rep_2port.vhd"
   set MOD "$MOD $ENTITY_BASE/rep_2port_sdr_top_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/rep_2port_sdr_top_arch.vhd"
}

# Source file for empty component - empty architecture
if { $ARCHGRP == "EMPTY" } {
}
