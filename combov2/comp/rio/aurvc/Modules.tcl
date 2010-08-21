# Modules.tcl: Local include tcl script
# Copyright (C) 2005 CESNET
# Author: Martin Mikusek <martin.mikusek@liberouter.org>
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

set COMP_BASE     "$ENTITY_BASE/../.." 
set FL_BASE       "$COMP_BASE/fl_tools" 

# Modules variable
set ASFIFO_BRAM "FULL"
set AURORA     "FULL" 
#set AURORA     8BYTE2LANE 

# Base directories
set PKG_BASE            "$COMP_BASE/base/pkg"
set AURVC_CORE_BASE     "$ENTITY_BASE/comp/aurvc_core"
set TX_CHNL_CTRL_BASE   "$ENTITY_BASE/comp/tx_chnl_ctrl"
set RX_CHNL_CTRL_BASE   "$ENTITY_BASE/comp/rx_chnl_ctrl"
set TX_BUFFER_BASE      "$ENTITY_BASE/comp/tx_buffer"
set RX_BUFFER_BASE      "$ENTITY_BASE/comp/rx_buffer"
set AURORA_BASE         "$COMP_BASE/external/ip_cores/aurora"

# List of packages
set PACKAGES "$PACKAGES $PKG_BASE/math_pack.vhd \
              $FL_BASE/pkg/fl_pkg.vhd \
              $ENTITY_BASE/pkg/aurvc_pkg.vhd"

# Lists of instantces
set AURORA_INST            [list [list "RIO_AURORA_MODULE_U"        "FULL"]]

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   # List of components
   set COMPONENTS [list \
         [list "AURORA"                   $AURORA_BASE        $AURORA         $AURORA_INST] \
 	  	   [list "AURVC CORE"               $AURVC_CORE_BASE    "FULL"]  \
 	  	   [list "TX CHANNEL CONTROLLER"    $TX_CHNL_CTRL_BASE  "FULL"]  \
 	  	   [list "RX CHANNEL CONTROLLER"    $RX_CHNL_CTRL_BASE  "FULL"]  \
 	  	   [list "TX BUFFER"                $TX_BUFFER_BASE     "FULL"]  \
 	  	   [list "RX BUFFER"                $RX_BUFFER_BASE     "FULL"]  \
 	     ]

   set MOD "$MOD $ENTITY_BASE/aurvc_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/aurvc.vhd"
}

# Source file for empty component - empty architecture 
if { $ARCHGRP  == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/aurvc_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/aurvc_empty.vhd"
}

   set MOD "$MOD $ENTITY_BASE/top/aurvc1x4_fl32.vhd"
   set MOD "$MOD $ENTITY_BASE/top/aurvc4x1_fl32.vhd"
   set MOD "$MOD $ENTITY_BASE/top/aurvc4x4_fl32.vhd"

   set MOD "$MOD $ENTITY_BASE/top/aurvc1x4_fl64.vhd"
   set MOD "$MOD $ENTITY_BASE/top/aurvc4x1_fl64.vhd"
   set MOD "$MOD $ENTITY_BASE/top/aurvc4x4_fl64.vhd"
