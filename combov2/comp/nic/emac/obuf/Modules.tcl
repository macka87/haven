# Modules.tcl: Local include tcl script
# Copyright (C) 2007 CESNET
# Author(s): Libor Polcak <polcak_l@liberouter.org>
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
set COMP_BASE           "$ENTITY_BASE/../../.."

set OBUF_GMII_BASE      "$COMP_BASE/nic/gmii/obuf"
set OBUF_GMII_FL_BASE   "$OBUF_GMII_BASE/comp/fl"
set OBUF_EMAC_BUF_BASE  "$ENTITY_BASE/comp/buf"
set OBUF_EMAC_TX_BASE   "$ENTITY_BASE/comp/tx"
set MI32_ASYNC_BASE     "$COMP_BASE/ics/local_bus/comp/lb_endpoint/comp/mi32_async"

set MOD "$MOD $ENTITY_BASE/obuf_emac_ent.vhd"

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   set PACKAGES "$PACKAGES $COMP_BASE/base/pkg/math_pack.vhd"
   set PACKAGES "$PACKAGES $COMP_BASE/fl_tools/pkg/fl_pkg.vhd"
   set PACKAGES "$PACKAGES $COMP_BASE/external/ip_cores/emac/pkg/emac_pkg.vhd"
   set PACKAGES "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
   set PACKAGES "$PACKAGES $OBUF_GMII_BASE/pkg/obuf_pkg.vhd"

   
   # List of components
   set COMPONENTS [list \
      [list "CMD_DEC"        $COMP_BASE/base/misc/cmd_dec     "FULL" ]  \
      [list "ASFIFO_BRAM"    $COMP_BASE/base/fifo/asfifo_bram "FULL" ]  \
      [list "ASFIFO"         $COMP_BASE/base/fifo/asfifo      "FULL" ]  \
      [list "OBUF_GMII_FL"   $OBUF_GMII_FL_BASE               "FULL" ]  \
      [list "OBUF_EMAC_BUF"  $OBUF_EMAC_BUF_BASE              "FULL" ]  \
 		  [list "MI32_ASYNC"     $MI32_ASYNC_BASE                 "FULL" ]  \
      [list "OBUF_EMAC_TX"   $OBUF_EMAC_TX_BASE               "FULL" ]  \
   ]

   set MOD "$MOD $ENTITY_BASE/obuf_emac_top2_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/obuf_emac_top2_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/obuf_emac_top4_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/top/obuf_top2_fl16.vhd"
   set MOD "$MOD $ENTITY_BASE/obuf_emac.vhd"
}

# Source file for empty component - empty architecture 
if { $ARCHGRP  == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/obuf_emac_empty.vhd"
}  

