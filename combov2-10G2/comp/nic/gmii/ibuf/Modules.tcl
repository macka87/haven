# Modules.tcl: Local include tcl script
# Copyright (C) 2007 CESNET
# Author: Martin Mikusek <martin.mikusek@liberouter.org>
#         Martin Kosek <kosek@liberouter.org>
#         Libor Polcak <polcak_l@liberouter.org>
#         Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
set COMP_BASE               "$ENTITY_BASE/../../.."

set IBUF_GMII_BASE          "$COMP_BASE/nic/gmii/ibuf"
set IBUF_GMII_FL_BASE       "$COMP_BASE/nic/common/ibuf/fl_composer"
set IBUF_GMII_MAC_CHECK_BASE    "$IBUF_GMII_BASE/comp/mac_check"
set IBUF_GMII_BUF_BASE      "$IBUF_GMII_BASE/comp/buf"
set IBUF_GMII_RX_BASE       "$IBUF_GMII_BASE/comp/rx"

set LB_BASE                 "$COMP_BASE/old/lb"
set LB_ASYNC_BASE           "$LB_BASE/comp/lb_async"
set MI32_ASYNC_BASE         "$COMP_BASE/ics/local_bus/comp/lb_endpoint/comp/mi32_async"

# List of packages
set PACKAGES      "$COMP_BASE/base/pkg/math_pack.vhd \
                   $COMP_BASE/fl_tools/pkg/fl_pkg.vhd \
                   $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd \
                   $IBUF_GMII_BASE/pkg/ibuf_pkg.vhd \
                   $COMP_BASE/nic/pkg/ibuf_general_pkg.vhd"

# FULL version - both LB and MI32 interface
if { $ARCHGRP == "FULL" } {

   # List of components
   set COMPONENTS [list \
 	  	      [list "IBUF_GMII_FL"   $IBUF_GMII_FL_BASE  "FULL"]  \
 	         [list "IBUF_GMII_MAC_CHECK"  $IBUF_GMII_MAC_CHECK_BASE "FULL"]  \
 	         [list "IBUF_GMII_BUF"  $IBUF_GMII_BUF_BASE "FULL"]  \
 		      [list "IBUF_GMII_RX"   $IBUF_GMII_RX_BASE  "FULL"]  \
 		      [list "LB_ASYNC"       $LB_ASYNC_BASE      "FULL"]  \
 		      [list "MI32_ASYNC"     $MI32_ASYNC_BASE    "FULL"]  \
 	      ]
	 
   set MOD "$MOD $LB_BASE/lbconn_mem.vhd"

   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top1_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top1.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top2_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top2_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/top/ibuf_top2_fl16.vhd"
   set MOD "$MOD $ENTITY_BASE/top/ibuf_top4_fl16.vhd"
}

# FULL IBUF - MI32 interface only
if { $ARCHGRP == "FULL_MI32" } {

   # List of components
   set COMPONENTS [list \
 	  	   [list "IBUF_GMII_FL"   $IBUF_GMII_FL_BASE  "FULL"]  \
 	      [list "IBUF_GMII_MAC_CHECK"  $IBUF_GMII_MAC_CHECK_BASE "FULL"]  \
 	      [list "IBUF_GMII_BUF"  $IBUF_GMII_BUF_BASE "FULL"]  \
 		   [list "IBUF_GMII_RX"   $IBUF_GMII_RX_BASE  "FULL"]  \
 		   [list "MI32_ASYNC"     $MI32_ASYNC_BASE    "FULL"]  \
 	  ]
	 
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top2_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top2_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/top/ibuf_top2_fl16.vhd"
   set MOD "$MOD $ENTITY_BASE/top/ibuf_top4_fl16.vhd"
}

# Source file for empty component - empty architecture 
if { $ARCHGRP  == "EMPTY" } {
   set MOD "$MOD $IBUF_GMII_BASE/ibuf_gmii_ent.vhd"
   set MOD "$MOD $IBUF_GMII_BASE/ibuf_gmii_empty.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top1_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top1_empty.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_gmii_top4.vhd"
}

if { $ARCHGRP == "ONE" } {

   #set PACKAGES "$COMMON_BASE/pkg/math_pack.vhd"


   # List of components
   set COMPONENTS [list \
 	  	      [list "IBUF_GMII_FL"   $IBUF_GMII_FL_BASE  "FULL"]  \
 	         [list "IBUF_GMII_MAC_CHECK"  $IBUF_GMII_MAC_CHECK_BASE "FULL"]  \
 	         [list "IBUF_GMII_BUF"  $IBUF_GMII_BUF_BASE "FULL"]  \
 		      [list "IBUF_GMII_RX"   $IBUF_GMII_RX_BASE  "FULL"]  \
 	      ]

   set MOD "$MOD $IBUF_GMII_BASE/ibuf_gmii_ent.vhd"
   set MOD "$MOD $IBUF_GMII_BASE/ibuf_gmii.vhd"
}

