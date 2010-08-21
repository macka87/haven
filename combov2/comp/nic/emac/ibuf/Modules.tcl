# Modules.tcl: Local include tcl script
# Copyright (C) 2007 CESNET
# Author: Martin Mikusek <martin.mikusek@liberouter.org>
#         Martin Kosek <kosek@liberouter.org>
#			 Polcak Libor <polcak_l@liberouter.org>
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
set COMP_BASE                   "$ENTITY_BASE/../../.."

set IBUF_GENERAL_PKG_BASE       "$COMP_BASE/nic/pkg"
set IBUF_GMII_BASE              "$COMP_BASE/nic/gmii/ibuf"
set IBUF_FL_COMPOSER_BASE       "$COMP_BASE/nic/common/ibuf/fl_composer"
set IBUF_GMII_MAC_CHECK_BASE    "$IBUF_GMII_BASE/comp/mac_check"
set IBUF_EMAC_BUF_BASE          "$ENTITY_BASE/comp/buf"
set IBUF_EMAC_RX_BASE           "$ENTITY_BASE/comp/rx"
set EMAC_EXTERNALS_BASE         "$COMP_BASE/external/ip_cores/emac"
set FIFO_PKG                    "$COMP_BASE/base/fifo/fifo_layers/pkg"
set MI32_ASYNC_BASE             "$COMP_BASE/ics/local_bus/comp/lb_endpoint/comp/mi32_async"

# List of packages
set PACKAGES "$PACKAGES $COMP_BASE/base/pkg/math_pack.vhd"
set PACKAGES "$PACKAGES $ENTITY_BASE/pkg/ibuf_emac_pkg.vhd"
set PACKAGES "$PACKAGES $IBUF_GENERAL_PKG_BASE/ibuf_general_pkg.vhd"
set PACKAGES "$PACKAGES $EMAC_EXTERNALS_BASE/pkg/emac_pkg.vhd"
set PACKAGES "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
set PACKAGES "$PACKAGES $FIFO_PKG/fifo_pkg.vhd"


# FULL version - MI32 interface only
if { $ARCHGRP == "FULL" } {

   # List of components
   set COMPONENTS [list \
    	[list "IBUF_EMAC_BUF"        	$IBUF_EMAC_BUF_BASE 			"FULL"]  \
 		[list "IBUF_EMAC_RX"         	$IBUF_EMAC_RX_BASE  			"FULL"]  \
 	  	[list "IBUF_FL"         		$IBUF_FL_COMPOSER_BASE  	"FULL"]  \
 	   [list "IBUF_GMII_MAC_CHECK"  	$IBUF_GMII_MAC_CHECK_BASE 	"FULL"]  \
 		[list "MI32_ASYNC"           	$MI32_ASYNC_BASE    			"FULL"]  \
 	 ]
	 
   set MOD "$MOD $ENTITY_BASE/ibuf_emac_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_emac.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_emac_top2_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_emac_top2_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_emac_top4_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/top/ibuf_top2_fl16.vhd"
}

# Source file for empty component - empty architecture 
if { $ARCHGRP  == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/ibuf_emac_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_emac_empty.vhd"
}

if { $ARCHGRP == "ONE" } {

   # List of components
   set COMPONENTS [list \
      [list "IBUF_EMAC_BUF"        	$IBUF_EMAC_BUF_BASE       		"FULL"]  \
 	   [list "IBUF_FL"         		$IBUF_FL_COMPOSER_BASE        "FULL"]  \
 	   [list "IBUF_GMII_MAC_CHECK"  	$IBUF_GMII_MAC_CHECK_BASE 		"FULL"]  \
 		[list "IBUF_EMAC_RX"         	$IBUF_EMAC_RX_BASE        		"FULL"]  \
 	 ]

   set MOD "$MOD $ENTITY_BASE/ibuf_emac_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_emac.vhd"
}

