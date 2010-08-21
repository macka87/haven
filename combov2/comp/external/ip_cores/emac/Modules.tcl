# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
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

set COMP_BASE     $ENTITY_BASE/../../..

# List of packages
set PACKAGES "$ENTITY_BASE/pkg/emac_pkg.vhd"

# Source files for implemented component
# EMAC for LXT chips
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/v5_emac_v1_6/rocketio_wrapper_gtp_tile.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_emac_v1_6/rocketio_wrapper_gtp.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_emac_v1_6/rx_elastic_buffer.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_emac_v1_6/gtp_dual_1000X.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_emac_v1_6/v5_emac_v1_6.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_emac_v1_6/v5_emac_v1_6_block.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_emac_v1_6/rio_emac.vhd"

   # covers
   set MOD "$MOD $ENTITY_BASE/emac_top2_norec.vhd"
}

# EMAC for FXT chips
if { $ARCHGRP == "FXT" } {
   set MOD "$MOD $ENTITY_BASE/v5_fxt_emac_v1_5/rocketio_wrapper_gtx_tile.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_fxt_emac_v1_5/rocketio_wrapper_gtx.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_fxt_emac_v1_5/gtx_dual_1000X.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_fxt_emac_v1_5/v5_emac_v1_5.vhd"
   set MOD "$MOD $ENTITY_BASE/v5_fxt_emac_v1_5/v5_emac_v1_5_block.vhd"

   # covers
   set MOD "$MOD $ENTITY_BASE/fxt_emac_top2_norec.vhd"
}

# Help files for PHY simulation with EMAC
if { $ARCHGRP == "SIM" } {
   set MOD "$MOD $ENTITY_BASE/simulation/configuration_tb.vhd"
   set MOD "$MOD $ENTITY_BASE/simulation/emac0_phy_tb.vhd"
   set MOD "$MOD $ENTITY_BASE/simulation/emac1_phy_tb.vhd"
}


