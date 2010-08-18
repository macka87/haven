# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
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

# Source files for all components
set COMP_BASE "$ENTITY_BASE/../.."

set MOD "$MOD $COMP_BASE/base/pkg/crc_pack.vhd"
set MOD "$MOD $ENTITY_BASE/phy_oper.vhd"

if { $ARCHGRP == "GMII"} {
   set MOD "$MOD $ENTITY_BASE/phy_sim_gmii.vhd"
}

if { $ARCHGRP == "EMAC"} {
   set MOD "$MOD $ENTITY_BASE/phy_sim_emac.vhd"
}

if { $ARCHGRP == "SFP"} {
   set MOD "$MOD $ENTITY_BASE/phy_sim_sfp.vhd"
}

if { $ARCHGRP == "XGMII"} {
   set MOD "$MOD $ENTITY_BASE/phy_sim_xgmii.vhd"
}

if { $ARCHGRP == "XGMII_SDR"} {
   set REP_BASE      "$ENTITY_BASE/../../nic/xgmii/repeater"

   set COMPONENTS [list \
      [list "DDR2SDR" "$ENTITY_BASE/../../nic/xgmii/ibuf/comp/ddr2sdr" "FULL"] \
      [list "SDR2DDR" "$ENTITY_BASE/../../nic/xgmii/obuf/comp/sdr2ddr" "FULL"] \
      [list "REPEATER"         $REP_BASE       "COMBOv2" ] \
   ]

   set MOD "$MOD $ENTITY_BASE/phy_sim_xgmii.vhd"
   set MOD "$MOD $ENTITY_BASE/phy_sim_xgmii_sdr.vhd"
}

if { $ARCHGRP == "RIO_ETH"} {
   set COMPONENTS [list [list "RIO_GMII" $COMP_BASE/rio/rio_gmii "FULL"] ]
   set MOD "$MOD $ENTITY_BASE/phy_sim_gmii.vhd"
   set MOD "$MOD $ENTITY_BASE/phy_sim_rio_eth.vhd"
}

if { $ARCHGRP == "RIO_EMAC"} {
   set COMPONENTS [list [list "EMAC" $COMP_BASE/external/ip_cores/emac "FULL"] ]
   set PACKAGES      "$PACKAGES $COMP_BASE/external/ip_cores/emac/pkg/emac_pkg.vhd"

   set MOD "$MOD $ENTITY_BASE/phy_sim_emac.vhd"
   set MOD "$MOD $ENTITY_BASE/phy_sim_rio_emac.vhd"
}
