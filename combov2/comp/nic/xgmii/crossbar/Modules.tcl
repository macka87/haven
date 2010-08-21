# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Jan Viktorin <xvikto03@liberouter.org>
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

# Set paths
set FIRMWARE_BASE    "$ENTITY_BASE/../../../.."
set COMP_BASE        "$FIRMWARE_BASE/comp"
set PKG_BASE         "$COMP_BASE/base/pkg"                                                                                                                                 
set I2C_SLAVE_BASE   "$COMP_BASE/ctrls/i2c_slave_hw"
set XGMII_BASE       "$ENTITY_BASE/../pkg"
set XGMII_MUX_BASE   "$ENTITY_BASE/../mux"

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   # components                                                                                                                                                          
    set COMPONENTS [list \
        [list "I2C_SLAVE_TOP"   $I2C_SLAVE_BASE    "FULL"] \
        [list "PKG_MATH"        $PKG_BASE          "MATH"] \
        [list "XGMII_MUX"       $XGMII_MUX_BASE    "FULL"] \
    ]
   
   # modules setting
   set PACKAGES "$PACKAGES $XGMII_BASE/xgmii_pkg.vhd"

   set MOD "$MOD $ENTITY_BASE/crossbar_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/crossbar.vhd"
   set MOD "$MOD $ENTITY_BASE/crossbar_config_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/crossbar_config.vhd"
   set MOD "$MOD $ENTITY_BASE/packet_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/remap_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/crossbar_strict.vhd"

   set MOD "$MOD $ENTITY_BASE/crossbar_top.vhd"
   set MOD "$MOD $ENTITY_BASE/crossbar6.vhd"
}



