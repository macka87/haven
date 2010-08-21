# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Martin Louda <sandin@liberouter.org>
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

set COMP_BASE     "$ENTITY_BASE/../../.." 
set I2C_BASE      "$COMP_BASE/ctrls/i2c"

# Full architecture of I2C controller
if { $ARCHGRP == "FULL" } {
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c.vhd"
}

# Empty architecture of I2C controller
if { $ARCHGRP == "EMPTY" } {
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_empty.vhd"
}

# Full architecture of I2C controller with MI32 interface
if { $ARCHGRP == "MI32_FULL" } {
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_norec_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_norec.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_mi32.vhd"
    set MOD "$MOD $ENTITY_BASE/top/phyter_i2c_mi32_4ifc.vhd"

    set PACKAGES "$COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
}

# Empty architecture of I2C controlle with MI32 interface
if { $ARCHGRP == "MI32_EMPTY" } {
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_norec_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_norec_empty.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_mi32.vhd"
    set MOD "$MOD $ENTITY_BASE/top/phyter_i2c_mi32_4ifc.vhd"

    set PACKAGES "$COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
}

# Full generic architecture of I2C controller with localbus interface
if { $ARCHGRP == "LB_FULL" } {
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_norec_ent.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_norec.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_mi32.vhd"
    set MOD "$MOD $ENTITY_BASE/phyter_i2c_generic_lb.vhd"

    set PACKAGES "$COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
}

# Components
set COMPONENTS [list \
    [list "I2C_SW"    $I2C_BASE   "SW"] \
]
