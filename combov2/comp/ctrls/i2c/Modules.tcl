# Modules.tcl: Local include tcl script
# Copyright (C) 2006 CESNET
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

# Base directories
set COMP_BASE           "$ENTITY_BASE/../.." 

# Source files for implemented component
if { $ARCHGRP == "FULL" } {
   set LB         "FULL"
   set LB_INST         [list [list "LB_U"         "FULL"]]
   set LB_BASE          "$COMP_BASE/lb"

   set COMPONENTS [list   \
      [list "LB"         $LB_BASE           $LB         $LB_INST    ]\   
   ]
   #set PACKAGES "$COMMON_BASE/pkg/math_pack.vhd"

   set MOD "$MOD $ENTITY_BASE/i2c_master_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/i2c_master.vhd"
   set MOD "$MOD $ENTITY_BASE/i2c.vhd"
}

# Source files for implemented component
if { $ARCHGRP == "SW" } {
    set MOD "$MOD $ENTITY_BASE/i2c_sw.vhd"
}

# Source file for empty component - empty architecture 
if { $ARCHGRP == "EMPTY" } {
}

# debug component
if { $ARCHGRP == "DEBUG" } {
}
