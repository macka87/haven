# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Libor Polcak <polcak_l@liberouter.org>
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
set FIRMWARE_BASE       "$ENTITY_BASE/../../../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"
set XGMII_BASE          "$ENTITY_BASE/../../.."
set IBUF_PKG            "$XGMII_BASE/ibuf/pkg"
set SH_REG_BASE         "$BASE_BASE/shreg/sh_reg"
set SH_FIFO_BASE        "$BASE_BASE/fifo/sh_fifo"
set CRC_BASE            "$COMP_BASE/nic/crc/v5_crc"

set PACKAGES "$PACKAGES $IBUF_PKG/ibuf_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/check_ent.vhd"

# Full Check
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/crc_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/check.vhd"
   
   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"       $BASE_BASE/pkg       "MATH" ] \
      [ list "SH_REG"         $SH_REG_BASE         "FULL" ] \
      [ list "SH_FIFO"        $SH_FIFO_BASE        "FULL" ] \
      [ list "CRC"            $CRC_BASE            "FULL" ] \
   ]
}

