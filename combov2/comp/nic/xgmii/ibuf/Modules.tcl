# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Libor Polcak <polcak_l@liberouter.org>
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

# Set paths
set FIRMWARE_BASE    "$ENTITY_BASE/../../../.."
set COMP_BASE        "$FIRMWARE_BASE/comp"
set BASE_BASE        "$COMP_BASE/base"
set IBUF_COMP_BASE   "$ENTITY_BASE/comp"
set DDR2SDR_BASE     "$IBUF_COMP_BASE/ddr2sdr"
set ALIGN_BASE       "$IBUF_COMP_BASE/align"
set XGMII_DEC_BASE   "$IBUF_COMP_BASE/xgmii_dec"
set CHECK_BASE       "$IBUF_COMP_BASE/check"
set BUF_BASE         "$IBUF_COMP_BASE/buf"
set FL_COMPOSER_BASE "$COMP_BASE/nic/common/ibuf/fl_composer"
set MI_INT_BASE      "$IBUF_COMP_BASE/mi_int"
set FIFO_PKG         "$BASE_BASE/fifo/fifo_layers/pkg"

set PACKAGES "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
set PACKAGES "$PACKAGES $ENTITY_BASE/pkg/ibuf_pkg.vhd"
set PACKAGES "$PACKAGES $FIFO_PKG/fifo_pkg.vhd"
set PACKAGES "$PACKAGES $COMP_BASE/nic/pkg/ibuf_general_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr_norec_ent.vhd"
set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr_pcd_norec_ent.vhd"
set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_norec_ent.vhd"
set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr_ent.vhd"
set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_ent.vhd"
set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_top2_mi32_ent.vhd"
set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr_top2_mi32_ent.vhd"

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   # list of sub-components
   set COMPONENTS [list \
      [ list "PKG_MATH"     $BASE_BASE/pkg    "MATH" ]  \
      [ list "XGMII"        $DDR2SDR_BASE     "FULL" ]  \
      [ list "ALIGN"        $ALIGN_BASE       "FULL" ]  \
      [ list "XGMII_DEC"    $XGMII_DEC_BASE   "FULL" ]  \
      [ list "CHECK"        $CHECK_BASE       "FULL" ]  \
      [ list "BUF"          $BUF_BASE         "FULL" ]  \
      [ list "FL_COMPOSER"  $FL_COMPOSER_BASE "FULL" ]  \
      [ list "MI_INT"       $MI_INT_BASE      "FULL" ]  \
   ]

   # modules setting
   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr_norec.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_norec.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr_pcd_norec.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_top2_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_sdr_top2_mi32.vhd"

   # Covers
   set MOD "$MOD $ENTITY_BASE/top/ibuf_xgmii_sdr_fl128.vhd"
   set MOD "$MOD $ENTITY_BASE/top/ibuf_xgmii_fl128.vhd"
}


if { $ARCHGRP == "CRC_INCLUDE" } {

    set CRC_BASE         "$COMP_BASE/nic/crc/crc64"

    set COMPONENTS [list \
            [list "IBUF_XGMII"     $ENTITY_BASE    "FULL"] \
        ]
}


# Empty architecture
if { $ARCHGRP == "EMPTY" } {

   # list of sub-components
   set COMPONENTS [list \
      [ list "PKG_MATH"     $BASE_BASE/pkg    "MATH" ]  \
   ]

   set MOD "$MOD $ENTITY_BASE/ibuf_xgmii_empty.vhd"
} 
