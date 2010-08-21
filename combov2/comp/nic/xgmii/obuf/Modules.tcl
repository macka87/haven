# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2008 CESNET
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
set FIRMWARE_BASE       "$ENTITY_BASE/../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"
set XGMII_OBUF_PKG_BASE "$ENTITY_BASE/pkg"
set OBUF_COMP_BASE      "$ENTITY_BASE/comp"
set SDR2DDR_BASE        "$OBUF_COMP_BASE/sdr2ddr"
set FL_PART_BASE        "$OBUF_COMP_BASE/fl"
set BUF_BASE            "$OBUF_COMP_BASE/buf"
set PROCESS_BASE        "$OBUF_COMP_BASE/process"
set XGMII_ENC_BASE      "$OBUF_COMP_BASE/xgmii_enc"
set FIFO_PKG            "$BASE_BASE/fifo/fifo_layers/pkg"
set MI_SPLITTER_BASE    "$COMP_BASE/gics/internal_bus/comp/base/mi_splitter"

set PACKAGES "$PACKAGES $XGMII_OBUF_PKG_BASE/xgmii_obuf_pkg.vhd"
set PACKAGES "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
set PACKAGES "$PACKAGES $FIFO_PKG/fifo_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/obuf_xgmii_sdr_norec_ent.vhd"
set MOD "$MOD $ENTITY_BASE/obuf_xgmii_sdr_ent.vhd"
set MOD "$MOD $ENTITY_BASE/obuf_xgmii_ent.vhd"
set MOD "$MOD $ENTITY_BASE/obuf_xgmii_top2_mi32_ent.vhd"
set MOD "$MOD $ENTITY_BASE/obuf_xgmii_sdr_top2_mi32_ent.vhd"

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   # list of sub-components
   set COMPONENTS [list \
      [ list "PKG_MATH"     $BASE_BASE/pkg    "MATH" ]  \
      [ list "XGMII"        $SDR2DDR_BASE     "FULL" ]  \
      [ list "FL_PART"      $FL_PART_BASE     "FULL" ]  \
      [ list "BUF"          $BUF_BASE         "FULL" ]  \
      [ list "PROCESS"      $PROCESS_BASE     "FULL" ]  \
      [ list "XGMII_ENC"    $XGMII_ENC_BASE   "FULL" ]  \
      [ list "MI_SPLITTER"  $MI_SPLITTER_BASE "FULL" ]  \
   ]

   # modules setting
   set MOD "$MOD $ENTITY_BASE/obuf_xgmii_sdr_norec.vhd"
   set MOD "$MOD $ENTITY_BASE/obuf_xgmii_sdr.vhd"
   set MOD "$MOD $ENTITY_BASE/obuf_xgmii.vhd"
   set MOD "$MOD $ENTITY_BASE/obuf_xgmii_top2_mi32.vhd"
   set MOD "$MOD $ENTITY_BASE/obuf_xgmii_sdr_top2_mi32.vhd"

   # Covers
   #set MOD "$MOD $ENTITY_BASE/top/obuf_xgmii_fl128.vhd"
}

# Empty architecture
if { $ARCHGRP == "EMPTY" } {

   # list of sub-components
   set COMPONENTS [list \
      [ list "PKG_MATH"     $BASE_BASE/pkg    "MATH" ]  \
   ]

   set MOD "$MOD $ENTITY_BASE/obuf_xgmii_empty.vhd"
}
