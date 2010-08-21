# Modules.tcl: Modules.tcl script to compile status upload manager
# Copyright (C) 2009 CESNET
# Author: Petr Kastovsky <kastovsky@liberouter.org>
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
# 
# $Id$
#

if {$ARCHGRP == "FULL"} {

   set COMP_BASE     "$ENTITY_BASE/../.."

   # Components
   set RX_CTRL       "FULL"
   set TX_CTRL       "FULL"
   set DDM           "FULL"
   set SUM           "FULL"
   set NFIFO         "FULL"
   set DEC1FN        "FULL"


   # Base directories
   set RX_CTRL_BASE  "$ENTITY_BASE/comp/rx_ctrl"
   set TX_CTRL_BASE  "$ENTITY_BASE/comp/tx_ctrl"
   set DDM_BASE      "$ENTITY_BASE/comp/ddm"
   set SUM_BASE      "$ENTITY_BASE/comp/sum"
   set NFIFO_BASE    "$COMP_BASE/base/buffers/top"
   set DEC1FN_BASE   "$COMP_BASE/base/logic/dec1fn"


   set PACKAGES   "$PACKAGES $COMP_BASE/base/pkg/math_pack.vhd"
   set PACKAGES   "$PACKAGES $ENTITY_BASE/pkg/pac_dma_pkg.vhd"

   set USED_COMPONENTS [list \
                        [list "RX_CTRL"   $RX_CTRL_BASE    $RX_CTRL] \
                        [list "TX_CTRL"   $TX_CTRL_BASE    $TX_CTRL] \
                        [list "DDM"       $DDM_BASE        $DDM] \
                        [list "SUM"       $SUM_BASE        $SUM] \
                        [list "NFIFO"     $NFIFO_BASE      $NFIFO] \
                        [list "DEC1FN"    $DEC1FN_BASE     $DEC1FN] \
                       ]

   set COMPONENTS "$USED_COMPONENTS $COMPONENTS"

   set MOD  "$MOD $COMP_BASE/ics/dma_ctrl/comp/dma2data.vhd"
   set MOD  "$MOD $COMP_BASE/ics/dma_ctrl/comp/data2bm.vhd"
   set MOD  "$MOD $ENTITY_BASE/dma_ctrl_ent.vhd"
   set MOD  "$MOD $ENTITY_BASE/dma_ctrl_arch.vhd"

} else {
   error "$ENTITY_MODFILE: Unsupported ARCHGRP: $ARCHGRP" "" "1"
}
