# Modules.tcl: Local include tcl script
# Copyright (C) 2008 CESNET
# Author: Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
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

# Base directories
set FIRMWARE_BASE  "$ENTITY_BASE/../../../.."
set MATH_PACK_BASE "$FIRMWARE_BASE/comp/base/pkg"

if { $ARCHGRP == "FULL" } {
   set BASECOMP_BASE "$FIRMWARE_BASE/comp/base"
   set BUFCOMP_BASE  "$BASECOMP_BASE/buffers/comp"
   set BMEM_BASE     "$BASECOMP_BASE/mem/dp_bmem"
   set SH_FIFO_BASE  "$BASECOMP_BASE/fifo/sh_fifo"

# Source files for all components
   set PACKAGES  "$MATH_PACK_BASE/math_pack.vhd"

   set COMPONENTS [list \
      [list "MATH_PACK"  $MATH_PACK_BASE "MATH"] \
      [list "RX_SWITCH"  $BUFCOMP_BASE   "FULL"] \
      [list "TX_SWITCH"  $BUFCOMP_BASE   "FULL"] \
      [list "BUF_MEM"    $BUFCOMP_BASE   "FULL"] \
      [list "BUF_STATUS" $BUFCOMP_BASE   "FULL"] \
      [list "SH_FIFO"    $SH_FIFO_BASE   "FULL"]]

   set MOD "$MOD $ENTITY_BASE/nfifo2mem.vhd"
   set MOD "$MOD $ENTITY_BASE/nfifo.vhd"
   set MOD "$MOD $ENTITY_BASE/nfifo2fifo.vhd"
   set MOD "$MOD $ENTITY_BASE/mem2nfifo.vhd"
   set MOD "$MOD $ENTITY_BASE/fifo2nfifo.vhd"
   set MOD "$MOD $ENTITY_BASE/mfifo2mem.vhd"
}
