# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Pribyl Bronislav <xpriby12@stud.fit.vutbr.cz>
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
set FIRMWARE_BASE  "$ENTITY_BASE/../../../../../.."
set MATH_PACK_BASE "$FIRMWARE_BASE/comp/base/pkg"

if { $ARCHGRP == "FULL" } {
   set BASECOMP_BASE       "$FIRMWARE_BASE/comp/base"
   set FIFO_MEM_BASE       "$BASECOMP_BASE/fifo/fifo_layers/fifo_mem"
   set CNT_BASE            "$BASECOMP_BASE/logic/cnt"
   set ASYNC_ORD_BASE      "$BASECOMP_BASE/fifo/fifo_layers/fifo_core/async_ord"

# Source files for all components
   set PACKAGES  "$MATH_PACK_BASE/math_pack.vhd \ 
               $FIFO_MEM_BASE/../pkg/fifo_pkg.vhd"

   set COMPONENTS [list\
      [list   "MATH_PACK" $MATH_PACK_BASE   "MATH"]\
      [list   "FIFO_MEM"  $FIFO_MEM_BASE    "FULL"]\
      [list   "CNT"       $CNT_BASE         "FULL"]]

   set MOD "$MOD $ASYNC_ORD_BASE/fifo_async_ord_ent.vhd"
   set MOD "$MOD $ASYNC_ORD_BASE/fifo_async_ord.vhd"
}
