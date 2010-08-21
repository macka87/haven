# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Kastil Jan <xkasti00@stud.fit.vutbr.cz>
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
#global VHDL_BASE
set FIRMWARE_BASE      "$ENTITY_BASE/../../../../../.."
set COMP_BASE          "$FIRMWARE_BASE/comp"
set MATH_PACK_BASE     "$COMP_BASE/base/pkg"

#set MATH_PACK_BASE "$VHDL_BASE/units/common/pkg"

if { $ARCHGRP == "FULL" } {
   set FIFO_MEM_BASE   "$COMP_BASE/base/fifo/fifo_layers/fifo_mem"
   set DP_BMEM_BASE    "$COMP_BASE/base/mem/dp_bmem"
   set DP_DISTMEM_BASE "$COMP_BASE/base/mem/dp_distmem"

   set ASYNC_BLOCK_BASE "$COMP_BASE/base/fifo/fifo_layers/fifo_core/async_block"
   set ASYNC_ORD_BASE  "$COMP_BASE/base/fifo/fifo_layers/fifo_core/async_ord"
   set CNT_BASE        "$COMP_BASE/base/logic/cnt"


   set DP_BMEM      "FULL"
   set DP_DISTMEM   "FULL"



# Source files for all components
   set PACKAGES  "$MATH_PACK_BASE/math_pack.vhd \ 
               $FIFO_MEM_BASE/../pkg/fifo_pkg.vhd"
	       
   set COMPONENTS [list\
      [list   "MATH_PACK" $MATH_PACK_BASE   "MATH"]\
      [list   "DP_BMEM"   $DP_BMEM_BASE     "FULL"]\
      [list   "DP_DISTMEM" $DP_DISTMEM_BASE "FULL"]\
      [list   "FIFO_MEM"   $FIFO_MEM_BASE   "FULL"]\
      [list "CNT"          $CNT_BASE        "FULL"]\
      [list "ASYNC_ORD"    $ASYNC_ORD_BASE  "FULL"]]


   set MOD "$MOD $ASYNC_BLOCK_BASE/fifo_async_blocka_ent.vhd"
   set MOD "$MOD $ASYNC_BLOCK_BASE/fifo_async_blocka.vhd"
}
