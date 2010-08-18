# Modules.tcl: Modules.tcl script to compile DMA help components 
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

   set COMP_BASE     "$ENTITY_BASE/../../.."

   # Components
   set DPDISTMEM     "FULL"
   # dp_distmem is used in sync_flags component

   # Base directories
   set DPDISTMEM_BASE   "$COMP_BASE/base/mem/dp_distmem"

   set PACKAGES   "$PACKAGES $COMP_BASE/base/pkg/math_pack.vhd"

   set USED_COMPONENTS [list \
                        [list "DPDISTMEM" $DPDISTMEM_BASE $DPDISTMEM] \
                       ]

   set COMPONENTS "$USED_COMPONENTS $COMPONENTS"

   set MOD  "$MOD $COMP_BASE/ics/dma_ctrl/comp/dma2bm.vhd"
   set MOD  "$MOD $ENTITY_BASE/nport_or.vhd"
   set MOD  "$MOD $ENTITY_BASE/sync_flags.vhd"
#   set MOD  "$MOD $ENTITY_BASE/reg_array.vhd"
   set MOD  "$MOD $ENTITY_BASE/reg_array_be.vhd"
   set MOD  "$MOD $ENTITY_BASE/reg_array_sp_be.vhd"

} else {
   error "$ENTITY_MODFILE: Unsupported ARCHGRP: $ARCHGRP" "" "1"
}
