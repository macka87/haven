# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Viktor Pus <pus@liberouter.org>
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

# Source files for the component

set COMP_BASE       "$ENTITY_BASE/../../../.."
set CNTR_ARRAY_BASE "$ENTITY_BASE/comp/cntr_array"
set QUEUE_BRAM_BASE "$ENTITY_BASE/comp/queue_bram"
set ARBITER_BASE    "$ENTITY_BASE/comp/arbiter"
set DP_DISTMEM_BASE "$COMP_BASE/base/mem/dp_distmem"
set MUX_BASE        "$COMP_BASE/base/logic/mux"

if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/cb_root.vhd"
   set MOD "$MOD $ENTITY_BASE/cb_root_arch.vhd"
}

if { $ARCHGRP == "DEBUG" } {
   set MOD "$MOD $ENTITY_BASE/cb_root_debug.vhd"
   set MOD "$MOD $ENTITY_BASE/cb_root_debug_arch.vhd"
}

set PACKAGES "$PACKAGES $ENTITY_BASE/../../pkg/cb_pkg.vhd"

set COMPONENTS [list [list "CNTR_ARRAY"    $CNTR_ARRAY_BASE  "FULL" ] \
                     [list "QUEUE_BRAM"    $QUEUE_BRAM_BASE  "FULL" ] \
                     [list "ARBITER"       $ARBITER_BASE     "FULL" ] \
                     [list "DP_DISTMEM"    $DP_DISTMEM_BASE  "FULL" ] \
                     [list "MUX"           $MUX_BASE         "FULL" ] \
               ]
