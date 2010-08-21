# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
# Author: Martin Louda <sandin@liberouter.org>
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

set COMP_BASE   "$ENTITY_BASE/../../.."
set PKG_BASE    "$COMP_BASE/base/pkg"
set MUX_BASE    "$COMP_BASE/base/logic/mux"
set FL_BASE     "$COMP_BASE/fl_tools"

# Source files for all architectures
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/transformer_ent.vhd"

# Full architecture of FrameLink Transformer
if { $ARCHGRP == "FULL" } {
    set MOD "$MOD $ENTITY_BASE/transformer_down.vhd"
    set MOD "$MOD $ENTITY_BASE/transformer_up.vhd"
    set MOD "$MOD $ENTITY_BASE/transformer_down_8.vhd"
    set MOD "$MOD $ENTITY_BASE/transformer_up_8.vhd"    
    set MOD "$MOD $ENTITY_BASE/transformer.vhd"
}

# Empty architecture of FrameLink Transformer
if { $ARCHGRP == "EMPTY" } {
    set MOD "$MOD $ENTITY_BASE/transformer_empty.vhd"
}


# components
set COMPONENTS [list \
    [list "PKG_MATH"        $PKG_BASE       "MATH"]     \
    [list "GEN_MUX"         $MUX_BASE       "FULL"]     \
]

# covers
set MOD "$MOD $ENTITY_BASE/top/transformer_fl128_16.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl128_32.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl128_64.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl64_16.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl64_128.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl16_32.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl16_64.vhd"
set MOD "$MOD $ENTITY_BASE/top/transformer_fl32_16.vhd"
