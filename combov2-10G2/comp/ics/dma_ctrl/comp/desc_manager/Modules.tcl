# Modules.tcl: Modules.tcl script
# Copyright (C) 2008 CESNET
# Author: Pavol Korcek <korcek@liberouter.org>
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


# Set paths
set COMP_BASE           "$ENTITY_BASE/../../../.."

set PACKAGES   "$PACKAGES $ENTITY_BASE/pkg/desc_man_pkg.vhd"

set MOD "$MOD $ENTITY_BASE/desc_we_logic_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/desc_flags.vhd"
set MOD "$MOD $ENTITY_BASE/desc_get_next_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/../bm2mem_ifc.vhd"
set MOD "$MOD $ENTITY_BASE/reg_array.vhd"
set MOD "$MOD $ENTITY_BASE/be_register.vhd"
set MOD "$MOD $ENTITY_BASE/desc_manager_bm.vhd"  
set MOD "$MOD $ENTITY_BASE/desc_manager.vhd"  
set MOD "$MOD $ENTITY_BASE/desc_manager_gcc.vhd"  


# components
set COMPONENTS [list \
    [ list "PKG_MATH"       $COMP_BASE/base/pkg              "MATH"] \
    [ list "MUX"            $COMP_BASE/base/logic/mux        "FULL"] \
    [ list "SPDISTMEM"      $COMP_BASE/base/mem/sp_distmem   "FULL"] \
    [ list "FIFO2NFIFO"     $COMP_BASE/base/buffers/top      "FULL"] \
]

