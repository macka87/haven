# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2008 CESNET
# Author: Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
#set FL_DEC_BASE "$COMP_BASE/fl_tools/misc/decoder"
set FSM_TRANSMIT_BASE "$ENTITY_BASE/comp/fsm_transmit"
set FSM_MAIN_BASE     "$ENTITY_BASE/comp/fsm_main"
set FSM_VALID_BASE    "$ENTITY_BASE/comp/fsm_valid"
set CUT_DATA_BASE     "$ENTITY_BASE/comp/cut_data"
set REORDER_BASE      "$ENTITY_BASE/comp/reorder"


# Source files for all architectures
set MOD "$MOD $ENTITY_BASE/cutter_ent.vhd"



# Full architecture
if { $ARCHGRP == "FULL" } {

		# packages
		set PACKAGES "$PKG_BASE/math_pack.vhd"
		
		# components
		set COMPONENTS [list \
    		[list "FSM_TRANSMIT"    $FSM_TRANSMIT_BASE   "FULL"]     \
    		[list "FSM_MAIN"        $FSM_MAIN_BASE       "FULL"]     \
    		[list "FSM_VALID"       $FSM_VALID_BASE      "FULL"]     \
    		[list "CUT_DATA"        $CUT_DATA_BASE       "FULL"]     \
    		[list "REORDER"         $REORDER_BASE        "FULL"]     \
		]

		# mods
    set MOD "$MOD $ENTITY_BASE/cutter.vhd"
    
}
