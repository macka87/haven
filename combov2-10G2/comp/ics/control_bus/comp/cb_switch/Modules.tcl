# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
#         Patrik Beck <beck@liberouter.org>
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

# Source files for all components


if { $ARCHGRP == "FULL" } {
   set COMP_BASE     "$ENTITY_BASE/../../../.."
   
  set COMPONENTS [list \
    [ list "PKG"        "$COMP_BASE/base/pkg"           "MATH"] \
    [ list "RR_ARBITER" "$COMP_BASE/base/misc/rr_arbiter"    "FULL"] \
  ]
   
  set MOD "$MOD $ENTITY_BASE/../../pkg/cb_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/../../../internal_bus/comp/ib_switch/ib_shift_reg.vhd"
  set MOD "$MOD $ENTITY_BASE/cb_switch_in_fsm.vhd"
  set MOD "$MOD $ENTITY_BASE/cb_switch_mux.vhd"
  set MOD "$MOD $ENTITY_BASE/cb_switch_out_fsm.vhd"
  set MOD "$MOD $ENTITY_BASE/cb_switch.vhd"
  set MOD "$MOD $ENTITY_BASE/cb_switch_arch.vhd"
  set MOD "$MOD $ENTITY_BASE/top/cb_switch_2p.vhd"
  set MOD "$MOD $ENTITY_BASE/top/cb_switch_3p.vhd"
  set MOD "$MOD $ENTITY_BASE/top/cb_switch_4p.vhd"
  set MOD "$MOD $ENTITY_BASE/top/cb_switch_5p.vhd"
  set MOD "$MOD $ENTITY_BASE/top/cb_switch_6p.vhd"
  
}


