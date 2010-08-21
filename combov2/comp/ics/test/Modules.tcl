# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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

global FIRMWARE_BASE

if { $ARCHGRP == "FULL" } {
 set ICS_BASE            "$FIRMWARE_BASE/comp/ics" 
 set ID_BASE             "$FIRMWARE_BASE/comp/base/misc/id32" 

 set IB_SWITCH_INST   [list [list "IB_SWITCH0_U"      "FULL"] \
                            [list "IB_SWITCH1_U"      "FULL"] \
                            [list "IB_SWITCH2_U"      "FULL"] \
                            [list "IB_SWITCH3_U"      "FULL"]]

 set IB_ENDPOINT_INST [list [list "IB_ENDPOINT0_U"    "FULL"] \
                            [list "IB_ENDPOINT1_U"    "FULL"] \
                            [list "IB_ENDPOINT2_U"    "FULL"] \
                            [list "IB_ENDPOINT3_U"    "FULL"]]

 set LB_ROOT_INST     [list [list "LB_ROOT_U"         "FULL"]]

 set LB_SWITCH_INST   [list [list "LB_SWITCH0_U"      "FULL"] \
                            [list "IB_SWITCH1_U"      "FULL"]]
 
 set LB_ENDPOINT_INST [list [list "LB_ENDPOINT0_U"    "FULL"] \
                            [list "LB_ENDPOINT1_U"    "FULL"] \
                            [list "LB_ENDPOINT2_U"    "FULL"] \
                            [list "LB_ENDPOINT3_U"    "FULL"] \
                            [list "LB_ENDPOINT4_U"    "FULL"] \
                            [list "LB_ENDPOINT5_U"    "FULL"] \
                            [list "LB_ENDPOINT6_U"    "FULL"]]

 set COMPONENTS [list \
     [list "IB_SWITCH"     $ICS_BASE/internal_bus/comp/ib_switch    "FULL"  $IB_SWITCH_INST   ] \
     [list "IB_ENDPOINT"   $ICS_BASE/internal_bus/comp/ib_endpoint  "FULL"  $IB_ENDPOINT_INST ] \
     [list "LB_ROOT"       $ICS_BASE/local_bus/comp/lb_root         "FULL"  $LB_ROOT_INST     ] \
     [list "LB_SWITCH"     $ICS_BASE/local_bus/comp/lb_switch       "FULL"  $LB_SWITCH_INST   ] \
     [list "LB_ENDPOINT"   $ICS_BASE/local_bus/comp/lb_endpoint     "FULL"  $LB_ENDPOINT_INST ] \
     [list "ID"            $ID_BASE                                 "FULL"  ] \
     [list "IBMEM"         $ICS_BASE/internal_bus/comp/ibmem        "FULL"  ] \
     [list "LBMEM"         $ICS_BASE/local_bus/comp/lbmem           "FULL"  ] \
     [list "LB2BM"         $ICS_BASE/local_bus/comp/lb2bm           "FULL"  ] \
  ]

  set MOD "$MOD $ENTITY_BASE/ics_core_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/ics_core.vhd"
  set MOD "$MOD $ENTITY_BASE/ics_test_app_pkg.vhd"
  set MOD "$MOD $ENTITY_BASE/ics_test_app.vhd"
  set MOD "$MOD $ENTITY_BASE/ics_core_mini.vhd"
  set MOD "$MOD $ENTITY_BASE/ics_test_app_mini.vhd"
}

