# Modules.tcl
# Copyright (C) 2008 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
#         Pecenka  Tomas <pecenka  AT liberouter.org>
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

set COMP_BASE     "$ENTITY_BASE/../.." 
set FL_BASE       "$COMP_BASE/fl_tools" 
 
# Modules variable
set ASFIFO_BRAM "FULL"
set ASFIFO_BRAM_RELEASE "FULL"
set AURORA     "FULL" 
set SWITCH     "FULL" 
set BINDER     "FULL" 
set STAMPER    "FULL" 
set TRANSFORMER "FULL" 
set FIFO       "FULL" 

#Base directories
set ASFIFO_BRAM_BASE   "$COMP_BASE/base/fifo/asfifo_bram"
set AURORA_BASE  "$COMP_BASE/external/ip_cores/aurora"
set SWITCH_BASE  "$FL_BASE/flow/switch"
set BINDER_BASE  "$FL_BASE/flow/binder"
set STAMPER_BASE  "$FL_BASE/edit/stamper"
set TRANSFORMER_BASE  "$FL_BASE/flow/transformer"
set FIFO_BASE     "$FL_BASE/storage/fifo"

# List of packages
set PACKAGES "$FL_BASE/pkg/fl_pkg.vhd"

# Lists of instantces
set ASFIFO_BRAM_INST       [list [list "ASFIFO_BRAM_U"      "FULL"]]
set ASFIFO_BRAM_RELEASE_INST       [list [list "ASFIFO_BRAM_RELEASE_U"     "FULL"]]
set AURORA_INST            [list [list "RIO_AURORA_MODULE_U"    "FULL"]]
set SWITCH_INST            [list [list "FL_SWITCH_I"        "FULL"]]
set BINDER_INST            [list [list "FL_BINDER_I"        "FULL"]]
set STAMPER_INST           [list [list "FL_STAMPER*_I"      "FULL"]]
set TRANSFORMER_INST       [list [list "FL_TRANSFORMER*_I"  "FULL"]]
set FIFO_INST              [list [list "FL_FIFO*_I"         "FULL"]]

# List of components
if { $ARCHGRP == "FULL" } { 
set COMPONENTS [list \
    [list "ASFIFO_BRAM"	   $ASFIFO_BRAM_BASE  	$ASFIFO_BRAM  	$ASFIFO_BRAM_INST]  \
    [list "ASFIFO_BRAM_RELEASE"	$ASFIFO_BRAM_BASE  	$ASFIFO_BRAM_RELEASE  	$ASFIFO_BRAM_RELEASE_INST]  \
    [list "AURORA"         $AURORA_BASE         $AURORA         $AURORA_INST] \
    [list "FL_SWITCH"      $SWITCH_BASE         $SWITCH         $SWITCH_INST] \
    [list "FL_BINDER"      $BINDER_BASE         $BINDER         $BINDER_INST] \
    [list "FL_STAMPER"     $STAMPER_BASE        $STAMPER        $STAMPER_INST] \
    [list "FL_TRANSFORMER" $TRANSFORMER_BASE    $TRANSFORMER    $TRANSFORMER_INST] \
    [list "FL_FIFO"        $FIFO_BASE           $FIFO           $FIFO_INST] \
  ]

# Source files for implemented component
   set MOD "$MOD $ENTITY_BASE/comp/transmitter.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/buf_ctrl_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/receiver.vhd"
   set MOD "$MOD $ENTITY_BASE/../comp/sof_eof_generator.vhd"
   set MOD "$MOD $ENTITY_BASE/aurfc_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/aurfc.vhd"
#   set MOD "$MOD $ENTITY_BASE/synth/top_level.vhd"
}

# Source file for empty component - empty architecture 
if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/aurfc_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/aurfc_empty.vhd"
}
   set MOD "$MOD $ENTITY_BASE/top/aurfc_fl64.vhd"
   set MOD "$MOD $ENTITY_BASE/top/aurfc_4xfl16.vhd"
