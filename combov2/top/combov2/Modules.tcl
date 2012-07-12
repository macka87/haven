# Modules.tcl: Modules.tcl script to compile Combov2 design
# Copyright (C) 2008 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
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

global FIRMWARE_BASE 
set NETCOPE_BASE  "$FIRMWARE_BASE/cards/combov2/netcope/eth-10G2"
set COMP_BASE    "$FIRMWARE_BASE/comp"

# List of packages
set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/addr_space.vhd"
set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/combov2_core_const.vhd"
set PACKAGES "$PACKAGES $FIRMWARE_BASE/pkg/combov2_user_const.vhd"
set PACKAGES "$PACKAGES $NETCOPE_BASE/pkg/combov2_pkg.vhd"
set PACKAGES "$PACKAGES $NETCOPE_BASE/pkg/combov2_nc_const.vhd"
set PACKAGES "$PACKAGES $FIRMWARE_BASE/comp/base/fifo/fifo_layers/pkg/fifo_pkg.vhd"
set PACKAGES "$PACKAGES $FIRMWARE_BASE/comp/fl_tools/pkg/fl_pkg.vhd"


if { ![info exist ARCHGRP] } {
   if { [info exist env(MODS)] } {
      # Components from NetCOPE project
      if { [ string compare $env(MODS) "1" ] == 0} {
         # Translation from EDIFs and sources - MODS in Makefile set to 1
         set ARCHGRP "EDIF"
      } else {
         # Translation from sources
         set ARCHGRP "FULL"
      }
   } else {
      puts "WARNING: Neither ARCHGRP nor MODS specified"
      set ARCHGRP "EDIF"
   }
}
source $NETCOPE_BASE/Modules.tcl

global DMA_IFC_COUNT
set DMA_IFC_COUNT 2
set DMA_MOD "2x64b_rxtx"

# Components
set PACODAG       "FULL"
set WATCH         "FULL"
set MI_SPLITTER   "FULL"
set IB            "FULL"
set IB_ASYNC      "FULL"
set MI_ASYNC      "FULL"
set TRANSFORMER   "FULL"
set SPLITTER      "FULL"
set NETWORK_MOD   "10G2_64"
set TS_ASYNC      "FULL"
set STAT          "FULL"

# There are several ARCHGRPs for the Verification Engine, see
# comp/verification_engine/Modules.tcl
#set VER_ENGINE    "CORE"
#set VER_ENGINE    "HW_GEN"
#set VER_ENGINE    "HW_GEN_CORE"
set VER_ENGINE    "HW_FULL"

# Base directories
set PACODAG_BASE        "$COMP_BASE/pacodag"
set WATCH_BASE          "$COMP_BASE/fl_tools/debug/watch"
set MI_SPLITTER_BASE    "$COMP_BASE/gics/mi_bus/mi_splitter"
set IB_BASE             "$COMP_BASE/gics/internal_bus" 
set IB_ASYNC_BASE       "$COMP_BASE/ics/internal_bus/comp/ib_async"
set MI_ASYNC_BASE       "$COMP_BASE/ics/local_bus/comp/lb_endpoint/comp/mi32_async"
set TRANSFORMER_BASE    "$COMP_BASE/fl_tools/flow/transformer"
set SPLITTER_BASE       "$COMP_BASE/fl_tools/flow/splitter"
set NETWORK_MOD_BASE    "$NETCOPE_BASE/comp/network_mod" 
set DMA_MOD_BASE        "$COMP_BASE/proc/dma_mod/dma_mod_$DMA_MOD" 
set TS_ASYNC_BASE       "$COMP_BASE/tsu/tsu_async"
set STAT_BASE           "$COMP_BASE/fl_tools/debug/stat"
set VER_ENGINE_BASE     "$COMP_BASE/verification_engine"

# List of instances
set PACODAG_INST     [list [list "PACODAG_I"             "FULL"]]
set WATCH_INST       [list [list "FL_WATCH*_I"           "FULL"]]
set MI_SPLITTER_INST [list [list "MI_SPLITTER_I"         "FULL"]]
set IB_INST          [list [list "IB*_I"                 "FULL"]]
set IB_ASYNC_INST    [list [list "IB_ASFIFO*"            "FULL"]]
set MI_ASYNC_INST    [list [list "MI_ASYNC*"             "FULL"]] 
set TRANSFORMER_INST [list [list "FL_TRANSFORMER_I"      "FULL"]]
set SPLITTER_INST    [list [list "FL_SPLITTER_I"         "FULL"]]
set NETWORK_MOD_INST [list [list "NETWORK_MOD*_I"        "FULL"]] 
set DMA_MOD_INST     [list [list "DMA_MOD*_I"            "FULL"]] 
set TS_ASYNC_INST    [list [list "TS_ASYNC_UNIT_I"       "FULL"]]
set STAT_INST        [list [list "STAT_I"                "FULL"]]
set VER_ENGINE_INST  [list [list "VERIFICATION_ENGINE_I" "FULL"]]

# List of components
if { $ARCHGRP == "FULL" } {
   set COMPONENTS [concat $COMPONENTS [list \
      [list "PACODAG"             $PACODAG_BASE     $PACODAG     $PACODAG_INST     ] \
      [list "WATCH"               $WATCH_BASE       $WATCH       $WATCH_INST       ] \
      [list "MI_SPLITTER"         $MI_SPLITTER_BASE $MI_SPLITTER $MI_SPLITTER_INST ] \
      [list "IB"                  $IB_BASE          $IB          $IB_INST          ] \
      [list "IB_ASYNC"            $IB_ASYNC_BASE    $IB_ASYNC    $IB_ASYNC_INST    ] \
      [list "MI_ASYNC"            $MI_ASYNC_BASE    $MI_ASYNC    $MI_ASYNC_INST    ] \
      [list "TS_ASYNC"            $TS_ASYNC_BASE    $TS_ASYNC    $TS_ASYNC_INST    ] \
      [list "FL_TRANSFORMER"      $TRANSFORMER_BASE $TRANSFORMER $TRANSFORMER_INST ] \
      [list "FL_SPLITTER"         $SPLITTER_BASE    $SPLITTER    $SPLITTER_INST    ] \
      [list "NETWORK_MOD"         $NETWORK_MOD_BASE $NETWORK_MOD $NETWORK_MOD_INST ] \
      [list "DMA_MOD"             $DMA_MOD_BASE     $DMA_MOD     $DMA_MOD_INST     ] \
      [list "STAT"                $STAT_BASE        $STAT        $STAT_INST        ] \
      [list "VERIFICATION_ENGINE" $VER_ENGINE_BASE  $VER_ENGINE  $VER_ENGINE_INST    ] \
   ]]
}

if { $ARCHGRP == "EDIF" } {
   set COMPONENTS [concat $COMPONENTS [list \
      [list "PACODAG"     $PACODAG_BASE     $PACODAG     $PACODAG_INST     ] \
      [list "MI_SPLITTER" $MI_SPLITTER_BASE $MI_SPLITTER $MI_SPLITTER_INST ] \
      [list "IB"          $IB_BASE          $IB          $IB_INST          ] \
      [list "IB_ASYNC"    $IB_ASYNC_BASE    $IB_ASYNC    $IB_ASYNC_INST    ] \
      [list "MI_ASYNC"    $MI_ASYNC_BASE    $MI_ASYNC    $MI_ASYNC_INST    ] \
      [list "FL_TRANSFORMER" $TRANSFORMER_BASE $TRANSFORMER $TRANSFORMER_INST ] \
      [list "WATCH"       $WATCH_BASE       $WATCH       $WATCH_INST       ] \
      [list "STAT"        $STAT_BASE        $STAT        $STAT_INST        ] \
      [list "VERIFICATION_ENGINE" $VER_ENGINE_BASE  $VER_ENGINE  $VER_ENGINE_INST    ] \
   ]]
}


set MOD "$MOD $FIRMWARE_BASE/top/combov2/application_ent.vhd"
set MOD "$MOD $FIRMWARE_BASE/top/combov2/application.vhd"
set MOD "$MOD $FIRMWARE_BASE/top/combov2/combov2_core.vhd"

# For loopback, set INBANDFCS in ../../pkg/combov2_user_const.vhd to false!

