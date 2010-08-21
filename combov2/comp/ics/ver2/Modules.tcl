# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2008 CESNET
# Author: Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
  set COMP_BASE            "$ENTITY_BASE/../.."
  set SV_FL_TOOLS_VER_BASE "$COMP_BASE/fl_tools/ver"
  set ETH1G4_BASE          "$ENTITY_BASE/../../../cards/combov2/netcope/eth-1G4"
#  set DMA_MOD_BASE         "$COMP_BASE/proc/dma_mod"
  set DMA_MOD_BASE         "$COMP_BASE/ics/buffers/top"
  set LB_ROOT              "$COMP_BASE/ics/local_bus/comp/lb_root"
  set IB_SWITCH            "$COMP_BASE/ics/internal_bus/comp/ib_switch"
 
  set PACKAGES      "$PACKAGES $COMP_BASE/ics/internal_bus/pkg/ib_pkg.vhd"
  set PACKAGES      "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
  set PACKAGES      "$PACKAGES $COMP_BASE/fl_tools/pkg/fl_pkg.vhd"
  set PACKAGES      "$PACKAGES $ETH1G4_BASE/pkg/combov2_nc_const.vhd"
  set PACKAGES      "$PACKAGES $COMP_BASE/proc/dma_mod/dma_mod_4x64_rxtx/dma_4x16b_rxtx_const.vhd"
  
  set COMPONENTS [list \
      [ list "LB_ROOT"                 $LB_ROOT                "FULL"] \
      [ list "IB_SWITCH"               $IB_SWITCH              "FULL"] \
      [ list "SV_FL_TOOLS_VER_BASE"    $SV_FL_TOOLS_VER_BASE   "FULL"] \
      [ list "DMA_MOD_BASE"            $DMA_MOD_BASE           "NEWDMA"] \
  ]

  set MOD "$MOD $ENTITY_BASE/dma_module_wrapper.vhd"
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/sv_dmamodule_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"  
} elseif { $ARCHGRP == "GENERIC" } {
  set COMP_BASE            "$ENTITY_BASE/../.."
  set SV_FL_TOOLS_VER_BASE "$COMP_BASE/fl_tools/ver"
  set ETH1G4_BASE          "$ENTITY_BASE/../../../cards/combov2/netcope/eth-1G4"
  set DMA_MOD_BASE         "$COMP_BASE/ics/dma_ctrl_generic/top"
  set LB_ROOT              "$COMP_BASE/ics/local_bus/comp/lb_root"
  set IB_SWITCH            "$COMP_BASE/ics/internal_bus/comp/ib_switch"

  global DMA_CONST_FILE
  set DMA_CONST_FILE [eval pwd]/$COMP_BASE/proc/dma_mod/dma_mod_4x64_rxtx_gen/dma_4x16b_rxtx_gen_const.vhd
 
  set PACKAGES      "$PACKAGES $COMP_BASE/ics/internal_bus/pkg/ib_pkg.vhd"
  set PACKAGES      "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
  set PACKAGES      "$PACKAGES $COMP_BASE/fl_tools/pkg/fl_pkg.vhd"
  set PACKAGES      "$PACKAGES $ETH1G4_BASE/pkg/combov2_nc_const.vhd"
  
  set COMPONENTS [list \
      [ list "LB_ROOT"                 $LB_ROOT                "FULL"] \
      [ list "IB_SWITCH"               $IB_SWITCH              "FULL"] \
      [ list "SV_FL_TOOLS_VER_BASE"    $SV_FL_TOOLS_VER_BASE   "FULL"] \
      [ list "DMA_MOD_BASE"            $DMA_MOD_BASE           "FULL"] \
  ]

  set MOD "$MOD $ENTITY_BASE/dma_module_gen_wrapper.vhd"
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/sv_dmamodule_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"  
}

