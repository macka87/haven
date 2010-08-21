# Modules.tcl: Modules.tcl script to compile Combov2 design
# Copyright (C) 2008 CESNET
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

global FIRMWARE_BASE 
set COMP_BASE     "$FIRMWARE_BASE/comp"
set NETCOPE_BASE  "$FIRMWARE_BASE/cards/combov2/netcope/eth-10G2"

if { $ARCHGRP == "CORE" || $ARCHGRP == "FULL" } {
   # Packages
   set PACKAGES   "$PACKAGES $COMP_BASE/gics/internal_bus/pkg/ib_ifc_pkg.vhd"
   set PACKAGES   "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
   set PACKAGES   "$PACKAGES $COMP_BASE/fl_tools/pkg/fl_pkg.vhd"
   set PACKAGES   "$PACKAGES $COMP_BASE/base/pkg/math_pack.vhd"
   set PACKAGES   "$PACKAGES $COMP_BASE/base/fifo/fifo_layers/pkg/fifo_pkg.vhd"

   set PACKAGES   "$PACKAGES $NETCOPE_BASE/pkg/combov2_nc_const.vhd"
   set PACKAGES   "$PACKAGES $FIRMWARE_BASE/pkg/combov2_user_const.vhd"
   set PACKAGES   "$PACKAGES $NETCOPE_BASE/pkg/combov2_pkg.vhd"
}

#if {[info exists env(FPGA_TYPE)]} {
   #if {$env(FPGA_TYPE) == "xc5vfx100t" } {
      #puts "Setting XAUI core for FXT cards (GTX)."
      #set XAUI          "GTX"
      #set XAUI_INST      [list [list "XAUI_CORE*_I"       "GTX"]]
   #} else {
      #puts "Setting XAUI core for LXT cards (GTP)."
      #set XAUI          "FULL"
      #set XAUI_INST      [list [list "XAUI_CORE*_I"       "FULL"]]
   #}
#} else {
   #puts "Setting default XAUI core for LXT cards (GTP)."
   #set XAUI          "FULL"
   #set XAUI_INST      [list [list "XAUI_CORE*_I"       "FULL"]]
#}

# Components
set ID            "FULL"
set IB        	   "FULL"
set EMPTY     	   "FULL"
set PCIE          "FULL"
#set XAUI          "GTX"
set MDIO          "MI32"
set CLKGEN        "FULL"
set NETCOPE_ICS   "FULL"
set TS            "FULL"

# Base directories
set ID_BASE       "$COMP_BASE/base/misc/id32" 
set IB_BASE       "$COMP_BASE/gics/internal_bus"
set EMPTY_BASE    "$COMP_BASE/empty"
set CLKGEN_BASE   "$COMP_BASE/base/misc/clk_gen"
set PCIE_BASE     "$FIRMWARE_BASE/cards/combov2/chips/comp/pci"
set XAUI_BASE     "$NETCOPE_BASE/comp/xaui"
set MDIO_BASE     "$COMP_BASE/nic/xgmii/mdio"
set NETCOPE_ICS_BASE "$NETCOPE_BASE/comp/netcope_ics"
set TS_BASE       "$COMP_BASE/tsu/tsu_cv2"

# List of instances
set ID_INST        [list [list "ID32_I"             "FULL"]]
set IB_INST        [list [list "IB*_I"              "FULL"]]
set CLKGEN_INST    [list [list "clkgen_i"           "FULL"]]
set EMPTY_INST     [list [list "RIO_EMPTY?"         "FULL"]]
set PCIE_INST      [list [list "PCIE2IB_TOP_I"      "FULL"]]
#set XAUI_INST      [list [list "XAUI_CORE*_I"       "GTX"]]
set MDIO_INST      [list [list "MDIO_I"             "MI32"]]
set NETCOPE_ICS_INST [list [list "netcope_i"        "FULL"]]
set TS_INST        [list [list "TS_UNIT_I"          "FULL"]]

if {[info exist COMPONENTS]} {
   set COMPONENTS ""
}

## List of components for various architectures:

# CORE - Only combov2_netcope part, VHDL sources
if { $ARCHGRP == "CORE" } {
   set COMPONENTS [concat $COMPONENTS [list \
      [list "ID"           $ID_BASE      $ID       $ID_INST   ] \
      [list "MDIO"         $MDIO_BASE    $MDIO     $MDIO_INST ] \
      [list "CLKGEN"       $CLKGEN_BASE  $CLKGEN   $CLKGEN_INST ] \
      [list "NETCOPE_ICS"  $NETCOPE_ICS_BASE $NETCOPE_ICS $NETCOPE_ICS_INST ] \
      [list "TS"           $TS_BASE      $TS       $TS_INST ] \
   ]]
}

# FULL - Full chip, all VHDL sources
if { $ARCHGRP == "FULL" } {
   set COMPONENTS [concat $COMPONENTS [list \
      [list "ID"           $ID_BASE      $ID       $ID_INST   ] \
      [list "MDIO"         $MDIO_BASE    $MDIO     $MDIO_INST ] \
      [list "CLKGEN"       $CLKGEN_BASE  $CLKGEN   $CLKGEN_INST ] \
      [list "NETCOPE_ICS"  $NETCOPE_ICS_BASE $NETCOPE_ICS $NETCOPE_ICS_INST ] \
      [list "PCIE"         $PCIE_BASE    $PCIE     $PCIE_INST ] \
      [list "TS"           $TS_BASE      $TS       $TS_INST ] \
   ]]

}
#      [list "XAUI"         $XAUI_BASE    $XAUI     $XAUI_INST ] \

# EDIF - Full chip, EDIFs and VHDL sources
if { $ARCHGRP == "EDIF" } {
   set COMPONENTS [concat $COMPONENTS [list \
      [list "ID"           $ID_BASE      $ID       $ID_INST   ] \
      [list "CLKGEN"       $CLKGEN_BASE  $CLKGEN   $CLKGEN_INST ] \
   ]]
      #[list "XAUI"         $XAUI_BASE    $XAUI     $XAUI_INST ] \

}

if { $ARCHGRP == "CORE" || $ARCHGRP == "FULL" || $ARCHGRP == "EDIF" } {
   # COMBO core entity
   set MOD "$MOD $NETCOPE_BASE/combov2_core_ent.vhd"
   set MOD "$MOD $NETCOPE_BASE/combov2_netcope.vhd"
}
