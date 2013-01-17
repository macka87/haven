# ------------------------------------------------------------------------------
# Project Name: ALU Functional Verification
# File Name:    Modules.tcl 
# Description:  Definition of testbench environment. 
# Author:       Marcela Simkova <isimkova@fit.vutbr.cz>    
# Date:         22.3.2012
# ------------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {
  # interface packages
  set SV_BASIC_BASE   "$ENTITY_BASE/../../combov2/comp/sw_ver/basic_ver_components_package"
  
  set COMPONENTS [list \
      [ list "SV_BASIC_BASE"  $SV_BASIC_BASE  "FULL"] \
  ]
 
  # verification files
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/sv_alu_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"  
}

if { $ARCHGRP == "GENALG" } {
  # interface packages
  set SV_BASIC_BASE   "$ENTITY_BASE/../../combov2/comp/sw_ver/basic_ver_components_package"
  set SV_GA_BASE      "$ENTITY_BASE/../../combov2/comp/sw_ver/basic_ver_components_package/ga_components"
  
  set COMPONENTS [list \
      [ list "SV_BASIC_BASE"  $SV_BASIC_BASE  "FULL"] \
      [ list "SV_GA_BASE"     $SV_GA_BASE     "FULL"] \
  ]
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ga_test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/sv_ga_alu_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/ga_test.sv"  
}