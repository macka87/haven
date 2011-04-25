# ------------------------------------------------------------------------------
# Project Name: HGEN Functional Verification
# File Name:    Modules.tcl    
# Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz>    
# Date:         24.4.2011
# ------------------------------------------------------------------------------


if { $ARCHGRP == "FULL" } {
  set SV_FL_BASE      "$ENTITY_BASE/../../sw_ver/framelink_package"
  set SV_BASIC_BASE   "$ENTITY_BASE/../../sw_ver/basic_ver_components_package"
  set SV_MI32_BASE    "$ENTITY_BASE/../../sw_ver/mi32_package"
  
  set COMPONENTS [list \
      [ list "SV_FL_BASE"     $SV_FL_BASE     "FULL"] \
      [ list "SV_BASIC_BASE"  $SV_BASIC_BASE  "FULL"] \
      [ list "SV_MI32_BASE"   $SV_MI32_BASE   "FULL"] \
  ]

  # verification files
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/sv_hgen_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"
}

