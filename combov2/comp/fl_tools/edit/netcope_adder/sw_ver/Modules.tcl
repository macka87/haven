# ------------------------------------------------------------------------------
# Project Name: NetCOPE Adder Functional Verification
# File Name:    Modules.tcl    
# Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz>    
# Date:         27.2.2011
# ------------------------------------------------------------------------------

set FIRMWARE_BASE "$ENTITY_BASE/../../../../.."
set COMP_BASE     "$FIRMWARE_BASE/comp"
set SW_VER_BASE   "$COMP_BASE/sw_ver"

if { $ARCHGRP == "FULL" } {
  
  # interface packages
  set SV_FL_BASE      "$SW_VER_BASE/framelink_package"
  set SV_BASIC_BASE   "$SW_VER_BASE/basic_ver_components_package"
  
  set COMPONENTS [list \
      [ list "SV_FL_BASE"     $SV_FL_BASE     "FULL"] \
      [ list "SV_BASIC_BASE"  $SV_BASIC_BASE  "FULL"] \
  ]
 
  # verification files
  set MOD "$MOD $ENTITY_BASE/tbench/sv_netcope_adder_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"  
}
