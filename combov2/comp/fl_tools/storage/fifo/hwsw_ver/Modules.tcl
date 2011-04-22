# ------------------------------------------------------------------------------
# Project Name: FIFO Functional Verification
# File Name:    Modules.tcl    
# Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz>    
# Date:         27.2.2011
# ------------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {
  
  # interface packages
  set SV_FL_BASE      "$ENTITY_BASE/../../../../sw_ver/framelink_package"
  set SV_BASIC_BASE   "$ENTITY_BASE/../../../../sw_ver/basic_ver_components_package"
  
  set COMPONENTS [list \
      [ list "SV_FL_BASE"     $SV_FL_BASE     "FULL"] \
      [ list "SV_BASIC_BASE"  $SV_BASIC_BASE  "FULL"] \
  ]
 
  # verification files
  set MOD "$MOD $ENTITY_BASE/tbench/sv_fl_fifo_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"  
}