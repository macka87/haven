# ------------------------------------------------------------------------------
# Project Name: NetCOPE Adder Functional Verification
# File Name:    Modules.tcl    
# Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz>    
# Date:         27.2.2011
# ------------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {
  
  # interface packages
  set SV_FL_BASE   "$ENTITY_BASE/framelink_package"
  
  set COMPONENTS [list \
      [ list "SV_FL_BASE"  $SV_FL_BASE  "FULL"] \
  ]
 
  # verification files
  set MOD "$MOD $ENTITY_BASE/tbench/test_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/dut.sv"
  set MOD "$MOD $ENTITY_BASE/tbench/test.sv"  
}