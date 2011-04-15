# ------------------------------------------------------------------------------
# Project Name: Basic Verification Environment Components 
# File Name:    Modules.tcl    
# Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz>    
# Date:         27.2.2011
# ------------------------------------------------------------------------------

if { $ARCHGRP == "FULL" } {
  set MOD "$MOD $ENTITY_BASE/dpi_input/dpi_input_wrapper_pkg.sv"
  #set MOD "$MOD $ENTITY_BASE/dpi_output/dpi_output_wrapper_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/sv_basic_comp_pkg.sv"
  set MOD "$MOD $ENTITY_BASE/math_pkg.sv"
}
