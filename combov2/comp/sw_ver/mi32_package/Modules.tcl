# ------------------------------------------------------------------------------
# Project Name: MI32 Components 
# File Name:    Modules.tcl    
# Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz>    
# Date:         24.4.2011
# ------------------------------------------------------------------------------


if { $ARCHGRP == "FULL" } {
  set SV_BASIC_BASE    "$ENTITY_BASE/../basic_ver_components_package"

  set COMPONENTS [list \
      [ list "SV_BASIC_BASE"   $SV_BASIC_BASE    "FULL"] \
   ]

  set MOD "$MOD $ENTITY_BASE/sv_mi32_pkg.sv"
}

