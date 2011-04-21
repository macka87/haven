# Modules.tcl
# Copyright (C) 2011
# Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"

# components
set COMPONENTS [list \
   [ list "PKG_MATH"    $BASE_BASE/pkg    "MATH"] \
]

# FrameLink Adder of NetCOPE Header 
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/fl_driver.vhd"
}
