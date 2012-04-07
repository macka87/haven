# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"
set WAIT_BASE           "$COMP_BASE/hw_ver/wait_unit"

# components
set COMPONENTS [list \
   [ list "PKG_MATH"    $BASE_BASE/pkg    "MATH"] \
   [ list "WAIT_UNIT"   $WAIT_BASE        "FULL"] \
]

# FrameLink hardware driver
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/fl_driver_ctrl.vhd"
}
