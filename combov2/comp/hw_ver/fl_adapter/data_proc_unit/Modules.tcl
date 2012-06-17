# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"


# components
set COMPONENTS [list \
   [ list "PKG_MATH"              $BASE_BASE/pkg          "MATH"] \
]

if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/data_proc_unit.vhd"
}
