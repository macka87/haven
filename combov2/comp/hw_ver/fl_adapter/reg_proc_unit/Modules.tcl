# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"
set GEN_PROC_BASE       "$ENTITY_BASE/gen_proc_unit"

set MOD         "$MOD $ENTITY_BASE/reg_proc_unit.vhd"

# components
set COMPONENTS [list \
   [ list "PKG_MATH"        $BASE_BASE/pkg    "MATH"] \
   [ list "GEN_PROC_UNIT"   $GEN_PROC_BASE    "FULL"] \
]
