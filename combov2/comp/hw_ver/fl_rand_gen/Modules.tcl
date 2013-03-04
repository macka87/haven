# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE        "$ENTITY_BASE/../../.."
set COMP_BASE            "$FIRMWARE_BASE/comp"
set HW_VER_BASE          "$COMP_BASE/hw_ver"
set RAND_GEN_BASE        "$HW_VER_BASE/random_generator"
set FL_ADAPTER_BASE      "$HW_VER_BASE/fl_adapter"
set MI_SPLITTER_BASE     "$COMP_BASE/gics/mi_bus/mi_splitter_plus"

set MOD         "$MOD $ENTITY_BASE/fl_rand_gen.vhd"

# components
set COMPONENTS [list \
   [ list "RAND_GEN"         $RAND_GEN_BASE     "FULL"] \
   [ list "FL_ADAPTER"       $FL_ADAPTER_BASE   "FULL"] \
   [ list "MI_SPLITTER"      $MI_SPLITTER_BASE  "FULL"] \
]
