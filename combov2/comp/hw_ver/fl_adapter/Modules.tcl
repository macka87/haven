# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE        "$ENTITY_BASE/../../.."
set COMP_BASE            "$FIRMWARE_BASE/comp"
set SIZE_PROC_COVER_BASE "$ENTITY_BASE/size_proc_cover"
set DELAY_PROC_UNIT_BASE "$ENTITY_BASE/delay_proc_unit"
set DELAY_TRANS_BASE     "$ENTITY_BASE/delay_trans"

set MOD         "$MOD $ENTITY_BASE/fl_adapter.vhd"

# components
set COMPONENTS [list \
   [ list "SIZE_PROC_COVER"       $SIZE_PROC_COVER_BASE   "FULL"] \
   [ list "DELAY_PROC_UNIT"       $DELAY_PROC_UNIT_BASE   "FULL"] \
   [ list "DELAY_TRANSFORMER"     $DELAY_TRANS_BASE       "FULL"] \
]
