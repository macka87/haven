# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE        "$ENTITY_BASE/../../.."
set COMP_BASE            "$FIRMWARE_BASE/comp"
set SIZE_PROC_COVER_BASE "$ENTITY_BASE/size_proc_cover"

set MOD         "$MOD $ENTITY_BASE/fl_adapter.vhd"

# components
set COMPONENTS [list \
   [ list "SIZE_PROC_COVER"       $SIZE_PROC_COVER_BASE   "FULL"] \
]
