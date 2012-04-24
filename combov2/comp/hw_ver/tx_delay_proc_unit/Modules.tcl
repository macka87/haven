# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"

set FIFO_BASE           "$COMP_BASE/cdc_fifo"

# components
set COMPONENTS [list \
   [ list "PKG_MATH"    $BASE_BASE/pkg    "MATH"] \
   [ list "CDC_FIFO"    $FIFO_BASE        "FULL"] \
]

# FrameLink Adder of NetCOPE Header 
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/tx_delay_proc_unit.vhd"
}
