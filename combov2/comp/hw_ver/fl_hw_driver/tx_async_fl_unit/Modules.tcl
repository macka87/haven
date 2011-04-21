# Modules.tcl
# Copyright (C) 2011
# Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
#set FL_BASE             "$COMP_BASE/fl_tools"
set BASE_BASE           "$COMP_BASE/base"
#set FL_FIFO_BASE        "$FL_BASE/storage/fifo"

set FIFO_BASE           "$COMP_BASE/cdc_fifo"

#set PACKAGES "$PACKAGES $FL_BASE/pkg/fl_pkg.vhd"

# components
set COMPONENTS [list \
   [ list "PKG_MATH"       $BASE_BASE/pkg       "MATH"] \
   [ list "CDC_FIFO"    $FIFO_BASE        "FULL"] \
]

# FrameLink Adder of NetCOPE Header 
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/tx_async_fl_unit.vhd"
}
