# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set DATA_PROC_BASE      "$ENTITY_BASE/data_proc_unit"
set DATA_SIZE_PROC_BASE "$ENTITY_BASE/data_size_proc_unit"
set REG_PROC_BASE       "$ENTITY_BASE/reg_proc_unit"
set ORD_FIFO_BASE       "$COMP_BASE/base/fifo/fifo_layers/fifo_core/sync_ord" 

set MOD         "$MOD $ENTITY_BASE/fl_adapter.vhd"

# components
set COMPONENTS [list \
   [ list "DATA_PROC_UNIT"        $DATA_PROC_BASE         "FULL"] \
   [ list "DATA_SIZE_PROC_UNIT"   $DATA_SIZE_PROC_BASE    "FULL"] \
   [ list "REG_PROC_UNIT"         $REG_PROC_BASE          "FULL"] \
   [ list "ORD_FIFO_UNIT"         $ORD_FIFO_BASE          "FULL"] \
]
