# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE       "$ENTITY_BASE/../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$COMP_BASE/base"

set MOD "$MOD $ENTITY_BASE/output_reg.vhd"
set MOD "$MOD $ENTITY_BASE/impulse_counter.vhd"
set MOD "$MOD $ENTITY_BASE/tx_delay_proc_unit.vhd"
