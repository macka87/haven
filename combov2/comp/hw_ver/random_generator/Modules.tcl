# Modules.tcl
# Copyright (C) 2012
# Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

# Set paths
set FIRMWARE_BASE        "$ENTITY_BASE/../../.."
set COMP_BASE            "$FIRMWARE_BASE/comp"
set MT_N_BASE            "$ENTITY_BASE/mersenne_twister_gen_n"

set MOD         "$MOD $ENTITY_BASE/rand_gen.vhd"

# components
set COMPONENTS [list \
   [ list "MT_N"       $MT_N_BASE   "FULL"] \
]
