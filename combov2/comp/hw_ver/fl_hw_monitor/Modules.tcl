# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../.."
set HW_VER_BASE            "$COMP_BASE/hw_ver"
set CDC_FIFO_BASE          "$COMP_BASE/cdc_fifo"
set LFSR_PRNG_BASE         "$HW_VER_BASE/lfsr_prng"
set FL_TRANSFORMER_BASE    "$COMP_BASE/fl_tools/flow/transformer"

# Source files
set MOD "$MOD $ENTITY_BASE/fl_hw_monitor.vhd"

# Componentss
set COMPONENTS [list \
   [ list "CDC_FIFO"       $CDC_FIFO_BASE        "FULL"] \
   [ list "LFSR_PRNG"      $LFSR_PRNG_BASE       "FULL"] \
   [ list "FL_TRANSFORMER" $FL_TRANSFORMER_BASE  "FULL"] \
]
