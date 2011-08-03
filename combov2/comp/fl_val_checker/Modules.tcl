# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set BASE_BASE              "$COMP_BASE/base"
set CDC_FIFO_BASE          "$COMP_BASE/cdc_fifo"

# Source files
set MOD "$MOD $ENTITY_BASE/fl_val_guard.vhd"
set MOD "$MOD $ENTITY_BASE/fl_val_checker.vhd"

# Components
set COMPONENTS [list \
   [ list "CDC_FIFO"       $CDC_FIFO_BASE        "FULL"] \
   [ list "PKG_MATH"       $BASE_BASE/pkg       "MATH"] \
]
