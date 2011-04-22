# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../.."
set HW_VER_BASE            "$COMP_BASE/hw_ver"
set CDC_FIFO_BASE          "$COMP_BASE/cdc_fifo"

set FL_DRIVER_CTRL_BASE    "$ENTITY_BASE/fl_driver_ctrl"
set TX_ASYNC_FL_UNIT_BASE  "$ENTITY_BASE/tx_async_fl_unit"


# Source files
set MOD "$MOD $ENTITY_BASE/fl_hw_driver.vhd"

# Componentss
set COMPONENTS [list \
   [ list "CDC_FIFO"           $CDC_FIFO_BASE            "FULL"] \
   [ list "FL_DRIVER_CTRL"     $FL_DRIVER_CTRL_BASE      "FULL"] \
   [ list "TX_ASYNC_FL_UNIT"   $TX_ASYNC_FL_UNIT_BASE    "FULL"] \
]
