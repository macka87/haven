# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../.."
set HW_VER_BASE            "$COMP_BASE/hw_ver"
set MATH_PKG_BASE          "$COMP_BASE/base/pkg"
set CDC_FIFO_BASE          "$COMP_BASE/cdc_fifo"
set REARRANGER_BASE        "$HW_VER_BASE/rearranger"
set PACKETIZER_BASE        "$HW_VER_BASE/packetizer"


# Source files
set MOD "$MOD $ENTITY_BASE/toggle_cell.vhd"
set MOD "$MOD $ENTITY_BASE/toggle_cov_unit.vhd"

# Componentss
set COMPONENTS [list \
   [ list "PKG"            $MATH_PKG_BASE        "MATH"] \
   [ list "CDC_FIFO"       $CDC_FIFO_BASE        "FULL"] \
   [ list "REARRANGER"     $REARRANGER_BASE      "FULL"] \
   [ list "PACKETIZER"     $PACKETIZER_BASE      "FULL"] \
]
