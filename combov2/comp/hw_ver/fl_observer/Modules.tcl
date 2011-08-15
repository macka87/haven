# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../.."
set HW_VER_BASE            "$COMP_BASE/hw_ver"
set SIGNAL_OBSERVER_BASE   "$HW_VER_BASE/signal_observer"

# Source files
set MOD "$MOD $ENTITY_BASE/fl_observer.vhd"

# Componentss
set COMPONENTS [list \
   [ list "SIGNAL_OBSERVER"  $SIGNAL_OBSERVER_BASE        "FULL"] \
]
