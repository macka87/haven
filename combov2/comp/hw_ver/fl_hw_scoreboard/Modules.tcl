# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../.."
set FL_FIFO_BASE           "$COMP_BASE/fl_tools/storage/fifo"

# Source files
set MOD "$MOD $ENTITY_BASE/scoreboard_sender.vhd"
set MOD "$MOD $ENTITY_BASE/scoreboard_checker.vhd"
set MOD "$MOD $ENTITY_BASE/fl_hw_scoreboard.vhd"

# Componentss
set COMPONENTS [list \
   [ list "FL_FIFO"        $FL_FIFO_BASE         "FULL"] \
]
