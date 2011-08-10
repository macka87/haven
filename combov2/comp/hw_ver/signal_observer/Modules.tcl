# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../.."
set HW_VER_BASE            "$COMP_BASE/hw_ver"
set CDC_FIFO_BASE          "$COMP_BASE/cdc_fifo"
set FL_BASE                "$COMP_BASE/fl_tools"
set FL_FIFO_BASE           "$FL_BASE/storage/fifo"


# Source files
set MOD "$MOD $ENTITY_BASE/signal_observer.vhd"

# Smart monitor
set MOD "$MOD $ENTITY_BASE/observer_packetizer.vhd"
set MOD "$MOD $ENTITY_BASE/frame_sender.vhd"

# Componentss
set COMPONENTS [list \
   [ list "CDC_FIFO"       $CDC_FIFO_BASE        "FULL"] \
   [ list "LFSR_PRNG"      $LFSR_PRNG_BASE       "FULL"] \
   [ list "FL_FIFO"        $FL_FIFO_BASE         "FULL"] \
]
