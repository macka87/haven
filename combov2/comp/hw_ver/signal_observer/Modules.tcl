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
set REARRANGER_BASE        "$HW_VER_BASE/rearranger"
set PACKETIZER_BASE        "$HW_VER_BASE/packetizer"
set FRAME_SENDER_BASE      "$HW_VER_BASE/frame_sender"

# Source files
set MOD "$MOD $ENTITY_BASE/signal_observer.vhd"

# Componentss
set COMPONENTS [list \
   [ list "CDC_FIFO"       $CDC_FIFO_BASE        "FULL"] \
   [ list "FL_FIFO"        $FL_FIFO_BASE         "FULL"] \
   [ list "REARRANGER"     $REARRANGER_BASE      "FULL"] \
   [ list "PACKETIZER"     $PACKETIZER_BASE      "FULL"] \
   [ list "FRAME_SENDER"   $FRAME_SENDER_BASE    "FULL"] \
]
