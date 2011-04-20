# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

set FL_FIFO_BASE           "$FL_BASE/storage/fifo"
set FL_ASFIFO_BASE         "$FL_BASE/storage/asfifo"
set FL_ADDER_BASE          "$FL_BASE/edit/netcope_adder"
set CLOCK_GATE_BASE        "$COMP_BASE/clock_gate"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/verification_core.vhd"

# Componentss
set COMPONENTS [list \
   [ list "FL_FIFO"            $FL_FIFO_BASE             "FULL"] \
   [ list "FL_ASFIFO"          $FL_ASFIFO_BASE           "FULL"] \
   [ list "FL_ADDER"           $FL_ADDER_BASE            "FULL"] \
   [ list "CLOCK_GATE"         $CLOCK_GATE_BASE          "FULL"] \
]
