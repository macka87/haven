# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <lengal@liberouter.org>
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

set FL_FRAME_METER_BASE    "$FL_BASE/misc/frame_meter"
set FL_SHORTENER_BASE      "$FL_BASE/edit/shortener"
set FL_FIRST_INSERT_BASE   "$FL_BASE/edit/first_insert"
set FL_ASFIFO_BASE         "$FL_BASE/storage/asfifo"
set CLOCK_GATE_BASE        "$COMP_BASE/clock_gate"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/verification_core.vhd"

# Componentss
set COMPONENTS [list \
   [ list "FL_FRAME_METER"     $FL_FRAME_METER_BASE      "FULL"] \
   [ list "FL_SHORTENER"       $FL_SHORTENER_BASE        "FULL"] \
   [ list "FL_FIRST_INSERT"    $FL_FIRST_INSERT_BASE     "FULL"] \
   [ list "FL_ASFIFO"          $FL_ASFIFO_BASE           "FULL"] \
   [ list "CLOCK_GATE"         $CLOCK_GATE_BASE          "FULL"] \
]
