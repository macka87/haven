# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <lengal@liberouter.org>
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

set FL_FRAME_METER_BASE    "$FL_BASE/misc/frame_meter"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_core_ent.vhd"
set MOD "$MOD $ENTITY_BASE/verification_core.vhd"

# Componentss
set COMPONENTS [list \
   [ list "FL_FRAME_METER"     $FL_FRAME_METER_BASE      "FULL"] \
]
