# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set FL_BASE                "$COMP_BASE/fl_tools"

set FL_ADDER_BASE          "$FL_BASE/edit/netcope_adder"
set VER_CORE_BASE          "$COMP_BASE/verification_core"

# Source files
set MOD "$MOD $ENTITY_BASE/verification_engine_ent.vhd"
set MOD "$MOD $ENTITY_BASE/verification_engine.vhd"

# Componentss
set COMPONENTS [list \
   [ list "FL_ADDER"           $FL_ADDER_BASE         "FULL"] \
   [ list "VER_CORE"           $VER_CORE_BASE         "FULL"] \
]
