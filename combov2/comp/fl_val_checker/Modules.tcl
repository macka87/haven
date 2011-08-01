# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/.."
set BASE_BASE              "$COMP_BASE/base"

# Source files
set MOD "$MOD $ENTITY_BASE/fl_val_checker.vhd"

 Componentss
set COMPONENTS [list \
   [ list "PKG_MATH"       $BASE_BASE/pkg       "MATH"] \
]
