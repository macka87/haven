# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../.."
set MATH_PKG_BASE          "$COMP_BASE/base/pkg"

# Source files
set MOD "$MOD $ENTITY_BASE/frame_sender.vhd"

# Componentss
set COMPONENTS [list \
   [ list "MATH_PKG"        $MATH_PKG_BASE         "MATH"] \
]
