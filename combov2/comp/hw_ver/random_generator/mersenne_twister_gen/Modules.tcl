# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

# Set paths
set COMP_BASE              "$ENTITY_BASE/../../.."
set HW_VER_BASE            "$COMP_BASE/hw_ver"

# Source files
set MOD "$MOD $ENTITY_BASE/tinymt32.vhd"
set MOD "$MOD $ENTITY_BASE/tinymt32_gen.vhd"
