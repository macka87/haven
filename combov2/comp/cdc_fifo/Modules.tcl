# Modules.tcl: Local include Modules tcl script
# Author: Ondrej Lengal <ilengal@fit.vutbr.cz>
#
# $Id$
#

set MOD "$MOD $ENTITY_BASE/xilinx_fifos/asfifo_lut_1.vhd"
set MOD "$MOD $ENTITY_BASE/xilinx_fifos/asfifo_lut_8.vhd"
set MOD "$MOD $ENTITY_BASE/xilinx_fifos/asfifo_lut_71.vhd"

# Source files
set MOD "$MOD $ENTITY_BASE/cdc_fifo.vhd"
