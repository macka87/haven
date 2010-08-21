# Modules.tcl: Design modules definition
# Copyright (C) 2009 CESNET
# Author: Stepan Friedl <friedl@liberouter.org>
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the OpenIPCore Hardware General Public
# License as published by the OpenIPCore Organization; either version
# 0.20-15092000 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# OpenIPCore Hardware General Public License for more details.
#
# You should have received a copy of the OpenIPCore Hardware Public
# License along with this program; if not, download it from
# OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
#
# $Id$
#

global FIRMWARE_BASE

# Base directories
set COMP_BASE   "$FIRMWARE_BASE/comp"
set IB_EP_BASE  "$COMP_BASE/ics/internal_bus/comp/ib_endpoint" 
set IB_BR_BASE  "$FIRMWARE_BASE/cards/combov2/chips/comp/pci"
set I2C_BASE    "$COMP_BASE/ctrls/i2c_hw"
set ASFIFO_BASE "$COMP_BASE/base/fifo/asfifo"
set TRANSFORMER_BASE "$COMP_BASE/fl_tools/flow/transformer"

set COMPONENTS [list \
   [list "IB_EP"           $IB_EP_BASE       "FULL" ] \
   [list "I2C"             $I2C_BASE         "FULL" ] \
   [list "FL_TRANSFORMER"  $TRANSFORMER_BASE "FULL" ] \
   [list "ASFIFO"          $ASFIFO_BASE      "FULL" ] \
]

set MOD "$MOD $IB_BR_BASE/ib_tx8.vhd"
set MOD "$MOD ib_rx8_dcm.vhd"
set MOD "$MOD fpga_config.vhd"
set MOD "$MOD flashctrl.vhd"
set MOD "$MOD clkman_sp3.vhd"
set MOD "$MOD ifcboot.vhd"
set MOD "$MOD sysctrl.vhd"
