# Precision.tcl: Precision tcl script to compile specified module
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@liberouter.org>
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

# specify vhdl_design directory
set VHDL_BASE  "../../../../../.."
set BASE       "../../../../../.."

set UNITS_BASE         "$VHDL_BASE/units"
set COMMON_BASE        "$UNITS_BASE/common"
set MI32TOBM_BASE      "$VHDL_BASE/units/ics/local_bus/comp/lb2bm"

# synthesis variables
set SYNTH_FLAGS(MODULE) "mi32tobm"
set SYNTH_FLAGS(OUTPUT) "mi32tobm"
set SYNTH_FLAGS(FPGA)   "xc2vp50"

# list of sub-components
set COMPONENTS [list  [list "MI32TOBM"   $MI32TOBM_BASE      "FULL"]]


set HIERARCHY(COMPONENTS)  $COMPONENTS

proc SetTopAttribConstr { } {
       # PLX clock
       create_clock -period 10 CLK
}

# run global precision tcl script to synthesize module design
puts "Running global precision tcl script"
source $BASE/base/Precision.inc.tcl

SynthesizeProject SYNTH_FLAGS HIERARCHY
