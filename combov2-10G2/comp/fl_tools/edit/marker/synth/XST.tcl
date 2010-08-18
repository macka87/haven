# XST.tcl: XST tcl script to compile specified module
# Copyright (C) 2006 CESNET
# Author: Lukas Solanka <solanka@liberouter.org>
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

# top level entity
set TOP_LEVEL_ENT "fl_marker"

# the path to my component directory
set MY_COMP_BASE       ".."

# specify vhdl_design directory
set FIRMWARE_BASE       "$MY_COMP_BASE/../../../.."

# synthesis variables
# (MODULE must be set to the name of toplevel component)
set SYNTH_FLAGS(MODULE) $TOP_LEVEL_ENT
set SYNTH_FLAGS(OUTPUT) "comp"
set SYNTH_FLAGS(FPGA)   "xc2vp30"
#set SYNTH_FLAGS(FPGA)   "xc5vlx110"

# list of sub-components
set COMPONENTS [list  [list "MY_COMP"   $MY_COMP_BASE    "FULL"]]


set HIERARCHY(COMPONENTS)  $COMPONENTS
#set HIERARCHY(TOP_LEVEL)   "top_level.vhd"

proc SetTopAttribConstr { } {
   global TOP_LEVEL_ENT
   set CONSTR [list \
                  "BEGIN MODEL \"$TOP_LEVEL_ENT\"" \
                  "NET \"CLK\" PERIOD = 100MHz HIGH 50%;" \
                  "END;"\
   ]
   return $CONSTR
}

# Run global precision tcl script to include general functions
source $FIRMWARE_BASE/build/XST.inc.tcl

# In fact, XST tcl script only generates XST script named XST.xst.
SynthesizeProject SYNTH_FLAGS HIERARCHY

# Now Makefile will call 'xst -ifn XST.xst' to perform the synthesis.
