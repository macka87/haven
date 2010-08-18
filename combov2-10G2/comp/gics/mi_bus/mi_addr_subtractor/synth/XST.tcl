# 
# XST.tcl: XST tcl script to compile specified module
# Copyright (C) 2009 CESNET
# Author(s): Vaclav Bartos <washek@liberouter.org>
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in
#    the documentation and/or other materials provided with the
#    distribution.
# 3. Neither the name of the Company nor the names of its contributors
#    may be used to endorse or promote products derived from this
#    software without specific prior written permission.
#
# This software is provided ``as is'', and any express or implied
# warranties, including, but not limited to, the implied warranties of
# merchantability and fitness for a particular purpose are disclaimed.
# In no event shall the company or contributors be liable for any
# direct, indirect, incidental, special, exemplary, or consequential
# damages (including, but not limited to, procurement of substitute
# goods or services; loss of use, data, or profits; or business
# interruption) however caused and on any theory of liability, whether
# in contract, strict liability, or tort (including negligence or
# otherwise) arising in any way out of the use of this software, even
# if advised of the possibility of such damage.
#
# $Id$
# 

# specify vhdl_design directory
set FIRMWARE_BASE     "../../../../.."
set MODULE            "MI_ADDR_SUBTRACTOR"

# synthesis variables
# (MODULE must be set to the name of toplevel component)
set SYNTH_FLAGS(MODULE) $MODULE
set SYNTH_FLAGS(OUTPUT) $MODULE
set SYNTH_FLAGS(FPGA)   "xc5vlx110t"

# Don't insert IBUFs and OBUFs
set SYNTH_FLAGS(SETUP_FLAGS) [list \
                                [list "-iobuf" "no"] \
                             ]
# list of sub-components
set COMPONENTS [list  [list $MODULE   ".."    "FULL"]]

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(TOP_LEVEL)   "../mi_addr_subtractor.vhd"

proc SetTopAttribConstr { } {
   set CONSTR [list \
                  "BEGIN MODEL \"MI_ADDR_SUBTRACTOR\"" \
                  "NET \"CLK\" PERIOD = 250MHz HIGH 50%;" \
                  "END;"\
                  "MODEL \"MI_ADDR_SUBTRACTOR\" register_balancing = yes;" \
   ]
   return $CONSTR
}

# Run global precision tcl script to include general functions
source $FIRMWARE_BASE/build/XST.inc.tcl

# In fact, XST tcl script only generates XST script named XST.xst.
SynthesizeProject SYNTH_FLAGS HIERARCHY

# Now Makefile will call 'xst -ifn XST.xst' to perform the synthesis.
