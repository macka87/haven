# 
# XST.tcl: XST tcl script to compile specified module
# Copyright (C) 2007 CESNET
# Author(s): Stepan Friedl <friedl@liberouter.org>
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

# specify vhdl_design directory
set BASE       "../../../../../../.."
set FIRMWARE_BASE  $BASE

# synthesis variables
set SYNTH_FLAGS(MODULE) "ml555"
set SYNTH_FLAGS(OUTPUT) "ml555_arch"
set SYNTH_FLAGS(FPGA)   "xc5vlx50t"

set MOD ""
# list of sub-components
source Modules.tcl

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(MOD)         $MOD
set HIERARCHY(TOP_LEVEL)   "ml555.vhd \
                            ml555_arch.vhd"
                            

echo "Including Precision.tcl for NetCOPE"
source $FIRMWARE_BASE/cards/ml555/netcope/Precision.tcl

# global procedures
proc SetTopAttribConstr { } {
   # Call global NetCope constraints procedure
   NetCopeAttribConstr
   # Call local project constraints - none so far
}

# Run global precision tcl script to include general functions
source $BASE/build/Precision.inc.tcl

SynthesizeProject SYNTH_FLAGS HIERARCHY
