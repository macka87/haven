# Precision.tcl: Precision tcl script to compile specified module
# Copyright (C) 2008 CESNET
# Author: Jan Vozenilek <xvozen00@stud.fit.vutbr.cz>
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

# component to synthetise
set TEST_COMP "fifo2nfifo"
#set TEST_COMP "mem2nfifo"
#set TEST_COMP "nfifo2fifo"
#set TEST_COMP "nfifo2mem"

# specify vhdl_design directory
set FIRMWARE_BASE "../../../.."
set COMP_BASE     "$FIRMWARE_BASE/comp"
set BUFFER_BASE   "$COMP_BASE/base/buffers"

# synthesis variables
set SYNTH_FLAGS(MODULE) $TEST_COMP
set SYNTH_FLAGS(OUTPUT) $TEST_COMP
set SYNTH_FLAGS(FPGA)   "xc2vp50"
#set SYNTH_FLAGS(FPGA)   "xc5vlx110"

# list of sub-components
set COMPONENTS [list  \
                  [list $TEST_COMP $BUFFER_BASE/top "FULL"] \
               ]

set HIERARCHY(COMPONENTS)  $COMPONENTS

proc SetTopAttribConstr { } {
       create_clock -period 10 CLK
}

# run global precision tcl script to synthesize module design
puts "Running global precision tcl script"
source $FIRMWARE_BASE/build/Precision.inc.tcl

SynthesizeProject SYNTH_FLAGS HIERARCHY
