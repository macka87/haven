# Precision.tcl: Precision tcl script to compile specified module
# Copyright (C) 2006 CESNET
# Author: Petr Kastovsky <kastovsky@liberouter.org>
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
#
#

# top level entity
#set TOP_LEVEL_ENT "RX_DMA_CTRL"
set TOP_LEVEL_ENT "TX_DMA_CTRL"

# specify vhdl_design directory
set FIRMWARE_BASE   "../../../.."
set BASE            "../../../.."

set RX_DMA_BASE     ".."
set TX_DMA_BASE     ".."

# synthesis variables
set SYNTH_FLAGS(MODULE) $TOP_LEVEL_ENT
set SYNTH_FLAGS(OUTPUT) "comp"
#set SYNTH_FLAGS(FPGA)   "xc5vlx110"
set SYNTH_FLAGS(FPGA)   "xc2vp50"

# list of sub-components
set COMPONENTS [list \
    [list "RX_DMA_CTRL" $RX_DMA_BASE    "FULL"] \
    [list "TX_DMA_CTRL" $TX_DMA_BASE    "FULL"] \
]

set HIERARCHY(COMPONENTS)  $COMPONENTS

proc SetTopAttribConstr { } {
       # PLX clock
       create_clock -period 8 CLK
}

# run global precision tcl script to synthesize module design
puts "Running global precision tcl script"
source $BASE/build/Precision.inc.tcl

SynthesizeProject SYNTH_FLAGS HIERARCHY
