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

# specify vhdl_design directory
set FIRMWARE_BASE   "../../../../.."

# top level entity
set TOP_LEVEL_ENT   "dma_module_gen"

source $FIRMWARE_BASE/build/Precision.inc.tcl

set DMA_MODULE_BASE ".."
set DMA_CONST_FILE "default_const.vhd"

# synthesis variables
set SYNTH_FLAGS(MODULE) $TOP_LEVEL_ENT
set SYNTH_FLAGS(OUTPUT) $TOP_LEVEL_ENT
set SYNTH_FLAGS(FPGA)   "xc5vlx110t"

# hierarchy setting
set PACKAGES   ""
set COMPONENTS ""
set MOD        ""

# list of sub-components
set COMPONENTS [list \
    [list "DMA_MODULE" $DMA_MODULE_BASE    "FULL"] \
]

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(MOD)         $MOD

proc SetTopAttribConstr { } {
   create_clock -design rtl -name CLK -domain ClockDomain0 -period 5 [find_clocks]

   # Do not insert PADs - will be inserted in toplevel
   set_attribute -design rtl -name NOPAD -value TRUE -port {*}
}

SynthesizeProject SYNTH_FLAGS HIERARCHY
