# Precison.tcl: Precision tcl script to compile DMA module
# Copyright (C) 2009 CESNET
# Author: Viktor Pus <pus@liberouter.org>
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

set FIRMWARE_BASE "../../../../.."

set TOP_LEVEL_ENT $env(TOP_LEVEL_ENT)

# global Precision tcl script
source $FIRMWARE_BASE/build/Precision.inc.tcl

# synthesis variables
set SYNTH_FLAGS(MODULE) $TOP_LEVEL_ENT
set SYNTH_FLAGS(OUTPUT) $TOP_LEVEL_ENT
set SYNTH_FLAGS(FPGA)   "xc5vlx110t"

# hierarchy setting
set PACKAGES   ""
set COMPONENTS ""
set MOD        ""

# For precision2007a
#set XILINX_DIR $env(XILINX)
#set PACKAGES "$XILINX_DIR/vhdl/src/unisims/unisim_VCOMP.vhd"

set COMPONENTS [list [list $TOP_LEVEL_ENT ".." "FULL" ] ]

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(MOD)         $MOD
# set HIERARCHY(TOP_LEVEL)   ".."

# Read NetCope global procedures

# global procedures
proc SetTopAttribConstr { } {
   # Timing constraints does not work for some reason
   #create_clock -design rtl -name CLK -domain ClockDomain0 -period 5 [find_clocks]
   #create_clock -design rtl -name CLK_USER -domain ClockDomain1 -period 5 /CLK_USER

   # Do not insert PADs - will be inserted in toplevel
   set_attribute -design rtl -name NOPAD -value TRUE -port {*}

   # Clock buffers not inserted
}

# Automatic design sythtesis
SynthesizeProject SYNTH_FLAGS HIERARCHY
