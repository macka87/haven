# Precison.tcl: Precision tcl script to compile ComboV2 design
# Copyright (C) 2008 CESNET
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

set FIRMWARE_BASE    "../.."
set NETCOPE          "$FIRMWARE_BASE/cards/combov2/netcope/eth-10G2"

# global Precision tcl script
source $FIRMWARE_BASE/build/Precision.inc.tcl

# synthesis variables
set SYNTH_FLAGS(MODULE) "fpga_u0"
set SYNTH_FLAGS(OUTPUT) "combov2_core"
# Set FPGA type based on the environment variable
if {[info exists env(FPGA_TYPE)]} {
   puts "Setting FPGA type to $env(FPGA_TYPE)"
   set SYNTH_FLAGS(FPGA) $env(FPGA_TYPE)
} else {
   puts "FPGA_TYPE environment variable doesn't exist, setting FPGA type to default xc5vlx110t"
   set SYNTH_FLAGS(FPGA) "xc5vlx110t"
}

# hierarchy setting
set PACKAGES   ""
set COMPONENTS ""
set MOD        ""

# For precision2007a
#set XILINX_DIR $env(XILINX)
#set PACKAGES "$XILINX_DIR/vhdl/src/unisims/unisim_VCOMP.vhd"

source Modules.tcl

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(MOD)         $MOD
set HIERARCHY(TOP_LEVEL)   "$FIRMWARE_BASE/cards/combov2/chips/fpga_u0.vhd \
                            $NETCOPE/top_level.vhd"

# Read NetCope global procedures

echo "Including Precision.tcl for NetCOPE"
source $NETCOPE/Precision.tcl

# global procedures
proc SetTopAttribConstr { } {
   # Call global NetCope constraints procedure
   NetCopeAttribConstr
   # Call local project constraints - none so far
}

# Automatic design sythtesis
SynthesizeProject SYNTH_FLAGS HIERARCHY
