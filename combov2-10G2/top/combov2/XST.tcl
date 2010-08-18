# XST.tcl: tcl script to compile all design
# Copyright (C) 2007 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
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

set FIRMWARE_BASE "../.."
set NETCOPE       "$FIRMWARE_BASE/cards/combov2/netcope/eth-10G2"

# global XST tcl script
source $FIRMWARE_BASE/build/XST.inc.tcl

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

# Disable reading cores by XST, it caused MAP crash
set SYNTH_FLAGS(SETUP_FLAGS) [list \
   [list "-read_cores" "no"] \
   [list "-register_balancing" "yes"] \
   [list "-slice_packing" "yes"] \
   [list "-register_duplication" "Yes"] \
]
   #[list "-keep_hierarchy" "soft"] \

# Example of user generics setting
set SYNTH_FLAGS(USER_GENERICS) [list \
   [list "USER_GENERIC0" 126] \
   [list "USER_GENERIC1" 127] \
   [list "USER_GENERIC2" 128] \
   [list "USER_GENERIC3" 129] \
]

# hierarchy setting
set PACKAGES   ""
set COMPONENTS ""
set MOD        ""

source Modules.tcl

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(MOD)         $MOD
set HIERARCHY(TOP_LEVEL)   "$FIRMWARE_BASE/cards/combov2/chips/fpga_u0.vhd \
                            $NETCOPE/top_level.vhd"


# Read NetCope global procedures
source $FIRMWARE_BASE/cards/combov2/netcope/eth-10G2/XST.tcl

# global procedures
proc SetTopAttribConstr { } {

   # Set local constraints - none so far
   set CONSTR [list \
      "MODEL \"FPGA_U0\" register_balancing = yes;" \
      "BEGIN MODEL \"COMBOV2_CORE\"" \
      "NET \"CLK_ICS\" PERIOD = 200MHz HIGH 50%;" \
      "NET \"CLK_USER0\" PERIOD = 200MHz HIGH 50%;" \
      "NET \"CLK_USER0\" PERIOD = 200MHz HIGH 50%;" \
      "NET \"CLK_USER0\" PERIOD = 200MHz HIGH 50%;" \
      "NET \"CLK_USER0\" PERIOD = 200MHz HIGH 50%;" \
      "NET \"CLK125\" PERIOD = 125MHz HIGH 50%;" \
      "NET \"CLK100\" PERIOD = 100MHz HIGH 50%;" \
      "NET \"CLK250\" PERIOD = 250MHz HIGH 50%;" \
      "NET \"CLK62_5\" PERIOD = 62.5MHz HIGH 50%;" \
      "NET \"CLK200\" PERIOD = 200MHz HIGH 50%;" \
      "NET \"CLK166\" PERIOD = 166MHz HIGH 50%;" \
      "NET \"XGMII_RXCLK(0)\" PERIOD = 157MHz HIGH 50%;" \
      "NET \"XGMII_RXCLK(1)\" PERIOD = 157MHz HIGH 50%;" \
      "NET \"XGMII_TXCLK(0)\" PERIOD = 157MHz HIGH 50%;" \
      "NET \"XGMII_TXCLK(1)\" PERIOD = 157MHz HIGH 50%;" \
      "END;"\
   ]

   # Get global NetCope constraints
   set NETCOPE_CONSTR [NetCopeAttribConstr]

   # Resulting constraints are union of local and global constraints
   set CONSTR "$CONSTR $NETCOPE_CONSTR"
   return $CONSTR
}

# Automatic design sythtesis
SynthesizeProject SYNTH_FLAGS HIERARCHY 

