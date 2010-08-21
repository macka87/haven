# XST.tcl: tcl script to compile all design
# Copyright (C) 2007 CESNET
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

set VHDL_BASE     "../../../../.."

# global XST tcl script
source $VHDL_BASE/base/XST.inc.tcl

# synthesis variables
set SYNTH_FLAGS(MODULE) "fpga_u5"
set SYNTH_FLAGS(OUTPUT) "c6x_top"
set SYNTH_FLAGS(FPGA)   "xc2vp50"
set SYNTH_FLAGS(CARD)   "Combo6X"
# set SYNTH_FLAGS(SETUP_FLAGS) [list \
# [list "-fsm_encoding" "auto"] \
# ]

# hierarchy setting
set PACKAGES   ""
set COMPONENTS ""
set MOD        ""

source Modules.tcl

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(MOD)         $MOD
set HIERARCHY(TOP_LEVEL)   "../aurfc_test.vhd
                            c6x_ent.vhd \
                            c6x_top.vhd"


# global procedures
proc SetTopAttribConstr { } {
   global TOP_LEVEL_ENT
   set CONSTR [list \
                  "BEGIN MODEL \"fpga_u5\"" \
                  "NET \"LCLKF\" PERIOD = 50MHz HIGH 50%;" \
                  "NET \"CLKF\" PERIOD = 125 HIGH 50%;" \
                  "END;"\
   ]
   return $CONSTR

}

# Automatic design sythtesis
SynthesizeProject SYNTH_FLAGS HIERARCHY 

