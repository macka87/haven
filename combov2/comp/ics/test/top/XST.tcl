# Precision.tcl: Precision tcl script to compile specified module
# Copyright (C) 2006 CESNET
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

# specify vhdl_design directory
set VHDL_BASE  "../../../.."

set UNITS_BASE         "$VHDL_BASE/units"
set COMMON_BASE        "$UNITS_BASE/common"
set ICS_TEST_APP_BASE  "$VHDL_BASE/units/ics/test"
set AURFC_BASE         "$VHDL_BASE/units/rio/aurfc"
set RIO_CLKGEN_BASE    "$VHDL_BASE/units/rio/clkgen"

# synthesis variables
set SYNTH_FLAGS(MODULE) "fpga_u5"
set SYNTH_FLAGS(OUTPUT) "combo6x"
set SYNTH_FLAGS(FPGA)   "xc2vp50"

# list of sub-components
set COMPONENTS [list [list "RIO_CLKGEN"     $RIO_CLKGEN_BASE        "FULL" ] \
                     [list "AURFC"          $AURFC_BASE             "8BYTE"] \
                     [list "ICS_TEST_APP"   $ICS_TEST_APP_BASE      "FULL"]  \
               ]

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(TOP_LEVEL)   "fpga_u5.vhd combo6x.vhd"


proc SetTopAttribConstr { } {
   set CONSTR [list \
                  "BEGIN MODEL \"fpga_u5\"" \
                  "NET \"CLKF\" PERIOD = 125MHz HIGH 50%;" \
                  "NET \"CLKF_BUFG\" PERIOD = 125MHz HIGH 50%;" \
                  "NET \"USRCLK\" PERIOD = 125MHz HIGH 50%;" \
                  "NET \"USRCLK2\" PERIOD = 62.5MHz HIGH 50%;" \
                  "NET \"CLK\" PERIOD = 62.5MHz HIGH 50%;" \
                  "END;"\
   ]
   return $CONSTR
}

# Run global precision tcl script to include general functions
source $VHDL_BASE/base/XST.inc.tcl

# In fact, XST tcl script only generates XST script named XST.xst.
SynthesizeProject SYNTH_FLAGS HIERARCHY

# Now Makefile will call 'xst -ifn XST.xst' to perform the synthesis.
