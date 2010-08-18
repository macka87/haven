# Precison.tcl: Precision tcl script to compile all design
# Copyright (C) 2003 CESNET
# Author: Tomas Martinek <martinek@liberouter.org>
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

set ROOT            "../../../../.."
set FIRMWARE_BASE   $ROOT
set BUILD           "$ROOT/build"

# global leonardo tcl script
source $BUILD/Precision.inc.tcl

# synthesis variables
set SYNTH_FLAGS(MODULE) "top_level"
set SYNTH_FLAGS(OUTPUT) "top_level"
#set SYNTH_FLAGS(FPGA)   "xc2v1000"
set SYNTH_FLAGS(FPGA)   "xc2vp20"
#set SYNTH_FLAGS(FPGA)   "xc4fx12"

# list of sub-components
set COMPONENTS [list \
   [list "CRC64"   ".."   "FULL"]  \
]

set HIERARCHY(PACKAGES)     ""
set HIERARCHY(MOD)          "top_level.vhd"
set HIERARCHY(COMPONENTS)   $COMPONENTS

# glogal procedures
proc SetTopAttribConstr { } {
   create_clock -period 6.4 CLK

   set_attribute -design rtl -name IOB -value FALSE -port DI(*)
   set_attribute -design rtl -name IOB -value FALSE -port DI_DV
   set_attribute -design rtl -name IOB -value FALSE -port DO(*)
   set_attribute -design rtl -name IOB -value FALSE -port MASK(*)
   set_attribute -design rtl -name IOB -value FALSE -port EOP
   set_attribute -design rtl -name IOB -value FALSE -port DO_DV
}

# Automatic design sythtesis
SynthesizeProject SYNTH_FLAGS HIERARCHY

