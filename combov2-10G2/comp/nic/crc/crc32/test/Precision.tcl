# Precision.tcl: Precision tcl script to compille all design
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

set VHDL_BASE     "../../../.."

# global leonardo tcl script
source $VHDL_BASE/base/Precision.inc.tcl

# glogal procedures 
proc SetTopAttribConstr { } {
   create_clock -period 6.4 CLK
}

# synthesis variables
set MODULE     "top_level"
set OUTPUT     "top_level"
set FPGA       "xc2v1000"

set CRC32_BASE "$VHDL_BASE/units/crc/crc32"

set COMPONENTS [list \
   [list CRC32    $CRC32_BASE   "FULL"      [list [list "CRC_U"   "FULL"]]] \
]

set PACKAGES   ""
set MOD        "$VHDL_BASE/combo6/chips/fpga.vhd \
                $VHDL_BASE/units/crc/crc32/test/top_level.vhd"

# Automatic design sythtesis 
SynthesizeProject $FPGA $MODULE $OUTPUT $COMPONENTS $PACKAGES $MOD 


