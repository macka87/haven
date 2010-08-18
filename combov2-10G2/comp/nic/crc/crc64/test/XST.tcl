# XST.tcl: XST tcl script to compile specified module
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

set ROOT               "../../../../.."
set FIRMWARE_BASE      $ROOT
set BUILD              "$ROOT/build"

set TOP_LEVEL_ENT      "fpga"

# synthesis variables
# (MODULE must be set to the name of toplevel component)
set SYNTH_FLAGS(MODULE) $TOP_LEVEL_ENT
set SYNTH_FLAGS(OUTPUT) "top_level"
set SYNTH_FLAGS(FPGA)   "xc2vp20"
#set SYNTH_FLAGS(FPGA)   "xc5vlx110"

# list of sub-components
set COMPONENTS [list  [list "CRC64"   ".."    "FULL"]]


set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(MOD)         "top_level.vhd"

proc SetTopAttribConstr { } {
   global TOP_LEVEL_ENT
   set CONSTR [list \
                  "BEGIN MODEL \"$TOP_LEVEL_ENT\"" \
                  "NET \"CLK\" PERIOD = 156.25MHz HIGH 50%;" \
                  "NET \"DI(0)\"   IOB = FALSE;" \
                  "NET \"DI(1)\"   IOB = FALSE;" \
                  "NET \"DI(2)\"   IOB = FALSE;" \
                  "NET \"DI(3)\"   IOB = FALSE;" \
                  "NET \"DI(4)\"   IOB = FALSE;" \
                  "NET \"DI(5)\"   IOB = FALSE;" \
                  "NET \"DI(6)\"   IOB = FALSE;" \
                  "NET \"DI(7)\"   IOB = FALSE;" \
                  "NET \"DI(8)\"   IOB = FALSE;" \
                  "NET \"DI(9)\"   IOB = FALSE;" \
                  "NET \"DI(10)\"   IOB = FALSE;" \
                  "NET \"DI(11)\"   IOB = FALSE;" \
                  "NET \"DI(12)\"   IOB = FALSE;" \
                  "NET \"DI(13)\"   IOB = FALSE;" \
                  "NET \"DI(14)\"   IOB = FALSE;" \
                  "NET \"DI(15)\"   IOB = FALSE;" \
                  "NET \"DI(16)\"   IOB = FALSE;" \
                  "NET \"DI(17)\"   IOB = FALSE;" \
                  "NET \"DI(18)\"   IOB = FALSE;" \
                  "NET \"DI(19)\"   IOB = FALSE;" \
                  "NET \"DI(20)\"   IOB = FALSE;" \
                  "NET \"DI(21)\"   IOB = FALSE;" \
                  "NET \"DI(22)\"   IOB = FALSE;" \
                  "NET \"DI(23)\"   IOB = FALSE;" \
                  "NET \"DI(24)\"   IOB = FALSE;" \
                  "NET \"DI(25)\"   IOB = FALSE;" \
                  "NET \"DI(26)\"   IOB = FALSE;" \
                  "NET \"DI(27)\"   IOB = FALSE;" \
                  "NET \"DI(28)\"   IOB = FALSE;" \
                  "NET \"DI(29)\"   IOB = FALSE;" \
                  "NET \"DI(30)\"   IOB = FALSE;" \
                  "NET \"DI(31)\"   IOB = FALSE;" \
                  "NET \"DI(32)\"   IOB = FALSE;" \
                  "NET \"DI(33)\"   IOB = FALSE;" \
                  "NET \"DI(34)\"   IOB = FALSE;" \
                  "NET \"DI(35)\"   IOB = FALSE;" \
                  "NET \"DI(36)\"   IOB = FALSE;" \
                  "NET \"DI(37)\"   IOB = FALSE;" \
                  "NET \"DI(38)\"   IOB = FALSE;" \
                  "NET \"DI(39)\"   IOB = FALSE;" \
                  "NET \"DI(40)\"   IOB = FALSE;" \
                  "NET \"DI(41)\"   IOB = FALSE;" \
                  "NET \"DI(42)\"   IOB = FALSE;" \
                  "NET \"DI(43)\"   IOB = FALSE;" \
                  "NET \"DI(44)\"   IOB = FALSE;" \
                  "NET \"DI(45)\"   IOB = FALSE;" \
                  "NET \"DI(46)\"   IOB = FALSE;" \
                  "NET \"DI(47)\"   IOB = FALSE;" \
                  "NET \"DI(48)\"   IOB = FALSE;" \
                  "NET \"DI(49)\"   IOB = FALSE;" \
                  "NET \"DI(40)\"   IOB = FALSE;" \
                  "NET \"DI(51)\"   IOB = FALSE;" \
                  "NET \"DI(52)\"   IOB = FALSE;" \
                  "NET \"DI(53)\"   IOB = FALSE;" \
                  "NET \"DI(54)\"   IOB = FALSE;" \
                  "NET \"DI(55)\"   IOB = FALSE;" \
                  "NET \"DI(56)\"   IOB = FALSE;" \
                  "NET \"DI(57)\"   IOB = FALSE;" \
                  "NET \"DI(58)\"   IOB = FALSE;" \
                  "NET \"DI(59)\"   IOB = FALSE;" \
                  "NET \"DI(50)\"   IOB = FALSE;" \
                  "NET \"DI(61)\"   IOB = FALSE;" \
                  "NET \"DI(62)\"   IOB = FALSE;" \
                  "NET \"DI(63)\"   IOB = FALSE;" \
                  "NET \"DI_DV\"   IOB = FALSE;" \
                  "NET \"DO(0)\"   IOB = FALSE;" \
                  "NET \"DO(1)\"   IOB = FALSE;" \
                  "NET \"DO(2)\"   IOB = FALSE;" \
                  "NET \"DO(3)\"   IOB = FALSE;" \
                  "NET \"DO(4)\"   IOB = FALSE;" \
                  "NET \"DO(5)\"   IOB = FALSE;" \
                  "NET \"DO(6)\"   IOB = FALSE;" \
                  "NET \"DO(7)\"   IOB = FALSE;" \
                  "NET \"DO(8)\"   IOB = FALSE;" \
                  "NET \"DO(9)\"   IOB = FALSE;" \
                  "NET \"DO(10)\"   IOB = FALSE;" \
                  "NET \"DO(11)\"   IOB = FALSE;" \
                  "NET \"DO(12)\"   IOB = FALSE;" \
                  "NET \"DO(13)\"   IOB = FALSE;" \
                  "NET \"DO(14)\"   IOB = FALSE;" \
                  "NET \"DO(15)\"   IOB = FALSE;" \
                  "NET \"DO(16)\"   IOB = FALSE;" \
                  "NET \"DO(17)\"   IOB = FALSE;" \
                  "NET \"DO(18)\"   IOB = FALSE;" \
                  "NET \"DO(19)\"   IOB = FALSE;" \
                  "NET \"DO(20)\"   IOB = FALSE;" \
                  "NET \"DO(21)\"   IOB = FALSE;" \
                  "NET \"DO(22)\"   IOB = FALSE;" \
                  "NET \"DO(23)\"   IOB = FALSE;" \
                  "NET \"DO(24)\"   IOB = FALSE;" \
                  "NET \"DO(25)\"   IOB = FALSE;" \
                  "NET \"DO(26)\"   IOB = FALSE;" \
                  "NET \"DO(27)\"   IOB = FALSE;" \
                  "NET \"DO(28)\"   IOB = FALSE;" \
                  "NET \"DO(29)\"   IOB = FALSE;" \
                  "NET \"DO(30)\"   IOB = FALSE;" \
                  "NET \"DO(31)\"   IOB = FALSE;" \
                  "NET \"MASK(0)\" IOB = FALSE;" \
                  "NET \"MASK(1)\" IOB = FALSE;" \
                  "NET \"MASK(2)\" IOB = FALSE;" \
                  "NET \"EOP\"     IOB = FALSE;" \
                  "NET \"DO_DV\"   IOB = FALSE;" \
                  "END;"\
   ]
   return $CONSTR
}

# Run global precision tcl script to include general functions
source $BUILD/XST.inc.tcl

# In fact, XST tcl script only generates XST script named XST.xst.
SynthesizeProject SYNTH_FLAGS HIERARCHY

# Now Makefile will call 'xst -ifn XST.xst' to perform the synthesis.
