# 
# Precision.tcl: tcl script to compile specified module
# Copyright (C) 2007 CESNET
# Author(s): Stepan Friedl <friedl@liberouter.org>
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

# specify vhdl_design directory
set BASE       "../../../../.."
set FIRMWARE_BASE  $BASE

# synthesis variables
set SYNTH_FLAGS(MODULE) "fpga_u16"
set SYNTH_FLAGS(OUTPUT) "sp3"
set SYNTH_FLAGS(FPGA)   "xc3s1200e"
set XILINX "/Xilinx/ISE"

set MOD ""
set PACKAGES "$XILINX/vhdl/src/unisims/unisim_VCOMP.vhd"

set TIME [clock seconds]
scan [clock format $TIME -format %y] %d YEAR
scan [clock format $TIME -format %m] %d MONTH
scan [clock format $TIME -format %d] %d DAY
scan [clock format $TIME -format %H] %d HOUR
scan [clock format $TIME -format %M] %d MIN

set HEXTIME [expr (($YEAR<<28) + ($MONTH<<24) + ($DAY<<16) + ($HOUR<<8) + ($MIN))]
set GEN_TIME "BUILD_TIME X\"[format %08X $HEXTIME]\""

set SYNTH_FLAGS(GENERICS) [list [list $GEN_TIME]]

# global procedures
proc SetTopAttribConstr { } {
   # Project constraints 
   create_clock -design rtl -name CCLK -period 10 -waveform {0 5} -domain ClockDomain0 CCLK
   create_clock -design rtl -name XRD(7) -period 8 -waveform {0 4} -domain ClockDomain1 XRD(7)
   set_attribute -design rtl -name OUTFF -value FALSE -port FA(25:0)
#   set_attribute -design rtl -name INFF -value FALSE -port FD(15:0)
}


# list of sub-components
source Modules.tcl

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(MOD)         $MOD
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(TOP_LEVEL)   "$FIRMWARE_BASE/cards/combov2/chips/fpga_u16.vhd \
                            sp3.vhd"
                           
# Run global precision tcl script to include general functions
source $BASE/build/Precision.inc.tcl

SynthesizeProject SYNTH_FLAGS HIERARCHY
