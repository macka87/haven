# Precison.tcl: Precision tcl script to compile PCIE module
# Copyright (C) 2010 CESNET
# Author: Pavol Korcek <korcek@liberouter.org>
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

set FIRMWARE_BASE    "../../../../../../.."
set TOP_LEVEL_ENT     "ebp_wrapper"
set MODULE            "ebp_wrapper"

if { [info exist env(PCIE_CORE_PATH)] } {
   # Get base path from project Makefile
   set PCIE_CORE_PATH   $env(PCIE_CORE_PATH)
   puts "Will use PCIE EP from $PCIE_CORE_PATH"
} else  {
      puts "WARNING: No PCIE_CORE_PATH specified!"
      puts "Setting default path for NIC10G2 (lx155t-2)"
      set PCIE_CORE_PATH   "/home/data/sklep/ipcores/pcie_ebp/nic-10G2/combov2-lx155t/v1.13.0_250"
}

# global Precision tcl script
source $FIRMWARE_BASE/build/Precision.inc.tcl

# synthesis variables
set SYNTH_FLAGS(MODULE) $MODULE
set SYNTH_FLAGS(OUTPUT) $TOP_LEVEL_ENT
set SYNTH_FLAGS(FPGA)   "xc5vlx155t-2"

# hierarchy setting
set PACKAGES   ""
set COMPONENTS ""
set MOD        ""

set COMPONENTS [list  [list $MODULE   ".."    $PCIE_CORE_PATH]]
#set COMPONENTS [list [list  "PCIE_CORE" ".." "FULL" ] ]

set HIERARCHY(COMPONENTS)  $COMPONENTS
set HIERARCHY(PACKAGES)    $PACKAGES
set HIERARCHY(MOD)         $MOD
set HIERARCHY(TOP_LEVEL)   "../ebp_wrapper_ent.vhd"

# Read NetCope global procedures

# global procedures
proc SetTopAttribConstr { } {
   # Optimize synthesis for 250 MHz
   create_clock -design rtl -name TRN_CLK -domain ClockDomain0 -period 4 TRN_CLK
   create_clock -design rtl -name SYS_CLK -domain ClockDomain1 -period 4 SYS_CLK

   # Do not insert PADs - will be inserted in toplevel
   set_attribute -design rtl -name NOPAD -value TRUE -port {*}

   # Do not insert clock buffers
   set_attribute -design rtl -name NOBUFF -value TRUE -net TRN_CLK
   set_attribute -design rtl -name BUFFER_SIG -value {""} -net TRN_CLK
   set_attribute -design rtl -name NOBUFF -value TRUE -net SYS_CLK
   set_attribute -design rtl -name BUFFER_SIG -value {""} -net SYS_CLK
}

# Automatic design sythtesis
SynthesizeProject SYNTH_FLAGS HIERARCHY

