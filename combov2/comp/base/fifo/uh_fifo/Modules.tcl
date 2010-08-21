# Leonardo.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
#         Petr Mikusek   <petr.mikusek@liberouter.org>
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

set COMP_BASE       "$ENTITY_BASE/../../.."

# Source files for implemented component
if { $ARCHGRP == "FULL" } {

   # package
   set PACKAGES      "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
   set PACKAGES      "$PACKAGES $COMP_BASE/fl_tools/pkg/fl_pkg.vhd"

   # sub-components path setting
   set SH_REG_BASE   "$COMP_BASE/base/shreg/sh_reg"
   set REGFLAGS_BASE "$COMP_BASE/base/logic/dp_regflags"
   set LB_BASE       "$COMP_BASE/old/lb"

   # list of sub-components
   set COMPONENTS [list \
      [list "SH_REG"    $SH_REG_BASE   "FULL"] \
      [list "REGFLAGS"  $REGFLAGS_BASE "FULL"] \
      [list "LB"        $LB_BASE       "FULL"] \
   ]

   set MOD "$MOD $ENTITY_BASE/uh_fifo_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_fifo.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_four_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_four_top.vhd"

   # MI32 cover with ADC decoder for four UH FIFOs
   set MOD "$MOD $ENTITY_BASE/uh_four_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_four_mi32_top.vhd"

   # FrameLink cover
   set MOD "$MOD $ENTITY_BASE/uh_fifo_fl_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_fifo_fl.vhd"

   # FrameLink cover with ADC decoder for four UH FIFOs
   set MOD "$MOD $ENTITY_BASE/uh_four_fl32_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_four_fl32_mi32_top.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_four_fl32_mi32_lb.vhd"
}

# FULL UH_FIFO with MI32 interface only
if { $ARCHGRP == "FULL_MI32" } {

   # package
   set PACKAGES      "$PACKAGES $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"
   set PACKAGES      "$PACKAGES $COMP_BASE/fl_tools/pkg/fl_pkg.vhd"

   # sub-components path setting
   set SH_REG_BASE   "$COMP_BASE/base/shreg/sh_reg"
   set REGFLAGS_BASE "$COMP_BASE/base/logic/dp_regflags"

   # list of sub-components
   set COMPONENTS [list \
      [list "SH_REG"    $SH_REG_BASE   "FULL"] \
      [list "REGFLAGS"  $REGFLAGS_BASE "FULL"] \
   ]

   set MOD "$MOD $ENTITY_BASE/uh_fifo_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_fifo.vhd"

   # MI32 cover with ADC decoder for four UH FIFOs
   set MOD "$MOD $ENTITY_BASE/uh_four_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_four_mi32_top.vhd"

   # FrameLink cover
   set MOD "$MOD $ENTITY_BASE/uh_fifo_fl_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_fifo_fl.vhd"

   # FrameLink cover with ADC decoder for four UH FIFOs
   set MOD "$MOD $ENTITY_BASE/uh_four_fl32_mi32_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_four_fl32_mi32_top.vhd"
}

# LUP debug component  - It enables to send data into UH FIFO from SW
if { $ARCHGRP == "LUP_DEBUG" } {
   set MOD "$MOD $COMP_BASE/base/logic/dp_regflags/dp_regflags.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_fifo_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/debug/pci_to_lup.vhd"
}

# Source file for empty component - empty architecture
if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/uh_fifo_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/uh_fifo_empty.vhd"
}

# debug component
if { $ARCHGRP == "DEBUG" } {
   set MOD "$MOD $ENTITY_BASE/uh_fifo_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/debug/uh_hfe_debug.vhd"
   set MOD "$MOD $ENTITY_BASE/debug/uh_top_hfe_debug1.vhd"
}

