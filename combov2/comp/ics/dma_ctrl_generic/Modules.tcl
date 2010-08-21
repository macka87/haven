# Modules.tcl: Modules.tcl script
# Copyright (C) 2009 CESNET
# Author: Martin Spinler <xspinl00@stud.fit.vutbr.cz>
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

if { $ARCHGRP == "FULL" } {
  set COMP_BASE        "$ENTITY_BASE/../.."

  set MOD  "$MOD [list [list "dk" $COMP_BASE/base/pkg/dk.vhd]]"
  set MOD  "$MOD $ENTITY_BASE/rx_dma_ctrl_arch.vhd"
  set MOD  "$MOD $ENTITY_BASE/tx_dma_ctrl_arch.vhd"

  set COMPONENTS [list \
  [ list "PKG_MATH"   $COMP_BASE/base/pkg    "MATH"] \
  ]

  global DMA_CONST_FILE
  if {  [ info exist DMA_CONST_FILE ] == 0} {
    error "$ENTITY_MODFILE: Global variable DMA_CONST_FILE was not set!" "" "1"
  }
  puts -nonewline "Compiling handelc sources..."
  flush stdout
  exec make -C $ENTITY_BASE DMA_CONST_FILE=$DMA_CONST_FILE
  puts " done."

} else {
    error "$ENTITY_MODFILE: Unsupported ARCHGRP: $ARCHGRP" "" "1"
} 

