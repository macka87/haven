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

  set COMP_BASE        "$ENTITY_BASE/../../.."
  set ARCH_BASE        "$ENTITY_BASE/arch"

  set GICS_BASE        "$COMP_BASE/gics"
  set IBEP_BASE        "$COMP_BASE/gics/internal_bus/comp/endpoint"

  set PACKAGES "$PACKAGES $COMP_BASE/gics/internal_bus/pkg/ib_ifc_pkg.vhd"

  set MOD  "$MOD $COMP_BASE/ics/dma_ctrl/comp/dma_status_reg.vhd"
  set MOD  "$MOD $COMP_BASE/ics/dma_ctrl/comp/dma2data.vhd"
  set MOD  "$MOD $COMP_BASE/ics/dma_ctrl/comp/data2bm.vhd"

  set MOD  "$MOD $ENTITY_BASE/dma_module_gen.vhd"

  set COMPONENTS [list \
   [ list "PKG_MATH"       $COMP_BASE/base/pkg                      "MATH"] \
   [ list "MUX"            $COMP_BASE/base/logic/mux                "FULL"] \
   [ list "DMA_CTRL"       $COMP_BASE/ics/dma_ctrl_generic          "FULL"] \
   [ list "DEMUX"          $COMP_BASE/base/logic/demux              "FULL"] \
   [ list "PIPE"           $COMP_BASE/base/misc/pipe                "FULL"] \
   [ list "DEC1FN"         $COMP_BASE/base/logic/dec1fn             "FULL"] \
   [ list "DESC_MANAGER"   $COMP_BASE/ics/dma_ctrl/comp/desc_manager "FULL"] \
   [ list "TXBUFFER"       $COMP_BASE/ics/buffers/sw_txbuf          "FULL"] \
   [ list "RXBUFFERGEN"    $COMP_BASE/ics/buffers/sw_rxbuf_gen      "FULL"] \
   [ list "FL_DISCARD_STAT" $COMP_BASE/fl_tools/flow/discard        "FULL"] \
   [ list "MI_SPLITTER_ADDR32" $COMP_BASE/gics/mi_bus/mi_splitter   "FULL"] \
   [ list "IB_EP"          $GICS_BASE/internal_bus/comp/endpoint    "FULL"] \
   [ list "BM_CONVERTER"   $GICS_BASE/misc/bm_converter             "FULL"] \
   [ list "TAG_SEQUENCER"  $COMP_BASE/ics/internal_bus/comp/ib_endpoint/tag_sequencer "FULL"] \
   ]

} else {
    error "$ENTITY_MODFILE: Unsupported ARCHGRP: $ARCHGRP" "" "1"
} 

