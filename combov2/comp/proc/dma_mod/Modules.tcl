# Modules.tcl: DMA Module local include script
# Copyright (C) 2008 CESNET
# Author: Martin Kosek <kosek@liberouter.org>
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

# Components
set COMPONENTS [list \
   [ list "DMA_MOD_1x64b_RX"        $ENTITY_BASE/dma_mod_1x64b_rx        "FULL"] \
   [ list "DMA_MOD_1x64b_RXTX"      $ENTITY_BASE/dma_mod_1x64b_rxtx      "FULL"] \
   [ list "DMA_MOD_1x128b_RX"       $ENTITY_BASE/dma_mod_1x128b_rx       "FULL"] \
   [ list "DMA_MOD_nx64b_RX"        $ENTITY_BASE/dma_mod_nx64b_rx        "FULL"] \
   [ list "DMA_MOD_2x64b_RX"        $ENTITY_BASE/dma_mod_2x64b_rx        "FULL"] \
   [ list "DMA_MOD_2x64b_RXTX"      $ENTITY_BASE/dma_mod_2x64b_rxtx      "FULL"] \
   [ list "DMA_MOD_2x64b_RXTX_GEN"  $ENTITY_BASE/dma_mod_2x64b_rxtx_gen  "FULL"] \
   [ list "DMA_MOD_2x64b_RXTX_PAC"  $ENTITY_BASE/dma_mod_2x64b_rxtx_pac  "FULL"] \
   [ list "DMA_MOD_2x128b_RX"       $ENTITY_BASE/dma_mod_2x128b_rx       "FULL"] \
   [ list "DMA_MOD_4x16b_RXTX"      $ENTITY_BASE/dma_mod_4x16b_rxtx      "FULL"] \
   [ list "DMA_MOD_4x16b_RXTX_GEN"  $ENTITY_BASE/dma_mod_4x16b_rxtx_gen  "FULL"] \
   [ list "DMA_MOD_4x16b_RXTX_PAC"  $ENTITY_BASE/dma_mod_4x16b_rxtx_pac  "FULL"] \
]

