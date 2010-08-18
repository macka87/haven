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

# Set paths

set COMP_BASE           "$ENTITY_BASE/../../.."
set FL_ASFIFO_BASE      "$COMP_BASE/fl_tools/storage/asfifo"

set PACKAGES "$PACKAGES $COMP_BASE/gics/internal_bus/pkg/ib_ifc_pkg.vhd"
set PACKAGES "$PACKAGES $ENTITY_BASE/dma_1x64b_rx_const.vhd"

# Local include
set MOD "$MOD $ENTITY_BASE/dma_1x64b_rx_ent.vhd"
set MOD "$MOD $ENTITY_BASE/dma_1x64b_rx.vhd"

global DMA_CONST_FILE
set DMA_CONST_FILE [eval pwd]/$ENTITY_BASE/dma_1x64b_rx_const.vhd

# Components
set COMPONENTS [list \
   [ list "RX_BUFFERS_64B"  $COMP_BASE/ics/buffers/top  "NEWDMA"] \
   [ list "FL_ASFIFO"       $FL_ASFIFO_BASE             "FULL"] \
]
