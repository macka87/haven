# 
# Modules.tcl: 
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

global FIRMWARE_BASE

set TRANSFORMER_BASE "$FIRMWARE_BASE/comp/fl_tools/flow/transformer"
set ASFIFO_BASE      "$FIRMWARE_BASE/comp/base/fifo/asfifo"
set IBSW_BASE        "$FIRMWARE_BASE/comp/ics/internal_bus/comp/ib_switch"
set IBAS_BASE        "$FIRMWARE_BASE/comp/ics/internal_bus/comp/ib_async"
set PCIEBR_BASE      "$FIRMWARE_BASE/comp/gics/internal_bus/comp/root"

# List of instances
set PCIE_INST      [list [list "PCIE_BRIDGE"      "FULL"]]

set COMPONENTS [concat $COMPONENTS [list \
   [list "FL_TRANSFORMER"  $TRANSFORMER_BASE   "FULL" ] \
   [list "ASFIFO"          $ASFIFO_BASE        "FULL" ] \
   [list "PCIE"            $PCIEBR_BASE        "FULL"  $PCIE_INST ] \
   [list "IB_SWITCH"       $IBSW_BASE          "FULL" ] \
   [list "IB_ASYNC"        $IBAS_BASE          "FULL" ] \
]]

set MOD "$MOD $ENTITY_BASE/ib_rx8.vhd"
set MOD "$MOD $ENTITY_BASE/ib_tx8.vhd"
set MOD "$MOD $ENTITY_BASE/combov2_pci_ent.vhd"
set MOD "$MOD $ENTITY_BASE/combov2_pci_async.vhd"
