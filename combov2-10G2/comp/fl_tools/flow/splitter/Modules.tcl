# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2009 CESNET
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
set COMP_BASE        "$ENTITY_BASE/../../.."
set FL_BASE          "$ENTITY_BASE/../.."
set FIFO_BASE        "$FL_BASE/storage/fifo"
set SYNC_ORD_FIFO_BASE "$COMP_BASE/base/fifo/fifo_layers/fifo_core/sync_ord"
set FIFO2NFIFO_BASE  "$COMP_BASE/base/buffers/top"
set TRANSFORMER_BASE "$FL_BASE/flow/transformer"
set FIFO_PKG         "$COMP_BASE/base/fifo/fifo_layers/pkg"

# common files
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"

# Full FrameLink Splitter
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/splitter_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_max_select.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_cu_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_cu.vhd"
   set MOD "$MOD $ENTITY_BASE/splitter.vhd"
   set MOD "$MOD $ENTITY_BASE/splitter_generic_output.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"         $COMP_BASE/base/pkg     "MATH"] \
      [ list "FL_FIFO"          $FIFO_BASE              "FULL"] \
      [ list "FL_TRANSFORMER"   $TRANSFORMER_BASE       "FULL"] \
    ]
      # covers
      
set MOD "$MOD $ENTITY_BASE/top/splitter_fl64x4.vhd"
set MOD "$MOD $ENTITY_BASE/top/splitter_fl16x2.vhd"
set MOD "$MOD $ENTITY_BASE/top/splitter_fl128x2.vhd"
set MOD "$MOD $ENTITY_BASE/top/splitter_fl128x4.vhd"
set MOD "$MOD $ENTITY_BASE/top/splitter_fl128_fl4x16.vhd"
set MOD "$MOD $ENTITY_BASE/top/splitter_fl128_fl8x16.vhd"

set MOD "$MOD $ENTITY_BASE/top/splitter_x3_norec.vhd"


}

# FIFO2NFIFO FrameLink Splitter
if { $ARCHGRP == "FIFO2NFIFO" } {
   set MOD "$MOD $ENTITY_BASE/splitter_fifo2nfifo_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_max_select.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_cu_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_cu.vhd"
   set MOD "$MOD $FL_BASE/storage/fifo/compress.vhd"
   set MOD "$MOD $FL_BASE/storage/fifo/decompress.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/align_unit.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/fifo2nfifo_buffer.vhd"
   set MOD "$MOD $ENTITY_BASE/splitter_fifo2nfifo.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"         $COMP_BASE/base/pkg     "MATH"] \
      [ list "FIFO2NFIFO"       $FIFO2NFIFO_BASE        "FULL"] \
      [ list "FL_TRANSFORMER"   $TRANSFORMER_BASE       "FULL"] \
   ]
}

if { $ARCHGRP == "TICKET" } {
   set PACKAGES "$PACKAGES $FIFO_PKG/fifo_pkg.vhd"

   set MOD "$MOD $ENTITY_BASE/fls_max_select.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_cu_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/fls_cu.vhd"
   set MOD "$MOD $FL_BASE/storage/fifo/compress.vhd"
   set MOD "$MOD $FL_BASE/storage/fifo/decompress.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/align_unit.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/fifo2nfifo_buffer.vhd"
   set MOD "$MOD $ENTITY_BASE/ticket_splitter_fifo2nfifo_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/ticket_splitter_fifo2nfifo.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"         $COMP_BASE/base/pkg     "MATH"] \
      [ list "FIFO2NFIFO"       $FIFO2NFIFO_BASE        "FULL"] \
      [ list "TRANSFORMER"      $TRANSFORMER_BASE       "FULL"] \
      [ list "FIFO"             $SYNC_ORD_FIFO_BASE     "FULL"] \
   ]
}

# Empty FrameLink Splitter
if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/splitter_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/splitter_empty.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"    $COMP_BASE/base/pkg     "MATH"] \
   ]
}
