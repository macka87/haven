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
set PIPE_BASE        "$FL_BASE/flow/pipe"
set TRANSFORMER_BASE "$FL_BASE/flow/transformer"


set MOD "$MOD $ENTITY_BASE/binder_decl.vhd"
set MOD "$MOD $ENTITY_BASE/binder_ent.vhd"
set MOD "$MOD $FL_BASE/pkg/fl_pkg.vhd"

# Full FrameLink Binder
if { $ARCHGRP == "FULL" } {
   # NFIFO2FIFO Binder
   set MOD "$MOD $ENTITY_BASE/comp/frame_counter.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/frame_counters.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/rem_cmp.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/extrem_select.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output_robin.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/output_framed.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/crossbar.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/align_frame_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/align_frame.vhd"
   set MOD "$MOD $ENTITY_BASE/comp/data_transformer.vhd"
   set MOD "$MOD $ENTITY_BASE/binder_nfifo2fifo.vhd"

   # Simple Binder
   set MOD "$MOD $ENTITY_BASE/binder_simple.vhd"

   # Stupid Binder
   set MOD "$MOD $ENTITY_BASE/binder_stupid.vhd"   

   # top level entity
   set MOD "$MOD $ENTITY_BASE/binder.vhd"
   

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"          $COMP_BASE/base/pkg           "MATH"] \
      [ list "MUX"               $COMP_BASE/base/logic/mux     "FULL"] \
      [ list "DEMUX"             $COMP_BASE/base/logic/demux   "FULL"] \
      [ list "ENC"               $COMP_BASE/base/logic/enc     "FULL"] \
      [ list "DEC1FN"            $COMP_BASE/base/logic/dec1fn  "FULL"] \
      [ list "FL_FIFO"           $FIFO_BASE                    "FULL"] \
      [ list "FL_PIPE"           $PIPE_BASE                    "FULL"] \
      [ list "FL_TRANSFORMER"    $TRANSFORMER_BASE             "FULL"] \
      [ list "NFIFO2FIFO"        $COMP_BASE/base/buffers/top   "FULL"] \
   ]
}

# Empty FrameLink Binder
if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/binder_empty.vhd"
}

set MOD "$MOD $ENTITY_BASE/top/binder_fl16x4to64.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl16x2to16.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl16x2to64.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl32x2to32.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl32x4to32.vhd"
set MOD "$MOD $ENTITY_BASE/top/binder_fl32x4to64.vhd"

set MOD "$MOD $ENTITY_BASE/top/binder_x3_norec.vhd"

