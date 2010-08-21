# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Libor Polcak <polcak_l@liberouter.org>
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
set FIRMWARE_BASE       "$ENTITY_BASE/../../../.."
set COMP_BASE           "$FIRMWARE_BASE/comp"
set BASE_BASE           "$FIRMWARE_BASE/comp/base"
set FL_BASE             "$ENTITY_BASE/../.."
set FL_FIFO_BASE        "$FL_BASE/storage/fifo"
set FL_TRANSFORMER_BASE "$FL_BASE/flow/transformer"
set FL_CUTTER_BASE      "$FL_BASE/edit/cutter_fake"
set FIFO_BASE           "$BASE_BASE/fifo/fifo_layers/fifo_core/sync_ord"
set FIFO_PKG            "$BASE_BASE/fifo/fifo_layers/pkg"
set MUX_BASE            "$BASE_BASE/logic/mux"
set ENC_BASE            "$BASE_BASE/logic/enc"
set PIPE_BASE        "$FL_BASE/flow/pipe"

set PACKAGES "$PACKAGES $FIRMWARE_BASE/comp/ics/local_bus/pkg/lb_pkg.vhd"
set PACKAGES "$PACKAGES $FIFO_PKG/fifo_pkg.vhd"


# Full FrameLink Sequencer
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/sequencer_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/sequencer.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"       $BASE_BASE/pkg       "MATH"] \
      [ list "FL_CUTTER"      $FL_CUTTER_BASE      "FAKE"] \
      [ list "FIFO"           $FIFO_BASE           "FULL"] \
			[ list "TICKET_SEQUENCER" $ENTITY_BASE       "TICKET"] \
   ]
}

if { $ARCHGRP == "TICKET" } {
   set BINDER_BASE "$ENTITY_BASE/../binder"
   set COMPRESS_BASE "$ENTITY_BASE/../binder"

   set MOD "$MOD $FL_FIFO_BASE/compress.vhd"
   set MOD "$MOD $FL_FIFO_BASE/decompress.vhd"
   set MOD "$MOD $BINDER_BASE/comp/rem_cmp.vhd"
   set MOD "$MOD $BINDER_BASE/comp/align_frame_fsm.vhd"
   set MOD "$MOD $BINDER_BASE/comp/align_frame.vhd"
   set MOD "$MOD $BINDER_BASE/comp/data_transformer.vhd"
   set MOD "$MOD $ENTITY_BASE/ticket_sequencer_ent.vhd"
   set MOD "$MOD $ENTITY_BASE/sequencer_fsm.vhd"
   set MOD "$MOD $ENTITY_BASE/ticket_sequencer.vhd"

   # components
   set COMPONENTS [list \
      [ list "PKG_MATH"       $BASE_BASE/pkg       "MATH"] \
      [ list "GEN_MUX"        $MUX_BASE            "FULL"] \
      [ list "GEN_ENC"        $ENC_BASE            "FULL"] \
      [ list "FIFO"           $FIFO_BASE           "FULL"] \
      [ list "NFIFO2FIFO"     $COMP_BASE/base/buffers/top   "FULL"] \
      [ list "FL_PIPE"        $PIPE_BASE                    "FULL"] \
      [ list "DEMUX"          $COMP_BASE/base/logic/demux   "FULL"] \
      [ list "FL_TRANSFORMER" $FL_TRANSFORMER_BASE "FULL"] \
   ]
}

# Empty FrameLink Sequencer
if { $ARCHGRP == "EMPTY" } {
   set MOD "$MOD $ENTITY_BASE/sequencer_empty.vhd"
}
