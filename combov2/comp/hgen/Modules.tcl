# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2009 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
set COMP_BASE           "$ENTITY_BASE/.."
set MUX_BASE            "$COMP_BASE/base/logic/mux"
set DEMUX_BASE          "$COMP_BASE/base/logic/demux"
set SPLITER_BASE        "$COMP_BASE/hgen/comp/spliter"
set FIFO_BASE           "$COMP_BASE/base/fifo/fifo_layers/fifo_core/sync_block"
set JENKINS_BASE        "$COMP_BASE/hgen/comp/jenkins"
set FORK_BASE           "$COMP_BASE/fl_tools/flow/fork"
set FL_FIFO_BASE        "$COMP_BASE/fl_tools/storage/fifo"
set MASK_BASE           "$COMP_BASE/hgen/comp/mask"
set TRANSFORMER_BASE    "$COMP_BASE/fl_tools/flow/transformer"
set CONV_BASE           "$COMP_BASE/hgen/comp/128_to_96"
set MARKER_BASE         "$COMP_BASE/fl_tools/edit/simple_marker"
set SPLITTER_BASE       "$COMP_BASE/fl_tools/flow/splitter"
set SEQUENCER_BASE      "$COMP_BASE/fl_tools/flow/sequencer"

set PACKAGES "$PACKAGES $COMP_BASE/base/pkg/math_pack.vhd"

set COMPONENTS [list \
    [list "FL_FIFO"        $FL_FIFO_BASE        "FULL"] \
    [list "GEN_MUX"        $MUX_BASE            "FULL"] \
    [list "GEN_DEMUX"      $DEMUX_BASE          "FULL"] \
    [list "SPLITER"        $SPLITER_BASE        "FULL"] \
    [list "FIFO"           $FIFO_BASE           "FULL"] \
    [list "JENKINS"        $JENKINS_BASE        "FULL"] \
    [list "FORK"           $FORK_BASE           "FULL"] \
    [list "MASK"           $MASK_BASE           "FULL"] \
    [list "TRANSFORMER"    $TRANSFORMER_BASE    "FULL"] \
    [list "128_TO_96"      $CONV_BASE           "FULL"] \
    [list "MARKER"         $MARKER_BASE         "FULL"] \
    [list "SPLITTER"       $SPLITTER_BASE       "TICKET"] \
    [list "SEQUENCER"      $SEQUENCER_BASE      "TICKET"] \
]

#set MOD "$MOD $ENTITY_BASE/hgen_mark_fsm.vhd"
set MOD "$MOD $ENTITY_BASE/hgen_core.vhd"
set MOD "$MOD $ENTITY_BASE/hgen_ent.vhd"
set MOD "$MOD $ENTITY_BASE/hgen_new.vhd"
set MOD "$MOD $ENTITY_BASE/hgen_ver_cover.vhd"
set MOD "$MOD $ENTITY_BASE/multi_hgen_ver_cover.vhd"
set MOD "$MOD $ENTITY_BASE/double_multi_hgen_ver_cover.vhd"
