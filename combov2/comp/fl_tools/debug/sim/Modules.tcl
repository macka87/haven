# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
#         Libor Polcak <xpolca03@stud.fit.vutbr.cz>
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

# Source files for all components

set COMP_BASE          "$ENTITY_BASE/../../.."
set FL_BASE            "$ENTITY_BASE/../.."
set FIFO_BASE          "$FL_BASE/storage/fifo"
set TRANSFORMER_BASE   "$FL_BASE/flow/transformer"

# Base directories
set PKG_BASE    "$COMP_BASE/base/pkg"
set MOD "$MOD $ENTITY_BASE/../../pkg/fl_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/fl_sim_oper.vhd"
set MOD "$MOD $ENTITY_BASE/fl_sim_logging.vhd"
set MOD "$MOD $ENTITY_BASE/fl_sim.vhd"
set MOD "$MOD $ENTITY_BASE/fl_bfm_rdy_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/fl_bfm_pkg.vhd"
set MOD "$MOD $ENTITY_BASE/fl_bfm.vhd"
set MOD "$MOD $ENTITY_BASE/monitor.vhd"


# components
set COMPONENTS [list \
  [ list "PKG_MATH"        $PKG_BASE         "MATH"] \
  [ list "FL_TRANSFORMER"  $TRANSFORMER_BASE "FULL"] \
  [ list "FL_FIFO"         $FIFO_BASE        "FULL"] \
]

#set COMPONENTS [list \
#  [ list "PKG_MATH"        $PKG_BASE         "MATH"] \
#]