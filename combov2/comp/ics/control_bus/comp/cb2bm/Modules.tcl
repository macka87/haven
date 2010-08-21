# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2006 CESNET
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

# Source files for the component

if { $ARCHGRP == "FULL" } {
  set COMP_BASE         "$ENTITY_BASE/../../../.."
  set CB_ENDPOINT_BASE  "$ENTITY_BASE/../cb_endpoint"
  set IB_PKG_BASE       "$ENTITY_BASE/../../../internal_bus/pkg"
  set FL_PKG_BASE       "$COMP_BASE/fl_tools/pkg"
   
  # Components
  set COMPONENTS [list \
      [ list "CB_ENDPOINT"    "$CB_ENDPOINT_BASE"           "FULL"] \
      [ list "FIFO"           "$COMP_BASE/base/fifo/fifo"   "FULL"] \
      [ list "PKG_MATH"       "$COMP_BASE/base/pkg"         "MATH"] \
      [ list "DEMUX"          "$COMP_BASE/base/logic/demux" "FULL"] \
  ]

  # Packages
  set PACKAGES "$PACKAGES $ENTITY_BASE/../../pkg/cb_pkg.vhd" 
  set PACKAGES "$PACKAGES $IB_PKG_BASE/ib_pkg.vhd" 
  set PACKAGES "$PACKAGES $FL_PKG_BASE/fl_pkg.vhd" 

  set MOD "$MOD $ENTITY_BASE/cb2bm_core.vhd"
  set MOD "$MOD $ENTITY_BASE/cb2bm_core_arch.vhd"
  set MOD "$MOD $ENTITY_BASE/cb2bm.vhd"
  
  set MOD "$MOD $ENTITY_BASE/cb2bm_endpoint.vhd"
}

