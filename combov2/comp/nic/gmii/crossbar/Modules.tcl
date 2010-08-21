# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2007 CESNET
# Author: Pribyl Bronislav <xpriby12@stud.fit.vutbr.cz>
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the OpenIPCore Hardware General Public
# License as published by the OpenIPCore Organization; either version
# 0.20-15092000 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# OpenIPCore Hardware General Public License for more details.
#
# You should have received a copy of the OpenIPCore Hardware Public
# License along with this program; if not, download it from
# OpenCores.org (http://www.opencores.org/OIPC/OHGPL.shtml).
#
#

# Base directories
set COMP_BASE        "$ENTITY_BASE/../../.." 
set MATH_PACK_BASE   "$COMP_BASE/base/pkg"

if { $ARCHGRP == "FULL" } {
   set GEN_MUX_BASE      "$COMP_BASE/base/logic/mux"
   set LOCAL_BUS_BASE    "$COMP_BASE/ics/local_bus"
   set MI32_SIM_BASE     "$LOCAL_BUS_BASE/comp/mi32_sim"
   set GMII_BASE         "$COMP_BASE/nic/gmii"
   set CROSSBAR_BASE     "$GMII_BASE/crossbar"
   set IB_SIM_BASE       "$COMP_BASE/ics/internal_bus/comp/ib_sim"

# Source files for all components
   set PACKAGES  "$MATH_PACK_BASE/math_pack.vhd"
	       
   set COMPONENTS [list\
      [list   "MATH_PACK"    $MATH_PACK_BASE          "MATH"]\
			[list   "GEN_MUX"      $GEN_MUX_BASE            "FULL"]\
	]


   set MOD "$MOD $LOCAL_BUS_BASE/pkg/lb_pkg.vhd"


   set MOD "$MOD $CROSSBAR_BASE/crossbar_ent.vhd"
   set MOD "$MOD $CROSSBAR_BASE/crossbar.vhd"
}
