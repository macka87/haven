# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2006 CESNET
# Author: Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
# $Id$
#

# Source files for all components

global FIRMWARE_BASE

if { $ARCHGRP == "FULL" } {

 set COMMON_BASE         "$FIRMWARE_BASE/comp/base" 
 set COMPONENTS [list \
     [list "DP_BMEM"    $COMMON_BASE/mem/dp_bmem    "FULL"] \
     [list "DP_DISTMEM" $COMMON_BASE/mem/dp_distmem "FULL"] \
  ]
 
 set MOD "$MOD $ENTITY_BASE/../../pkg/ib_pkg.vhd"
 set MOD "$MOD $ENTITY_BASE/ibmi64mem.vhd"
 set MOD "$MOD $ENTITY_BASE/ibmi64mem_norec.vhd"
 
}


if { $ARCHGRP == "EMPTY" } {

}
