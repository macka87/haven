# Modules.tcl: Local include Modules tcl script
# Copyright (C) 2007 CESNET
# Author: Michal Spacek <xspace14@stud.fit.vutbr.cz>
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

# Set paths
set COMP_BASE         "$ENTITY_BASE/../../.."

set FL_BASE       "$ENTITY_BASE/../.."
set FIFO_BASE     "$FL_BASE/storage/fifo"

# Full FrameLink packet binder
if { $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/packet_binder.vhd"
}
# components
set COMPONENTS [list \
   [ list "PKG_MATH"    $COMP_BASE/base/pkg  "MATH"] \
   [ list "FIFO"        $FIFO_BASE           "FULL"] \
]


# covers
set MOD "$MOD $ENTITY_BASE/top/packet_binder_fl16.vhd"
set MOD "$MOD $ENTITY_BASE/top/packet_binder_fl32.vhd"
