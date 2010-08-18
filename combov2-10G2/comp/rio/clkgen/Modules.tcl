# Leonardo.tcl: Local include Leonardo tcl script
# Copyright (C) 2004 CESNET
# Author: Pecenka  Tomas <pecenka  AT liberouter.org>
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

# Source files for implemented component
set MOD "$MOD $ENTITY_BASE/clkgen_rio_ent.vhd"

if { $ARCHGRP == "FREQ_50" } {
   set MOD "$MOD $ENTITY_BASE/clkgen_50_div.vhd"
   set MOD "$MOD $ENTITY_BASE/clkgen_50_shift.vhd"
}

if { $ARCHGRP == "FREQ_125" | $ARCHGRP == "FULL" } {
   set MOD "$MOD $ENTITY_BASE/clkgen_125_div.vhd"
   set MOD "$MOD $ENTITY_BASE/clkgen_125_shift.vhd"
}

