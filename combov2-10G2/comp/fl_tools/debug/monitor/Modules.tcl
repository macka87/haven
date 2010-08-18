# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2003 CESNET
# Author: Martinek Tomas <martinek@liberouter.org>
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

# Base directories
set COMP_BASE           "$ENTITY_BASE/../../.." 
set FL_BASE             "$COMP_BASE/fl_tools" 

set PACKAGES            "$COMP_BASE/base/pkg/math_pack.vhd \
                        $FL_BASE/pkg/fl_pkg.vhd         \
                        $COMP_BASE/ics/local_bus/pkg/lb_pkg.vhd"


set MOD "$MOD $ENTITY_BASE/monitor_ent.vhd"
set MOD "$MOD $ENTITY_BASE/monitor_arch_full.vhd"
set MOD "$MOD $ENTITY_BASE/top/monitor_top1.vhd"
set MOD "$MOD $ENTITY_BASE/top/monitor_top4.vhd"

