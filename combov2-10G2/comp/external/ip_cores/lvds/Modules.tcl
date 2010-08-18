# Modules.tcl: Local include tcl script
# Copyright (C) 2009 CESNET
# Author: Stepan Friedl <friedl@liberouter.org>
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

set MOD "$MOD $ENTITY_BASE/count_to_128.vhd"
set MOD "$MOD $ENTITY_BASE/count_to_16x.vhd"
set MOD "$MOD $ENTITY_BASE/COUNT_TO_64.vhd"
set MOD "$MOD $ENTITY_BASE/BIT_ALIGN_MACHINE.vhd"
set MOD "$MOD $ENTITY_BASE/RESOURCE_SHARING_CONTROL.vhd"
set MOD "$MOD $ENTITY_BASE/seven_bit_reg_w_ce.vhd"
set MOD "$MOD $ENTITY_BASE/DDR_8TO1_16CHAN_RX.vhd"
set MOD "$MOD $ENTITY_BASE/DDR_8TO1_16CHAN_TX.vhd"
