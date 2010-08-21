# Modules.tcl: Local include Leonardo tcl script
# Copyright (C) 2005 CESNET
# Author: Vymazal Zbynek <vymazal at liberouter.org>
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

   set MOD "$MOD $ENTITY_BASE/aurora_pkg.vhd"
   set MOD "$MOD $ENTITY_BASE/aurora_lane.vhd"
   set MOD "$MOD $ENTITY_BASE/error_detect.vhd"
   set MOD "$MOD $ENTITY_BASE/global_logic.vhd"
   set MOD "$MOD $ENTITY_BASE/channel_error_detect.vhd"
   set MOD "$MOD $ENTITY_BASE/channel_init_sm.vhd"
   set MOD "$MOD $ENTITY_BASE/chbond_count_dec.vhd"
   set MOD "$MOD $ENTITY_BASE/idle_and_ver_gen.vhd"
   set MOD "$MOD $ENTITY_BASE/lane_init_sm.vhd"
   set MOD "$MOD $ENTITY_BASE/phase_align.vhd"
   set MOD "$MOD $ENTITY_BASE/sym_dec.vhd"
   set MOD "$MOD $ENTITY_BASE/sym_gen.vhd"
   set MOD "$MOD $ENTITY_BASE/rx_ll_pdu_datapath.vhd"
   set MOD "$MOD $ENTITY_BASE/rx_ll_ufc_datapath.vhd"
   set MOD "$MOD $ENTITY_BASE/ufc_filter.vhd"
   set MOD "$MOD $ENTITY_BASE/rx_ll.vhd"
   set MOD "$MOD $ENTITY_BASE/tx_ll_control.vhd"
   set MOD "$MOD $ENTITY_BASE/tx_ll_datapath.vhd"
   set MOD "$MOD $ENTITY_BASE/tx_ll.vhd"
   set MOD "$MOD $ENTITY_BASE/rio_aurora_module.vhd"




