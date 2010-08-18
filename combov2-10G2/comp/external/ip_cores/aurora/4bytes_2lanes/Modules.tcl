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

# Aurora package
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/aurora_pkg.vhd]]"

# Aurora Lane Modules  
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/chbond_count_dec.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/error_detect.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/lane_init_sm.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/sym_dec.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/sym_gen.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/aurora_lane.vhd]]"

# Global Logic Modules
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/channel_error_detect.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/channel_init_sm.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/idle_and_ver_gen.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/global_logic.vhd]]" 

# TX LocalLink User Interface modules
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/tx_ll_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/tx_ll_datapath.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/tx_ll.vhd]]"

#RX_LL Pdu Modules
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/left_align_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/left_align_mux.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/output_mux.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/output_switch_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/rx_ll_deframer.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/sideband_output.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/storage_ce_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/storage_count_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/storage_mux.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/storage_switch_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/valid_data_counter.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/rx_ll_pdu_datapath.vhd]]"

#RX_LL NFC Modules
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/rx_ll_nfc.vhd]]"

#RX_LL UFC Modules
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_barrel_shifter.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_barrel_shifter_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_output_mux.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_output_switch_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_sideband_output.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_storage_count_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_storage_mux.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_storage_switch_control.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/rx_ll_ufc_datapath.vhd]]"
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/ufc_filter.vhd]]"

#RX_LL top level
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/rx_ll.vhd]]"

#Top Level Modules and wrappers
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/phase_align.vhd]]"    
set MOD "$MOD [list [list "aurora_4byte2lane" $ENTITY_BASE/aurora_4bytes_2lanes.vhd]]"

