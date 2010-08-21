# Modules.tcl: Local include tcl script
# Copyright (C) 2008 CESNET
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

set MOD "$MOD $ENTITY_BASE/qdrii_chipscope.vhd"            
set MOD "$MOD $ENTITY_BASE/qdrii_idelay_ctrl.vhd"          
set MOD "$MOD $ENTITY_BASE/qdrii_infrastructure.vhd"       
set MOD "$MOD $ENTITY_BASE/qdrii_phy_addr_io.vhd"          
set MOD "$MOD $ENTITY_BASE/qdrii_phy_bw_io.vhd"            
set MOD "$MOD $ENTITY_BASE/qdrii_phy_clk_io.vhd"           
set MOD "$MOD $ENTITY_BASE/qdrii_phy_cq_io.vhd"            
set MOD "$MOD $ENTITY_BASE/qdrii_phy_d_io.vhd"             
set MOD "$MOD $ENTITY_BASE/qdrii_phy_dly_cal_sm.vhd"       
set MOD "$MOD $ENTITY_BASE/qdrii_phy_en.vhd"               
set MOD "$MOD $ENTITY_BASE/qdrii_phy_init_sm.vhd"          
set MOD "$MOD $ENTITY_BASE/qdrii_phy_q_io.vhd"             
set MOD "$MOD $ENTITY_BASE/qdrii_phy_read.vhd"             
set MOD "$MOD $ENTITY_BASE/qdrii_phy_v5_q_io.vhd"          
set MOD "$MOD $ENTITY_BASE/qdrii_phy_write.vhd"            
set MOD "$MOD $ENTITY_BASE/qdrii_sram.vhd"                 
set MOD "$MOD $ENTITY_BASE/qdrii_top.vhd"                  
set MOD "$MOD $ENTITY_BASE/qdrii_top_ctrl_sm.vhd"          
set MOD "$MOD $ENTITY_BASE/qdrii_top_phy.vhd"              
set MOD "$MOD $ENTITY_BASE/qdrii_top_rd_addr_interface.vhd"
set MOD "$MOD $ENTITY_BASE/qdrii_top_rd_interface.vhd"     
set MOD "$MOD $ENTITY_BASE/qdrii_top_user_interface.vhd"   
set MOD "$MOD $ENTITY_BASE/qdrii_top_wr_addr_interface.vhd"
set MOD "$MOD $ENTITY_BASE/qdrii_top_wr_data_interface.vhd"
set MOD "$MOD $ENTITY_BASE/qdrii_top_wr_interface.vhd"     
set MOD "$MOD $ENTITY_BASE/qdrii_top_wrdata_bw_fifo.vhd"   
set MOD "$MOD $ENTITY_BASE/qdrii_top_wrdata_fifo.vhd"      
