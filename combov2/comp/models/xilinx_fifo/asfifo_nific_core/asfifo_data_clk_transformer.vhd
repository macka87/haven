--------------------------------------------------------------------------------
-- Copyright (c) 1995-2008 Xilinx, Inc.  All rights reserved.
--------------------------------------------------------------------------------
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor: Xilinx
-- \   \   \/     Version: K.39
--  \   \         Application: netgen
--  /   /         Filename: asfifo_data_clk_transformer.vhd
-- /___/   /\     Timestamp: Mon Mar  2 14:09:00 2009
-- \   \  /  \ 
--  \___\/\___\
--             
-- Command	: -intstyle ise -w -sim -ofmt vhdl /home/shared/dedekt1/tmp/_cg/asfifo_data_clk_transformer.ngc /home/shared/dedekt1/tmp/_cg/asfifo_data_clk_transformer.vhd 
-- Device	: 5vlx110tff1136-1
-- Input file	: /home/shared/dedekt1/tmp/_cg/asfifo_data_clk_transformer.ngc
-- Output file	: /home/shared/dedekt1/tmp/_cg/asfifo_data_clk_transformer.vhd
-- # of Entities	: 1
-- Design Name	: asfifo_data_clk_transformer
-- Xilinx	: /usr/local/fpga/xilinx101
--             
-- Purpose:    
--     This VHDL netlist is a verification model and uses simulation 
--     primitives which may not represent the true implementation of the 
--     device, however the netlist is functionally correct and should not 
--     be modified. This file cannot be synthesized and should only be used 
--     with supported simulation tools.
--             
-- Reference:  
--     Development System Reference Guide, Chapter 23
--     Synthesis and Simulation Design Guide, Chapter 6
--             
--------------------------------------------------------------------------------


-- synthesis translate_off
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
use UNISIM.VPKG.ALL;

entity asfifo_data_clk_transformer is
  port (
    rd_en : in STD_LOGIC := 'X'; 
    wr_en : in STD_LOGIC := 'X'; 
    full : out STD_LOGIC; 
    empty : out STD_LOGIC; 
    wr_clk : in STD_LOGIC := 'X'; 
    rst : in STD_LOGIC := 'X'; 
    rd_clk : in STD_LOGIC := 'X'; 
    dout : out STD_LOGIC_VECTOR ( 135 downto 0 ); 
    din : in STD_LOGIC_VECTOR ( 135 downto 0 ) 
  );
end asfifo_data_clk_transformer;

architecture STRUCTURE of asfifo_data_clk_transformer is
  signal BU2_N28 : STD_LOGIC; 
  signal BU2_N26 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000176_674 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126_673 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000086_672 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000176_671 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000126_670 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000086_669 : STD_LOGIC; 
  signal BU2_U0_grf_rf_ram_regout_en : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count6 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count3 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count9 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count12 : STD_LOGIC; 
  signal BU2_U0_grf_rf_ram_wr_en : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_fb_371 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_i_or0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0003 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0002 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0001 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0003 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0002 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0001 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0003 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0002 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0001 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0003 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0002 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0001 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count12 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count9 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count6 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count3 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_307 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_294 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_comb : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_comb : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_asreg_285 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_asreg_284 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2_283 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_282 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2_281 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_280 : STD_LOGIC; 
  signal NLW_VCC_P_UNCONNECTED : STD_LOGIC; 
  signal NLW_GND_G_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM234_SPO_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM233_SPO_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM232_SPO_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM231_SPO_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM22_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM22_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM20_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM20_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM19_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM19_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM21_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM21_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM17_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM17_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM16_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM16_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM18_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM18_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM14_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM14_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM13_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM13_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM15_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM15_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM11_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM11_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM10_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM10_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM12_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM12_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM8_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM8_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM7_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM7_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM9_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM9_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM5_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM5_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM4_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM4_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM6_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM6_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM2_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM2_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM1_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM1_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM3_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM3_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal din_2 : STD_LOGIC_VECTOR ( 135 downto 0 ); 
  signal dout_3 : STD_LOGIC_VECTOR ( 135 downto 0 ); 
  signal BU2_U0_grf_rf_mem_gdm_dm_dout_i : STD_LOGIC_VECTOR ( 135 downto 0 ); 
  signal BU2_U0_grf_rf_mem_gdm_dm_varindex0000 : STD_LOGIC_VECTOR ( 135 downto 0 ); 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_count_d2 : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_count_d1 : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_count : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state : STD_LOGIC_VECTOR ( 1 downto 0 ); 
  signal BU2_U0_grf_rf_gl0_rd_gr1_rfwft_next_fwft_state : STD_LOGIC_VECTOR ( 1 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1 : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1 : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_count_d1 : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_count : STD_LOGIC_VECTOR ( 4 downto 0 ); 
  signal BU2_U0_grf_rf_rstblk_wr_rst_reg : STD_LOGIC_VECTOR ( 1 downto 0 ); 
  signal BU2_U0_grf_rf_rstblk_rd_rst_reg : STD_LOGIC_VECTOR ( 2 downto 0 ); 
  signal BU2_rd_data_count : STD_LOGIC_VECTOR ( 0 downto 0 ); 
begin
  dout(135) <= dout_3(135);
  dout(134) <= dout_3(134);
  dout(133) <= dout_3(133);
  dout(132) <= dout_3(132);
  dout(131) <= dout_3(131);
  dout(130) <= dout_3(130);
  dout(129) <= dout_3(129);
  dout(128) <= dout_3(128);
  dout(127) <= dout_3(127);
  dout(126) <= dout_3(126);
  dout(125) <= dout_3(125);
  dout(124) <= dout_3(124);
  dout(123) <= dout_3(123);
  dout(122) <= dout_3(122);
  dout(121) <= dout_3(121);
  dout(120) <= dout_3(120);
  dout(119) <= dout_3(119);
  dout(118) <= dout_3(118);
  dout(117) <= dout_3(117);
  dout(116) <= dout_3(116);
  dout(115) <= dout_3(115);
  dout(114) <= dout_3(114);
  dout(113) <= dout_3(113);
  dout(112) <= dout_3(112);
  dout(111) <= dout_3(111);
  dout(110) <= dout_3(110);
  dout(109) <= dout_3(109);
  dout(108) <= dout_3(108);
  dout(107) <= dout_3(107);
  dout(106) <= dout_3(106);
  dout(105) <= dout_3(105);
  dout(104) <= dout_3(104);
  dout(103) <= dout_3(103);
  dout(102) <= dout_3(102);
  dout(101) <= dout_3(101);
  dout(100) <= dout_3(100);
  dout(99) <= dout_3(99);
  dout(98) <= dout_3(98);
  dout(97) <= dout_3(97);
  dout(96) <= dout_3(96);
  dout(95) <= dout_3(95);
  dout(94) <= dout_3(94);
  dout(93) <= dout_3(93);
  dout(92) <= dout_3(92);
  dout(91) <= dout_3(91);
  dout(90) <= dout_3(90);
  dout(89) <= dout_3(89);
  dout(88) <= dout_3(88);
  dout(87) <= dout_3(87);
  dout(86) <= dout_3(86);
  dout(85) <= dout_3(85);
  dout(84) <= dout_3(84);
  dout(83) <= dout_3(83);
  dout(82) <= dout_3(82);
  dout(81) <= dout_3(81);
  dout(80) <= dout_3(80);
  dout(79) <= dout_3(79);
  dout(78) <= dout_3(78);
  dout(77) <= dout_3(77);
  dout(76) <= dout_3(76);
  dout(75) <= dout_3(75);
  dout(74) <= dout_3(74);
  dout(73) <= dout_3(73);
  dout(72) <= dout_3(72);
  dout(71) <= dout_3(71);
  dout(70) <= dout_3(70);
  dout(69) <= dout_3(69);
  dout(68) <= dout_3(68);
  dout(67) <= dout_3(67);
  dout(66) <= dout_3(66);
  dout(65) <= dout_3(65);
  dout(64) <= dout_3(64);
  dout(63) <= dout_3(63);
  dout(62) <= dout_3(62);
  dout(61) <= dout_3(61);
  dout(60) <= dout_3(60);
  dout(59) <= dout_3(59);
  dout(58) <= dout_3(58);
  dout(57) <= dout_3(57);
  dout(56) <= dout_3(56);
  dout(55) <= dout_3(55);
  dout(54) <= dout_3(54);
  dout(53) <= dout_3(53);
  dout(52) <= dout_3(52);
  dout(51) <= dout_3(51);
  dout(50) <= dout_3(50);
  dout(49) <= dout_3(49);
  dout(48) <= dout_3(48);
  dout(47) <= dout_3(47);
  dout(46) <= dout_3(46);
  dout(45) <= dout_3(45);
  dout(44) <= dout_3(44);
  dout(43) <= dout_3(43);
  dout(42) <= dout_3(42);
  dout(41) <= dout_3(41);
  dout(40) <= dout_3(40);
  dout(39) <= dout_3(39);
  dout(38) <= dout_3(38);
  dout(37) <= dout_3(37);
  dout(36) <= dout_3(36);
  dout(35) <= dout_3(35);
  dout(34) <= dout_3(34);
  dout(33) <= dout_3(33);
  dout(32) <= dout_3(32);
  dout(31) <= dout_3(31);
  dout(30) <= dout_3(30);
  dout(29) <= dout_3(29);
  dout(28) <= dout_3(28);
  dout(27) <= dout_3(27);
  dout(26) <= dout_3(26);
  dout(25) <= dout_3(25);
  dout(24) <= dout_3(24);
  dout(23) <= dout_3(23);
  dout(22) <= dout_3(22);
  dout(21) <= dout_3(21);
  dout(20) <= dout_3(20);
  dout(19) <= dout_3(19);
  dout(18) <= dout_3(18);
  dout(17) <= dout_3(17);
  dout(16) <= dout_3(16);
  dout(15) <= dout_3(15);
  dout(14) <= dout_3(14);
  dout(13) <= dout_3(13);
  dout(12) <= dout_3(12);
  dout(11) <= dout_3(11);
  dout(10) <= dout_3(10);
  dout(9) <= dout_3(9);
  dout(8) <= dout_3(8);
  dout(7) <= dout_3(7);
  dout(6) <= dout_3(6);
  dout(5) <= dout_3(5);
  dout(4) <= dout_3(4);
  dout(3) <= dout_3(3);
  dout(2) <= dout_3(2);
  dout(1) <= dout_3(1);
  dout(0) <= dout_3(0);
  din_2(135) <= din(135);
  din_2(134) <= din(134);
  din_2(133) <= din(133);
  din_2(132) <= din(132);
  din_2(131) <= din(131);
  din_2(130) <= din(130);
  din_2(129) <= din(129);
  din_2(128) <= din(128);
  din_2(127) <= din(127);
  din_2(126) <= din(126);
  din_2(125) <= din(125);
  din_2(124) <= din(124);
  din_2(123) <= din(123);
  din_2(122) <= din(122);
  din_2(121) <= din(121);
  din_2(120) <= din(120);
  din_2(119) <= din(119);
  din_2(118) <= din(118);
  din_2(117) <= din(117);
  din_2(116) <= din(116);
  din_2(115) <= din(115);
  din_2(114) <= din(114);
  din_2(113) <= din(113);
  din_2(112) <= din(112);
  din_2(111) <= din(111);
  din_2(110) <= din(110);
  din_2(109) <= din(109);
  din_2(108) <= din(108);
  din_2(107) <= din(107);
  din_2(106) <= din(106);
  din_2(105) <= din(105);
  din_2(104) <= din(104);
  din_2(103) <= din(103);
  din_2(102) <= din(102);
  din_2(101) <= din(101);
  din_2(100) <= din(100);
  din_2(99) <= din(99);
  din_2(98) <= din(98);
  din_2(97) <= din(97);
  din_2(96) <= din(96);
  din_2(95) <= din(95);
  din_2(94) <= din(94);
  din_2(93) <= din(93);
  din_2(92) <= din(92);
  din_2(91) <= din(91);
  din_2(90) <= din(90);
  din_2(89) <= din(89);
  din_2(88) <= din(88);
  din_2(87) <= din(87);
  din_2(86) <= din(86);
  din_2(85) <= din(85);
  din_2(84) <= din(84);
  din_2(83) <= din(83);
  din_2(82) <= din(82);
  din_2(81) <= din(81);
  din_2(80) <= din(80);
  din_2(79) <= din(79);
  din_2(78) <= din(78);
  din_2(77) <= din(77);
  din_2(76) <= din(76);
  din_2(75) <= din(75);
  din_2(74) <= din(74);
  din_2(73) <= din(73);
  din_2(72) <= din(72);
  din_2(71) <= din(71);
  din_2(70) <= din(70);
  din_2(69) <= din(69);
  din_2(68) <= din(68);
  din_2(67) <= din(67);
  din_2(66) <= din(66);
  din_2(65) <= din(65);
  din_2(64) <= din(64);
  din_2(63) <= din(63);
  din_2(62) <= din(62);
  din_2(61) <= din(61);
  din_2(60) <= din(60);
  din_2(59) <= din(59);
  din_2(58) <= din(58);
  din_2(57) <= din(57);
  din_2(56) <= din(56);
  din_2(55) <= din(55);
  din_2(54) <= din(54);
  din_2(53) <= din(53);
  din_2(52) <= din(52);
  din_2(51) <= din(51);
  din_2(50) <= din(50);
  din_2(49) <= din(49);
  din_2(48) <= din(48);
  din_2(47) <= din(47);
  din_2(46) <= din(46);
  din_2(45) <= din(45);
  din_2(44) <= din(44);
  din_2(43) <= din(43);
  din_2(42) <= din(42);
  din_2(41) <= din(41);
  din_2(40) <= din(40);
  din_2(39) <= din(39);
  din_2(38) <= din(38);
  din_2(37) <= din(37);
  din_2(36) <= din(36);
  din_2(35) <= din(35);
  din_2(34) <= din(34);
  din_2(33) <= din(33);
  din_2(32) <= din(32);
  din_2(31) <= din(31);
  din_2(30) <= din(30);
  din_2(29) <= din(29);
  din_2(28) <= din(28);
  din_2(27) <= din(27);
  din_2(26) <= din(26);
  din_2(25) <= din(25);
  din_2(24) <= din(24);
  din_2(23) <= din(23);
  din_2(22) <= din(22);
  din_2(21) <= din(21);
  din_2(20) <= din(20);
  din_2(19) <= din(19);
  din_2(18) <= din(18);
  din_2(17) <= din(17);
  din_2(16) <= din(16);
  din_2(15) <= din(15);
  din_2(14) <= din(14);
  din_2(13) <= din(13);
  din_2(12) <= din(12);
  din_2(11) <= din(11);
  din_2(10) <= din(10);
  din_2(9) <= din(9);
  din_2(8) <= din(8);
  din_2(7) <= din(7);
  din_2(6) <= din(6);
  din_2(5) <= din(5);
  din_2(4) <= din(4);
  din_2(3) <= din(3);
  din_2(2) <= din(2);
  din_2(1) <= din(1);
  din_2(0) <= din(0);
  VCC_0 : VCC
    port map (
      P => NLW_VCC_P_UNCONNECTED
    );
  GND_1 : GND
    port map (
      G => NLW_GND_G_UNCONNECTED
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count_xor_0_11_INV_0 : INV
    port map (
      I => BU2_U0_grf_rf_gl0_rd_rpntr_count(0),
      O => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count_xor_0_11_INV_0 : INV
    port map (
      I => BU2_U0_grf_rf_gl0_wr_wpntr_count(0),
      O => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count
    );
  BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000192 : LUT6
    generic map(
      INIT => X"F2F02200F0F00000"
    )
    port map (
      I0 => wr_en,
      I1 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_307,
      I2 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000126_670,
      I3 => BU2_N26,
      I4 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000176_671,
      I5 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000086_669,
      O => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_bin_xor0003_Result1 : LUT5
    generic map(
      INIT => X"96696996"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(4),
      I2 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(2),
      I3 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(1),
      I4 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(0),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0003
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_bin_xor0003_Result1 : LUT5
    generic map(
      INIT => X"96696996"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(4),
      I2 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(2),
      I3 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(1),
      I4 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(0),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0003
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_bin_xor0002_Result1 : LUT4
    generic map(
      INIT => X"6996"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(4),
      I2 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(2),
      I3 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(1),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0002
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_bin_xor0002_Result1 : LUT4
    generic map(
      INIT => X"6996"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(4),
      I2 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(2),
      I3 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(1),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0002
    );
  BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000192 : LUT5
    generic map(
      INIT => X"EAC0AA00"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126_673,
      I1 => BU2_N28,
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      I3 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000176_674,
      I4 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000086_672,
      O => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000
    );
  BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000036_SW0 : LUT4
    generic map(
      INIT => X"8241"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(0),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(1),
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count(1),
      I3 => BU2_U0_grf_rf_gl0_rd_rpntr_count(0),
      O => BU2_N28
    );
  BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000036_SW0 : LUT4
    generic map(
      INIT => X"8241"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(0),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(1),
      I2 => BU2_U0_grf_rf_gl0_wr_wpntr_count(1),
      I3 => BU2_U0_grf_rf_gl0_wr_wpntr_count(0),
      O => BU2_N26
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_bin_xor0001_Result1 : LUT3
    generic map(
      INIT => X"96"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(4),
      I2 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(2),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0001
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_bin_xor0001_Result1 : LUT3
    generic map(
      INIT => X"96"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(4),
      I2 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(2),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0001
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_bin_xor0000_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(4),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0000
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_bin_xor0000_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(4),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0000
    );
  BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000176 : LUT6
    generic map(
      INIT => X"8040201008040201"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(1),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(2),
      I2 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(3),
      I3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      I4 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      I5 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      O => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000176_674
    );
  BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126 : LUT4
    generic map(
      INIT => X"8421"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(4),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(0),
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      I3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      O => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126_673
    );
  BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000086 : LUT6
    generic map(
      INIT => X"9009000000009009"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count(4),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(4),
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count(3),
      I3 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(3),
      I4 => BU2_U0_grf_rf_gl0_rd_rpntr_count(2),
      I5 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(2),
      O => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000086_672
    );
  BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000176 : LUT6
    generic map(
      INIT => X"9009000000009009"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(3),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(3),
      I2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(2),
      I3 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(2),
      I4 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(1),
      I5 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(1),
      O => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000176_671
    );
  BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000126 : LUT4
    generic map(
      INIT => X"9009"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(0),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(0),
      I2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(4),
      I3 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(4),
      O => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000126_670
    );
  BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000086 : LUT6
    generic map(
      INIT => X"9009000000009009"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count(4),
      I1 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(4),
      I2 => BU2_U0_grf_rf_gl0_wr_wpntr_count(3),
      I3 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(3),
      I4 => BU2_U0_grf_rf_gl0_wr_wpntr_count(2),
      I5 => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(2),
      O => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000086_669
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_RAM_RD_EN_FWFT1 : LUT4
    generic map(
      INIT => X"2333"
    )
    port map (
      I0 => rd_en,
      I1 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_294,
      I2 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(1),
      I3 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(0),
      O => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001
    );
  BU2_U0_grf_rf_gl0_wr_ram_wr_en_i1 : LUT2
    generic map(
      INIT => X"2"
    )
    port map (
      I0 => wr_en,
      I1 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_307,
      O => BU2_U0_grf_rf_ram_wr_en
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_RAM_REGOUT_EN1 : LUT3
    generic map(
      INIT => X"B0"
    )
    port map (
      I0 => rd_en,
      I1 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(0),
      I2 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(1),
      O => BU2_U0_grf_rf_ram_regout_en
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count_xor_4_11 : LUT5
    generic map(
      INIT => X"6CCCCCCC"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count(0),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count(4),
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count(1),
      I3 => BU2_U0_grf_rf_gl0_rd_rpntr_count(2),
      I4 => BU2_U0_grf_rf_gl0_rd_rpntr_count(3),
      O => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count12
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count_xor_4_11 : LUT5
    generic map(
      INIT => X"6CCCCCCC"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count(0),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count(4),
      I2 => BU2_U0_grf_rf_gl0_wr_wpntr_count(3),
      I3 => BU2_U0_grf_rf_gl0_wr_wpntr_count(1),
      I4 => BU2_U0_grf_rf_gl0_wr_wpntr_count(2),
      O => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count12
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count_xor_3_11 : LUT4
    generic map(
      INIT => X"6CCC"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count(0),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count(3),
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count(1),
      I3 => BU2_U0_grf_rf_gl0_rd_rpntr_count(2),
      O => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count9
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count_xor_3_11 : LUT4
    generic map(
      INIT => X"6CCC"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count(0),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count(3),
      I2 => BU2_U0_grf_rf_gl0_wr_wpntr_count(1),
      I3 => BU2_U0_grf_rf_gl0_wr_wpntr_count(2),
      O => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count9
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_i_or00001 : LUT4
    generic map(
      INIT => X"8E8A"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_fb_371,
      I1 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(0),
      I2 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(1),
      I3 => rd_en,
      O => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_i_or0000
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_next_fwft_state_1_1 : LUT4
    generic map(
      INIT => X"5D55"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_294,
      I1 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(0),
      I2 => rd_en,
      I3 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(1),
      O => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_next_fwft_state(1)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count_xor_2_11 : LUT3
    generic map(
      INIT => X"6C"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count(0),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count(2),
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count(1),
      O => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count6
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count_xor_2_11 : LUT3
    generic map(
      INIT => X"6C"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count(0),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count(2),
      I2 => BU2_U0_grf_rf_gl0_wr_wpntr_count(1),
      O => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count6
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_next_fwft_state_0_1 : LUT3
    generic map(
      INIT => X"BA"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(1),
      I1 => rd_en,
      I2 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(0),
      O => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_next_fwft_state(0)
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_gc_xor0000_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0000
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_gc_xor0001_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0001
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_gc_xor0002_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0002
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_rd_pntr_gc_xor0003_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      O => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0003
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_gc_xor0000_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0000
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_gc_xor0001_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0001
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_gc_xor0002_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0002
    );
  BU2_U0_grf_rf_gcx_clkx_Mxor_wr_pntr_gc_xor0003_Result1 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      O => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0003
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count_xor_1_11 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_rpntr_count(1),
      I1 => BU2_U0_grf_rf_gl0_rd_rpntr_count(0),
      O => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count3
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count_xor_1_11 : LUT2
    generic map(
      INIT => X"6"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_wr_wpntr_count(1),
      I1 => BU2_U0_grf_rf_gl0_wr_wpntr_count(0),
      O => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count3
    );
  BU2_U0_grf_rf_rstblk_rd_rst_comb1 : LUT2
    generic map(
      INIT => X"4"
    )
    port map (
      I0 => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2_281,
      I1 => BU2_U0_grf_rf_rstblk_rd_rst_asreg_284,
      O => BU2_U0_grf_rf_rstblk_rd_rst_comb
    );
  BU2_U0_grf_rf_rstblk_wr_rst_comb1 : LUT2
    generic map(
      INIT => X"4"
    )
    port map (
      I0 => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2_283,
      I1 => BU2_U0_grf_rf_rstblk_wr_rst_asreg_285,
      O => BU2_U0_grf_rf_rstblk_wr_rst_comb
    );
  BU2_U0_grf_rf_mem_dout_i_0 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(0),
      Q => dout_3(0)
    );
  BU2_U0_grf_rf_mem_dout_i_1 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(1),
      Q => dout_3(1)
    );
  BU2_U0_grf_rf_mem_dout_i_2 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(2),
      Q => dout_3(2)
    );
  BU2_U0_grf_rf_mem_dout_i_3 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(3),
      Q => dout_3(3)
    );
  BU2_U0_grf_rf_mem_dout_i_4 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(4),
      Q => dout_3(4)
    );
  BU2_U0_grf_rf_mem_dout_i_5 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(5),
      Q => dout_3(5)
    );
  BU2_U0_grf_rf_mem_dout_i_6 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(6),
      Q => dout_3(6)
    );
  BU2_U0_grf_rf_mem_dout_i_7 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(7),
      Q => dout_3(7)
    );
  BU2_U0_grf_rf_mem_dout_i_8 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(8),
      Q => dout_3(8)
    );
  BU2_U0_grf_rf_mem_dout_i_9 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(9),
      Q => dout_3(9)
    );
  BU2_U0_grf_rf_mem_dout_i_10 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(10),
      Q => dout_3(10)
    );
  BU2_U0_grf_rf_mem_dout_i_11 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(11),
      Q => dout_3(11)
    );
  BU2_U0_grf_rf_mem_dout_i_12 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(12),
      Q => dout_3(12)
    );
  BU2_U0_grf_rf_mem_dout_i_13 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(13),
      Q => dout_3(13)
    );
  BU2_U0_grf_rf_mem_dout_i_14 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(14),
      Q => dout_3(14)
    );
  BU2_U0_grf_rf_mem_dout_i_15 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(15),
      Q => dout_3(15)
    );
  BU2_U0_grf_rf_mem_dout_i_16 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(16),
      Q => dout_3(16)
    );
  BU2_U0_grf_rf_mem_dout_i_17 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(17),
      Q => dout_3(17)
    );
  BU2_U0_grf_rf_mem_dout_i_18 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(18),
      Q => dout_3(18)
    );
  BU2_U0_grf_rf_mem_dout_i_19 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(19),
      Q => dout_3(19)
    );
  BU2_U0_grf_rf_mem_dout_i_20 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(20),
      Q => dout_3(20)
    );
  BU2_U0_grf_rf_mem_dout_i_21 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(21),
      Q => dout_3(21)
    );
  BU2_U0_grf_rf_mem_dout_i_22 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(22),
      Q => dout_3(22)
    );
  BU2_U0_grf_rf_mem_dout_i_23 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(23),
      Q => dout_3(23)
    );
  BU2_U0_grf_rf_mem_dout_i_24 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(24),
      Q => dout_3(24)
    );
  BU2_U0_grf_rf_mem_dout_i_25 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(25),
      Q => dout_3(25)
    );
  BU2_U0_grf_rf_mem_dout_i_26 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(26),
      Q => dout_3(26)
    );
  BU2_U0_grf_rf_mem_dout_i_27 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(27),
      Q => dout_3(27)
    );
  BU2_U0_grf_rf_mem_dout_i_28 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(28),
      Q => dout_3(28)
    );
  BU2_U0_grf_rf_mem_dout_i_29 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(29),
      Q => dout_3(29)
    );
  BU2_U0_grf_rf_mem_dout_i_30 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(30),
      Q => dout_3(30)
    );
  BU2_U0_grf_rf_mem_dout_i_31 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(31),
      Q => dout_3(31)
    );
  BU2_U0_grf_rf_mem_dout_i_32 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(32),
      Q => dout_3(32)
    );
  BU2_U0_grf_rf_mem_dout_i_33 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(33),
      Q => dout_3(33)
    );
  BU2_U0_grf_rf_mem_dout_i_34 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(34),
      Q => dout_3(34)
    );
  BU2_U0_grf_rf_mem_dout_i_35 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(35),
      Q => dout_3(35)
    );
  BU2_U0_grf_rf_mem_dout_i_36 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(36),
      Q => dout_3(36)
    );
  BU2_U0_grf_rf_mem_dout_i_37 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(37),
      Q => dout_3(37)
    );
  BU2_U0_grf_rf_mem_dout_i_38 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(38),
      Q => dout_3(38)
    );
  BU2_U0_grf_rf_mem_dout_i_39 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(39),
      Q => dout_3(39)
    );
  BU2_U0_grf_rf_mem_dout_i_40 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(40),
      Q => dout_3(40)
    );
  BU2_U0_grf_rf_mem_dout_i_41 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(41),
      Q => dout_3(41)
    );
  BU2_U0_grf_rf_mem_dout_i_42 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(42),
      Q => dout_3(42)
    );
  BU2_U0_grf_rf_mem_dout_i_43 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(43),
      Q => dout_3(43)
    );
  BU2_U0_grf_rf_mem_dout_i_44 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(44),
      Q => dout_3(44)
    );
  BU2_U0_grf_rf_mem_dout_i_45 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(45),
      Q => dout_3(45)
    );
  BU2_U0_grf_rf_mem_dout_i_46 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(46),
      Q => dout_3(46)
    );
  BU2_U0_grf_rf_mem_dout_i_47 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(47),
      Q => dout_3(47)
    );
  BU2_U0_grf_rf_mem_dout_i_48 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(48),
      Q => dout_3(48)
    );
  BU2_U0_grf_rf_mem_dout_i_49 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(49),
      Q => dout_3(49)
    );
  BU2_U0_grf_rf_mem_dout_i_50 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(50),
      Q => dout_3(50)
    );
  BU2_U0_grf_rf_mem_dout_i_51 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(51),
      Q => dout_3(51)
    );
  BU2_U0_grf_rf_mem_dout_i_52 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(52),
      Q => dout_3(52)
    );
  BU2_U0_grf_rf_mem_dout_i_53 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(53),
      Q => dout_3(53)
    );
  BU2_U0_grf_rf_mem_dout_i_54 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(54),
      Q => dout_3(54)
    );
  BU2_U0_grf_rf_mem_dout_i_55 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(55),
      Q => dout_3(55)
    );
  BU2_U0_grf_rf_mem_dout_i_56 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(56),
      Q => dout_3(56)
    );
  BU2_U0_grf_rf_mem_dout_i_57 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(57),
      Q => dout_3(57)
    );
  BU2_U0_grf_rf_mem_dout_i_58 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(58),
      Q => dout_3(58)
    );
  BU2_U0_grf_rf_mem_dout_i_59 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(59),
      Q => dout_3(59)
    );
  BU2_U0_grf_rf_mem_dout_i_60 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(60),
      Q => dout_3(60)
    );
  BU2_U0_grf_rf_mem_dout_i_61 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(61),
      Q => dout_3(61)
    );
  BU2_U0_grf_rf_mem_dout_i_62 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(62),
      Q => dout_3(62)
    );
  BU2_U0_grf_rf_mem_dout_i_63 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(63),
      Q => dout_3(63)
    );
  BU2_U0_grf_rf_mem_dout_i_64 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(64),
      Q => dout_3(64)
    );
  BU2_U0_grf_rf_mem_dout_i_65 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(65),
      Q => dout_3(65)
    );
  BU2_U0_grf_rf_mem_dout_i_66 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(66),
      Q => dout_3(66)
    );
  BU2_U0_grf_rf_mem_dout_i_67 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(67),
      Q => dout_3(67)
    );
  BU2_U0_grf_rf_mem_dout_i_68 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(68),
      Q => dout_3(68)
    );
  BU2_U0_grf_rf_mem_dout_i_69 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(69),
      Q => dout_3(69)
    );
  BU2_U0_grf_rf_mem_dout_i_70 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(70),
      Q => dout_3(70)
    );
  BU2_U0_grf_rf_mem_dout_i_71 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(71),
      Q => dout_3(71)
    );
  BU2_U0_grf_rf_mem_dout_i_72 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(72),
      Q => dout_3(72)
    );
  BU2_U0_grf_rf_mem_dout_i_73 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(73),
      Q => dout_3(73)
    );
  BU2_U0_grf_rf_mem_dout_i_74 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(74),
      Q => dout_3(74)
    );
  BU2_U0_grf_rf_mem_dout_i_75 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(75),
      Q => dout_3(75)
    );
  BU2_U0_grf_rf_mem_dout_i_76 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(76),
      Q => dout_3(76)
    );
  BU2_U0_grf_rf_mem_dout_i_77 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(77),
      Q => dout_3(77)
    );
  BU2_U0_grf_rf_mem_dout_i_78 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(78),
      Q => dout_3(78)
    );
  BU2_U0_grf_rf_mem_dout_i_79 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(79),
      Q => dout_3(79)
    );
  BU2_U0_grf_rf_mem_dout_i_80 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(80),
      Q => dout_3(80)
    );
  BU2_U0_grf_rf_mem_dout_i_81 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(81),
      Q => dout_3(81)
    );
  BU2_U0_grf_rf_mem_dout_i_82 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(82),
      Q => dout_3(82)
    );
  BU2_U0_grf_rf_mem_dout_i_83 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(83),
      Q => dout_3(83)
    );
  BU2_U0_grf_rf_mem_dout_i_84 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(84),
      Q => dout_3(84)
    );
  BU2_U0_grf_rf_mem_dout_i_85 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(85),
      Q => dout_3(85)
    );
  BU2_U0_grf_rf_mem_dout_i_86 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(86),
      Q => dout_3(86)
    );
  BU2_U0_grf_rf_mem_dout_i_87 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(87),
      Q => dout_3(87)
    );
  BU2_U0_grf_rf_mem_dout_i_88 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(88),
      Q => dout_3(88)
    );
  BU2_U0_grf_rf_mem_dout_i_89 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(89),
      Q => dout_3(89)
    );
  BU2_U0_grf_rf_mem_dout_i_90 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(90),
      Q => dout_3(90)
    );
  BU2_U0_grf_rf_mem_dout_i_91 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(91),
      Q => dout_3(91)
    );
  BU2_U0_grf_rf_mem_dout_i_92 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(92),
      Q => dout_3(92)
    );
  BU2_U0_grf_rf_mem_dout_i_93 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(93),
      Q => dout_3(93)
    );
  BU2_U0_grf_rf_mem_dout_i_94 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(94),
      Q => dout_3(94)
    );
  BU2_U0_grf_rf_mem_dout_i_95 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(95),
      Q => dout_3(95)
    );
  BU2_U0_grf_rf_mem_dout_i_96 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(96),
      Q => dout_3(96)
    );
  BU2_U0_grf_rf_mem_dout_i_97 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(97),
      Q => dout_3(97)
    );
  BU2_U0_grf_rf_mem_dout_i_98 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(98),
      Q => dout_3(98)
    );
  BU2_U0_grf_rf_mem_dout_i_99 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(99),
      Q => dout_3(99)
    );
  BU2_U0_grf_rf_mem_dout_i_100 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(100),
      Q => dout_3(100)
    );
  BU2_U0_grf_rf_mem_dout_i_101 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(101),
      Q => dout_3(101)
    );
  BU2_U0_grf_rf_mem_dout_i_102 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(102),
      Q => dout_3(102)
    );
  BU2_U0_grf_rf_mem_dout_i_103 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(103),
      Q => dout_3(103)
    );
  BU2_U0_grf_rf_mem_dout_i_104 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(104),
      Q => dout_3(104)
    );
  BU2_U0_grf_rf_mem_dout_i_105 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(105),
      Q => dout_3(105)
    );
  BU2_U0_grf_rf_mem_dout_i_106 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(106),
      Q => dout_3(106)
    );
  BU2_U0_grf_rf_mem_dout_i_107 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(107),
      Q => dout_3(107)
    );
  BU2_U0_grf_rf_mem_dout_i_108 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(108),
      Q => dout_3(108)
    );
  BU2_U0_grf_rf_mem_dout_i_109 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(109),
      Q => dout_3(109)
    );
  BU2_U0_grf_rf_mem_dout_i_110 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(110),
      Q => dout_3(110)
    );
  BU2_U0_grf_rf_mem_dout_i_111 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(111),
      Q => dout_3(111)
    );
  BU2_U0_grf_rf_mem_dout_i_112 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(112),
      Q => dout_3(112)
    );
  BU2_U0_grf_rf_mem_dout_i_113 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(113),
      Q => dout_3(113)
    );
  BU2_U0_grf_rf_mem_dout_i_114 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(114),
      Q => dout_3(114)
    );
  BU2_U0_grf_rf_mem_dout_i_115 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(115),
      Q => dout_3(115)
    );
  BU2_U0_grf_rf_mem_dout_i_116 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(116),
      Q => dout_3(116)
    );
  BU2_U0_grf_rf_mem_dout_i_117 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(117),
      Q => dout_3(117)
    );
  BU2_U0_grf_rf_mem_dout_i_118 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(118),
      Q => dout_3(118)
    );
  BU2_U0_grf_rf_mem_dout_i_119 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(119),
      Q => dout_3(119)
    );
  BU2_U0_grf_rf_mem_dout_i_120 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(120),
      Q => dout_3(120)
    );
  BU2_U0_grf_rf_mem_dout_i_121 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(121),
      Q => dout_3(121)
    );
  BU2_U0_grf_rf_mem_dout_i_122 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(122),
      Q => dout_3(122)
    );
  BU2_U0_grf_rf_mem_dout_i_123 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(123),
      Q => dout_3(123)
    );
  BU2_U0_grf_rf_mem_dout_i_124 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(124),
      Q => dout_3(124)
    );
  BU2_U0_grf_rf_mem_dout_i_125 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(125),
      Q => dout_3(125)
    );
  BU2_U0_grf_rf_mem_dout_i_126 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(126),
      Q => dout_3(126)
    );
  BU2_U0_grf_rf_mem_dout_i_127 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(127),
      Q => dout_3(127)
    );
  BU2_U0_grf_rf_mem_dout_i_128 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(128),
      Q => dout_3(128)
    );
  BU2_U0_grf_rf_mem_dout_i_129 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(129),
      Q => dout_3(129)
    );
  BU2_U0_grf_rf_mem_dout_i_130 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(130),
      Q => dout_3(130)
    );
  BU2_U0_grf_rf_mem_dout_i_131 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(131),
      Q => dout_3(131)
    );
  BU2_U0_grf_rf_mem_dout_i_132 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(132),
      Q => dout_3(132)
    );
  BU2_U0_grf_rf_mem_dout_i_133 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(133),
      Q => dout_3(133)
    );
  BU2_U0_grf_rf_mem_dout_i_134 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(134),
      Q => dout_3(134)
    );
  BU2_U0_grf_rf_mem_dout_i_135 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_ram_regout_en,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_dout_i(135),
      Q => dout_3(135)
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM234 : RAM32X1D
    port map (
      A0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      A1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      A2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      A3 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      A4 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      D => din_2(135),
      DPRA0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      DPRA1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      DPRA2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      DPRA3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      DPRA4 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      SPO => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM234_SPO_UNCONNECTED,
      DPO => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(135)
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM233 : RAM32X1D
    port map (
      A0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      A1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      A2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      A3 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      A4 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      D => din_2(134),
      DPRA0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      DPRA1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      DPRA2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      DPRA3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      DPRA4 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      SPO => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM233_SPO_UNCONNECTED,
      DPO => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(134)
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM232 : RAM32X1D
    port map (
      A0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      A1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      A2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      A3 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      A4 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      D => din_2(133),
      DPRA0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      DPRA1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      DPRA2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      DPRA3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      DPRA4 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      SPO => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM232_SPO_UNCONNECTED,
      DPO => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(133)
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM231 : RAM32X1D
    port map (
      A0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      A1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      A2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      A3 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      A4 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      D => din_2(132),
      DPRA0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      DPRA1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      DPRA2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      DPRA3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      DPRA4 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      SPO => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM231_SPO_UNCONNECTED,
      DPO => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(132)
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM22 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(127),
      DIA(0) => din_2(126),
      DIB(1) => din_2(129),
      DIB(0) => din_2(128),
      DIC(1) => din_2(131),
      DIC(0) => din_2(130),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(127),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(126),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(129),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(128),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(131),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(130),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM22_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM22_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM20 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(115),
      DIA(0) => din_2(114),
      DIB(1) => din_2(117),
      DIB(0) => din_2(116),
      DIC(1) => din_2(119),
      DIC(0) => din_2(118),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(115),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(114),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(117),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(116),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(119),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(118),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM20_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM20_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM19 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(109),
      DIA(0) => din_2(108),
      DIB(1) => din_2(111),
      DIB(0) => din_2(110),
      DIC(1) => din_2(113),
      DIC(0) => din_2(112),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(109),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(108),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(111),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(110),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(113),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(112),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM19_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM19_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM21 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(121),
      DIA(0) => din_2(120),
      DIB(1) => din_2(123),
      DIB(0) => din_2(122),
      DIC(1) => din_2(125),
      DIC(0) => din_2(124),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(121),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(120),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(123),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(122),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(125),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(124),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM21_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM21_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM17 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(97),
      DIA(0) => din_2(96),
      DIB(1) => din_2(99),
      DIB(0) => din_2(98),
      DIC(1) => din_2(101),
      DIC(0) => din_2(100),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(97),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(96),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(99),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(98),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(101),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(100),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM17_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM17_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM16 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(91),
      DIA(0) => din_2(90),
      DIB(1) => din_2(93),
      DIB(0) => din_2(92),
      DIC(1) => din_2(95),
      DIC(0) => din_2(94),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(91),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(90),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(93),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(92),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(95),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(94),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM16_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM16_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM18 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(103),
      DIA(0) => din_2(102),
      DIB(1) => din_2(105),
      DIB(0) => din_2(104),
      DIC(1) => din_2(107),
      DIC(0) => din_2(106),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(103),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(102),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(105),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(104),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(107),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(106),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM18_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM18_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM14 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(79),
      DIA(0) => din_2(78),
      DIB(1) => din_2(81),
      DIB(0) => din_2(80),
      DIC(1) => din_2(83),
      DIC(0) => din_2(82),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(79),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(78),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(81),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(80),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(83),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(82),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM14_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM14_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM13 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(73),
      DIA(0) => din_2(72),
      DIB(1) => din_2(75),
      DIB(0) => din_2(74),
      DIC(1) => din_2(77),
      DIC(0) => din_2(76),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(73),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(72),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(75),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(74),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(77),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(76),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM13_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM13_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM15 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(85),
      DIA(0) => din_2(84),
      DIB(1) => din_2(87),
      DIB(0) => din_2(86),
      DIC(1) => din_2(89),
      DIC(0) => din_2(88),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(85),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(84),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(87),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(86),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(89),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(88),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM15_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM15_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM11 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(61),
      DIA(0) => din_2(60),
      DIB(1) => din_2(63),
      DIB(0) => din_2(62),
      DIC(1) => din_2(65),
      DIC(0) => din_2(64),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(61),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(60),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(63),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(62),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(65),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(64),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM11_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM11_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM10 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(55),
      DIA(0) => din_2(54),
      DIB(1) => din_2(57),
      DIB(0) => din_2(56),
      DIC(1) => din_2(59),
      DIC(0) => din_2(58),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(55),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(54),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(57),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(56),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(59),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(58),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM10_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM10_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM12 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(67),
      DIA(0) => din_2(66),
      DIB(1) => din_2(69),
      DIB(0) => din_2(68),
      DIC(1) => din_2(71),
      DIC(0) => din_2(70),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(67),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(66),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(69),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(68),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(71),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(70),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM12_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM12_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM8 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(43),
      DIA(0) => din_2(42),
      DIB(1) => din_2(45),
      DIB(0) => din_2(44),
      DIC(1) => din_2(47),
      DIC(0) => din_2(46),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(43),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(42),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(45),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(44),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(47),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(46),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM8_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM8_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM7 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(37),
      DIA(0) => din_2(36),
      DIB(1) => din_2(39),
      DIB(0) => din_2(38),
      DIC(1) => din_2(41),
      DIC(0) => din_2(40),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(37),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(36),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(39),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(38),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(41),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(40),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM7_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM7_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM9 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(49),
      DIA(0) => din_2(48),
      DIB(1) => din_2(51),
      DIB(0) => din_2(50),
      DIC(1) => din_2(53),
      DIC(0) => din_2(52),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(49),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(48),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(51),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(50),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(53),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(52),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM9_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM9_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM5 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(25),
      DIA(0) => din_2(24),
      DIB(1) => din_2(27),
      DIB(0) => din_2(26),
      DIC(1) => din_2(29),
      DIC(0) => din_2(28),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(25),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(24),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(27),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(26),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(29),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(28),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM5_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM5_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM4 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(19),
      DIA(0) => din_2(18),
      DIB(1) => din_2(21),
      DIB(0) => din_2(20),
      DIC(1) => din_2(23),
      DIC(0) => din_2(22),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(19),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(18),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(21),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(20),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(23),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(22),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM4_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM4_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM6 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(31),
      DIA(0) => din_2(30),
      DIB(1) => din_2(33),
      DIB(0) => din_2(32),
      DIC(1) => din_2(35),
      DIC(0) => din_2(34),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(31),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(30),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(33),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(32),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(35),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(34),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM6_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM6_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM2 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(7),
      DIA(0) => din_2(6),
      DIB(1) => din_2(9),
      DIB(0) => din_2(8),
      DIC(1) => din_2(11),
      DIC(0) => din_2(10),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(7),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(6),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(9),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(8),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(11),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(10),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM2_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM2_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM1 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(1),
      DIA(0) => din_2(0),
      DIB(1) => din_2(3),
      DIB(0) => din_2(2),
      DIC(1) => din_2(5),
      DIC(0) => din_2(4),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(1),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(0),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(3),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(2),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(5),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(4),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM1_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM1_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM3 : RAM32M
    generic map(
      INIT_C => X"0000000000000000",
      INIT_B => X"0000000000000000",
      INIT_D => X"0000000000000000",
      INIT_A => X"0000000000000000"
    )
    port map (
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      DIA(1) => din_2(13),
      DIA(0) => din_2(12),
      DIB(1) => din_2(15),
      DIB(0) => din_2(14),
      DIC(1) => din_2(17),
      DIC(0) => din_2(16),
      DID(1) => BU2_rd_data_count(0),
      DID(0) => BU2_rd_data_count(0),
      ADDRA(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRA(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRA(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRA(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRA(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRB(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRB(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRB(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRB(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRB(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRC(4) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      ADDRC(3) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      ADDRC(2) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      ADDRC(1) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      ADDRC(0) => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      ADDRD(4) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      ADDRD(3) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      ADDRD(2) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      ADDRD(1) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      ADDRD(0) => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      DOA(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(13),
      DOA(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(12),
      DOB(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(15),
      DOB(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(14),
      DOC(1) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(17),
      DOC(0) => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(16),
      DOD(1) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM3_DOD_1_UNCONNECTED,
      DOD(0) => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM3_DOD_0_UNCONNECTED
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_135 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(135),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(135)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_134 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(134),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(134)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_133 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(133),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(133)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_132 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(132),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(132)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_131 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(131),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(131)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_130 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(130),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(130)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_129 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(129),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(129)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_128 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(128),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(128)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_127 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(127),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(127)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_126 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(126),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(126)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_125 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(125),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(125)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_124 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(124),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(124)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_123 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(123),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(123)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_122 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(122),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(122)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_121 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(121),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(121)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_120 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(120),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(120)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_119 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(119),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(119)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_118 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(118),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(118)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_117 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(117),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(117)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_116 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(116),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(116)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_115 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(115),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(115)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_114 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(114),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(114)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_113 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(113),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(113)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_112 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(112),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(112)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_111 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(111),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(111)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_110 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(110),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(110)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_109 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(109),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(109)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_108 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(108),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(108)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_107 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(107),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(107)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_106 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(106),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(106)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_105 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(105),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(105)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_104 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(104),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(104)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_103 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(103),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(103)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_102 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(102),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(102)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_101 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(101),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(101)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_100 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(100),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(100)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_99 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(99),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(99)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_98 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(98),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(98)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_97 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(97),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(97)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_96 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(96),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(96)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_95 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(95),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(95)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_94 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(94),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(94)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_93 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(93),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(93)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_92 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(92),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(92)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_91 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(91),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(91)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_90 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(90),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(90)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_89 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(89),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(89)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_88 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(88),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(88)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_87 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(87),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(87)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_86 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(86),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(86)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_85 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(85),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(85)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_84 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(84),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(84)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_83 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(83),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(83)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_82 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(82),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(82)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_81 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(81),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(81)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_80 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(80),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(80)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_79 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(79),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(79)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_78 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(78),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(78)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_77 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(77),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(77)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_76 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(76),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(76)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_75 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(75),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(75)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_74 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(74),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(74)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_73 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(73),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(73)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_72 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(72),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(72)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_71 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(71),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(71)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_70 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(70),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(70)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_69 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(69),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(69)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_68 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(68),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(68)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_67 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(67),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(67)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_66 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(66),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(66)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_65 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(65),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(65)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_64 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(64),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(64)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_63 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(63),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(63)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_62 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(62),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(62)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_61 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(61),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(61)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_60 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(60),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(60)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_59 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(59),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(59)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_58 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(58),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(58)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_57 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(57),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(57)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_56 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(56),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(56)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_55 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(55),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(55)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_54 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(54),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(54)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_53 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(53),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(53)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_52 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(52),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(52)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_51 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(51),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(51)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_50 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(50),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(50)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_49 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(49),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(49)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_48 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(48),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(48)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_47 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(47),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(47)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_46 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(46),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(46)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_45 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(45),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(45)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_44 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(44),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(44)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_43 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(43),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(43)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_42 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(42),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(42)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_41 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(41),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(41)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_40 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(40),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(40)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_39 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(39),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(39)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_38 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(38),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(38)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_37 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(37),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(37)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_36 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(36),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(36)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_35 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(35),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(35)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_34 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(34),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(34)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_33 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(33),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(33)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_32 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(32),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(32)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_31 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(31),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(31)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_30 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(30),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(30)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_29 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(29),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(29)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_28 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(28),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(28)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_27 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(27),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(27)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_26 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(26),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(26)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_25 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(25),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(25)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_24 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(24),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(24)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_23 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(23),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(23)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_22 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(22),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(22)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_21 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(21),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(21)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_20 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(20),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(20)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_19 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(19),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(19)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_18 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(18),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(18)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_17 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(17),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(17)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_16 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(16),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(16)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_15 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(15),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(15)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_14 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(14),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(14)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_13 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(13),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(13)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_12 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(12),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(12)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_11 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(11),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(11)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_10 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(10),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(10)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_9 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(9),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(9)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_8 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(8),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(8)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_7 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(7),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(7)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_6 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(6),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(6)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_5 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(5),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(5)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_4 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(4),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(4)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_3 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(3),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(3)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_2 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(2),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(2)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_1 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(1),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(1)
    );
  BU2_U0_grf_rf_mem_gdm_dm_dout_i_0 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(0),
      D => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(0),
      Q => BU2_U0_grf_rf_mem_gdm_dm_dout_i(0)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d2_0 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(0),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d2_1 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(1),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d2_2 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(2),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d2_3 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(3),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d2_4 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(4),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d1_4 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count(4),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(4)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d1_3 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count(3),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(3)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d1_1 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count(1),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(1)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d1_0 : FDPE
    generic map(
      INIT => '1'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count(0),
      PRE => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(0)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_d1_2 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count(2),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count_d1(2)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_2 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count6,
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count(2)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_0 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count,
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count(0)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_1 : FDPE
    generic map(
      INIT => '1'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      D => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count3,
      PRE => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count(1)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_3 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count9,
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count(3)
    );
  BU2_U0_grf_rf_gl0_wr_wpntr_count_4 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_ram_wr_en,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count12,
      Q => BU2_U0_grf_rf_gl0_wr_wpntr_count(4)
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_next_fwft_state(0),
      Q => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(0)
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_next_fwft_state(1),
      Q => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(1)
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_i : FDP
    generic map(
      INIT => '1'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_i_or0000,
      PRE => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      Q => empty
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_fb : FDP
    generic map(
      INIT => '1'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_i_or0000,
      PRE => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      Q => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_fb_371
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0003,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(0)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0002,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(1)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0001,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(2)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_xor0000,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(3)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(4)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0003,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(0)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0002,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(1)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0001,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(2)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_xor0000,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(3)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(4)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(0),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(0)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(1),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(1)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(2),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(2)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(3),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(3)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc(4),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(4)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(0),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(0)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(1),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(1)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(2),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(2)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(3),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(3)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc(4),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(4)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(0),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(0)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(1),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(1)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(2),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(2)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(3),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(3)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg(4),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(4)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(0),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(0)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(1),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(1)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(2),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(2)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(3),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(3)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg(4),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(4)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0003,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(0)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0002,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(1)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0001,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(2)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_xor0000,
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(3)
    );
  BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(1),
      D => BU2_U0_grf_rf_gcx_clkx_wr_pntr_gc_asreg_d1(4),
      Q => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(4)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_0 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0003,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(0)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_1 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0002,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(1)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_2 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0001,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(2)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_3 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_xor0000,
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(3)
    );
  BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin_4 : FDC
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CLR => BU2_U0_grf_rf_rstblk_wr_rst_reg(0),
      D => BU2_U0_grf_rf_gcx_clkx_rd_pntr_gc_asreg_d1(4),
      Q => BU2_U0_grf_rf_gcx_clkx_rd_pntr_bin(4)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_4 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count12,
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count(4)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_3 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count9,
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count(3)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_2 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count6,
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count(2)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_1 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count3,
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count(1)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_0 : FDPE
    generic map(
      INIT => '1'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      D => BU2_U0_grf_rf_gl0_rd_rpntr_Mcount_count,
      PRE => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count(0)
    );
  BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000,
      PRE => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      Q => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_307
    );
  BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000,
      PRE => BU2_U0_grf_rf_rstblk_wr_rst_reg(1),
      Q => full
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_d1_4 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_count(4),
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_d1_3 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_count(3),
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_d1_2 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_count(2),
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_d1_1 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_count(1),
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1)
    );
  BU2_U0_grf_rf_gl0_rd_rpntr_count_d1_0 : FDCE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      CLR => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      D => BU2_U0_grf_rf_gl0_rd_rpntr_count(0),
      Q => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0)
    );
  BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i : FDP
    generic map(
      INIT => '1'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000,
      PRE => BU2_U0_grf_rf_rstblk_rd_rst_reg(2),
      Q => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_294
    );
  BU2_U0_grf_rf_rstblk_wr_rst_reg_0 : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_rd_data_count(0),
      PRE => BU2_U0_grf_rf_rstblk_wr_rst_comb,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_reg(0)
    );
  BU2_U0_grf_rf_rstblk_wr_rst_reg_1 : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_rd_data_count(0),
      PRE => BU2_U0_grf_rf_rstblk_wr_rst_comb,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_reg(1)
    );
  BU2_U0_grf_rf_rstblk_rd_rst_reg_0 : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_rd_data_count(0),
      PRE => BU2_U0_grf_rf_rstblk_rd_rst_comb,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_reg(0)
    );
  BU2_U0_grf_rf_rstblk_rd_rst_reg_1 : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_rd_data_count(0),
      PRE => BU2_U0_grf_rf_rstblk_rd_rst_comb,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_reg(1)
    );
  BU2_U0_grf_rf_rstblk_rd_rst_reg_2 : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_rd_data_count(0),
      PRE => BU2_U0_grf_rf_rstblk_rd_rst_comb,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_reg(2)
    );
  BU2_U0_grf_rf_rstblk_rd_rst_asreg : FDPE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_280,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_asreg_284
    );
  BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_grf_rf_rstblk_wr_rst_asreg_285,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_282
    );
  BU2_U0_grf_rf_rstblk_wr_rst_asreg : FDPE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_282,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_asreg_285
    );
  BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_grf_rf_rstblk_rd_rst_asreg_284,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_280
    );
  BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_282,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2_283
    );
  BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_280,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2_281
    );
  BU2_XST_GND : GND
    port map (
      G => BU2_rd_data_count(0)
    );

end STRUCTURE;

-- synthesis translate_on
