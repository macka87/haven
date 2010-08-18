--------------------------------------------------------------------------------
-- Copyright (c) 1995-2008 Xilinx, Inc.  All rights reserved.
--------------------------------------------------------------------------------
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor: Xilinx
-- \   \   \/     Version: K.39
--  \   \         Application: netgen
--  /   /         Filename: asfifo_mi32_out.vhd
-- /___/   /\     Timestamp: Mon Mar  2 14:06:35 2009
-- \   \  /  \ 
--  \___\/\___\
--             
-- Command	: -intstyle ise -w -sim -ofmt vhdl /home/shared/dedekt1/tmp/_cg/asfifo_mi32_out.ngc /home/shared/dedekt1/tmp/_cg/asfifo_mi32_out.vhd 
-- Device	: 5vlx110tff1136-1
-- Input file	: /home/shared/dedekt1/tmp/_cg/asfifo_mi32_out.ngc
-- Output file	: /home/shared/dedekt1/tmp/_cg/asfifo_mi32_out.vhd
-- # of Entities	: 1
-- Design Name	: asfifo_mi32_out
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

entity asfifo_mi32_out is
  port (
    rd_en : in STD_LOGIC := 'X'; 
    wr_en : in STD_LOGIC := 'X'; 
    full : out STD_LOGIC; 
    empty : out STD_LOGIC; 
    wr_clk : in STD_LOGIC := 'X'; 
    rst : in STD_LOGIC := 'X'; 
    rd_clk : in STD_LOGIC := 'X'; 
    dout : out STD_LOGIC_VECTOR ( 31 downto 0 ); 
    din : in STD_LOGIC_VECTOR ( 31 downto 0 ) 
  );
end asfifo_mi32_out;

architecture STRUCTURE of asfifo_mi32_out is
  signal BU2_N28 : STD_LOGIC; 
  signal BU2_N26 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000176_258 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126_257 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000086_256 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000176_255 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000126_254 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000086_253 : STD_LOGIC; 
  signal BU2_U0_grf_rf_ram_regout_en : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count6 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count3 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count9 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_wpntr_Mcount_count12 : STD_LOGIC; 
  signal BU2_U0_grf_rf_ram_wr_en : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_fb_163 : STD_LOGIC; 
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
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_99 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_86 : STD_LOGIC; 
  signal BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_comb : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_comb : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_asreg_77 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_asreg_76 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2_75 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_74 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2_73 : STD_LOGIC; 
  signal BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_72 : STD_LOGIC; 
  signal NLW_VCC_P_UNCONNECTED : STD_LOGIC; 
  signal NLW_GND_G_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM62_SPO_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM61_SPO_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM5_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM5_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM4_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM4_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM2_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM2_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM1_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM1_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM3_DOD_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM3_DOD_0_UNCONNECTED : STD_LOGIC; 
  signal din_2 : STD_LOGIC_VECTOR ( 31 downto 0 ); 
  signal dout_3 : STD_LOGIC_VECTOR ( 31 downto 0 ); 
  signal BU2_U0_grf_rf_mem_gdm_dm_dout_i : STD_LOGIC_VECTOR ( 31 downto 0 ); 
  signal BU2_U0_grf_rf_mem_gdm_dm_varindex0000 : STD_LOGIC_VECTOR ( 31 downto 0 ); 
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
      I1 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_99,
      I2 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000126_254,
      I3 => BU2_N26,
      I4 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000176_255,
      I5 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000086_253,
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
      I0 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126_257,
      I1 => BU2_N28,
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_not0001,
      I3 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000176_258,
      I4 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000086_256,
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
      O => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000176_258
    );
  BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126 : LUT4
    generic map(
      INIT => X"8241"
    )
    port map (
      I0 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(4),
      I1 => BU2_U0_grf_rf_gcx_clkx_wr_pntr_bin(0),
      I2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      I3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      O => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or0000126_257
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
      O => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_or000086_256
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
      O => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000176_255
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
      O => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or0000126_254
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
      O => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_i_or000086_253
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_RAM_RD_EN_FWFT1 : LUT4
    generic map(
      INIT => X"2333"
    )
    port map (
      I0 => rd_en,
      I1 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_86,
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
      I1 => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_99,
      O => BU2_U0_grf_rf_ram_wr_en
    );
  BU2_U0_grf_rf_gl0_rd_gr1_rfwft_RAM_REGOUT_EN1 : LUT3
    generic map(
      INIT => X"A2"
    )
    port map (
      I0 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(1),
      I1 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_curr_fwft_state(0),
      I2 => rd_en,
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
      I0 => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_fb_163,
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
      I0 => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_86,
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
      I0 => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2_73,
      I1 => BU2_U0_grf_rf_rstblk_rd_rst_asreg_76,
      O => BU2_U0_grf_rf_rstblk_rd_rst_comb
    );
  BU2_U0_grf_rf_rstblk_wr_rst_comb1 : LUT2
    generic map(
      INIT => X"4"
    )
    port map (
      I0 => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2_75,
      I1 => BU2_U0_grf_rf_rstblk_wr_rst_asreg_77,
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
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM62 : RAM32X1D
    port map (
      A0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      A1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      A2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      A3 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      A4 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      D => din_2(31),
      DPRA0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      DPRA1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      DPRA2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      DPRA3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      DPRA4 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      SPO => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM62_SPO_UNCONNECTED,
      DPO => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(31)
    );
  BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM61 : RAM32X1D
    port map (
      A0 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(0),
      A1 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(1),
      A2 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(2),
      A3 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(3),
      A4 => BU2_U0_grf_rf_gl0_wr_wpntr_count_d2(4),
      D => din_2(30),
      DPRA0 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(0),
      DPRA1 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(1),
      DPRA2 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(2),
      DPRA3 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(3),
      DPRA4 => BU2_U0_grf_rf_gl0_rd_rpntr_count_d1(4),
      WCLK => wr_clk,
      WE => BU2_U0_grf_rf_ram_wr_en,
      SPO => NLW_BU2_U0_grf_rf_mem_gdm_dm_Mram_RAM61_SPO_UNCONNECTED,
      DPO => BU2_U0_grf_rf_mem_gdm_dm_varindex0000(30)
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
      Q => BU2_U0_grf_rf_gl0_rd_gr1_rfwft_empty_fwft_fb_163
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
      Q => BU2_U0_grf_rf_gl0_wr_gwas_wsts_ram_full_fb_i_99
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
      Q => BU2_U0_grf_rf_gl0_rd_gras_rsts_ram_empty_fb_i_86
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
      CE => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_72,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_asreg_76
    );
  BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_grf_rf_rstblk_wr_rst_asreg_77,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_74
    );
  BU2_U0_grf_rf_rstblk_wr_rst_asreg : FDPE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_74,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_asreg_77
    );
  BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_grf_rf_rstblk_rd_rst_asreg_76,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_72
    );
  BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d1_74,
      Q => BU2_U0_grf_rf_rstblk_wr_rst_asreg_d2_75
    );
  BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2 : FD
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d1_72,
      Q => BU2_U0_grf_rf_rstblk_rd_rst_asreg_d2_73
    );
  BU2_XST_GND : GND
    port map (
      G => BU2_rd_data_count(0)
    );

end STRUCTURE;

-- synthesis translate_on
