--------------------------------------------------------------------------------
-- Copyright (c) 1995-2008 Xilinx, Inc.  All rights reserved.
--------------------------------------------------------------------------------
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor: Xilinx
-- \   \   \/     Version: K.39
--  \   \         Application: netgen
--  /   /         Filename: asfifo_2_lsb_addr_bits.vhd
-- /___/   /\     Timestamp: Wed Dec  3 21:31:42 2008
-- \   \  /  \ 
--  \___\/\___\
--             
-- Command	: -intstyle ise -w -sim -ofmt vhdl /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_2_lsb_addr_bits.ngc /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_2_lsb_addr_bits.vhd 
-- Device	: 5vlx110tff1136-1
-- Input file	: /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_2_lsb_addr_bits.ngc
-- Output file	: /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_2_lsb_addr_bits.vhd
-- # of Entities	: 1
-- Design Name	: asfifo_2_lsb_addr_bits
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

entity asfifo_2_lsb_addr_bits is
  port (
    valid : out STD_LOGIC; 
    rd_en : in STD_LOGIC := 'X'; 
    wr_en : in STD_LOGIC := 'X'; 
    full : out STD_LOGIC; 
    empty : out STD_LOGIC; 
    wr_clk : in STD_LOGIC := 'X'; 
    rst : in STD_LOGIC := 'X'; 
    rd_clk : in STD_LOGIC := 'X'; 
    dout : out STD_LOGIC_VECTOR ( 1 downto 0 ); 
    din : in STD_LOGIC_VECTOR ( 1 downto 0 ) 
  );
end asfifo_2_lsb_addr_bits;

architecture STRUCTURE of asfifo_2_lsb_addr_bits is
  signal NlwRenamedSig_OI_empty : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_16 : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_wr_rst_fb_15 : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_rd_rst_fb_14 : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_rd_rst_reg_13 : STD_LOGIC; 
  signal NLW_VCC_P_UNCONNECTED : STD_LOGIC; 
  signal NLW_GND_G_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTEMPTY_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTFULL_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDERR_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRERR_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_31_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_30_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_29_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_28_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_27_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_26_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_25_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_24_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_23_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_22_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_21_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_20_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_19_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_18_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_17_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_16_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_15_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_14_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_13_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_12_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_11_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_10_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_9_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_8_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_7_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_6_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_5_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_4_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_3_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_2_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_3_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_2_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_8_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_7_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_6_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_5_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_4_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_3_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_2_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_0_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_8_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_7_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_6_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_5_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_4_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_3_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_2_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_1_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_0_UNCONNECTED : STD_LOGIC; 
  signal din_2 : STD_LOGIC_VECTOR ( 1 downto 0 ); 
  signal dout_3 : STD_LOGIC_VECTOR ( 1 downto 0 ); 
  signal BU2_rd_data_count : STD_LOGIC_VECTOR ( 0 downto 0 ); 
begin
  empty <= NlwRenamedSig_OI_empty;
  dout(1) <= dout_3(1);
  dout(0) <= dout_3(0);
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
  BU2_U0_gbiv5_bi_fblk_VALID1_INV_0 : INV
    port map (
      I => NlwRenamedSig_OI_empty,
      O => valid
    );
  BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18 : FIFO18_36
    generic map(
      ALMOST_FULL_OFFSET => X"00A",
      SIM_MODE => "SAFE",
      DO_REG => 1,
      EN_SYN => FALSE,
      FIRST_WORD_FALL_THROUGH => TRUE,
      ALMOST_EMPTY_OFFSET => X"00A"
    )
    port map (
      RDEN => rd_en,
      WREN => wr_en,
      RST => BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_16,
      RDCLK => rd_clk,
      WRCLK => wr_clk,
      ALMOSTEMPTY => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTEMPTY_UNCONNECTED,
      ALMOSTFULL => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTFULL_UNCONNECTED,
      EMPTY => NlwRenamedSig_OI_empty,
      FULL => full,
      RDERR => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDERR_UNCONNECTED,
      WRERR => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRERR_UNCONNECTED,
      DI(31) => BU2_rd_data_count(0),
      DI(30) => BU2_rd_data_count(0),
      DI(29) => BU2_rd_data_count(0),
      DI(28) => BU2_rd_data_count(0),
      DI(27) => BU2_rd_data_count(0),
      DI(26) => BU2_rd_data_count(0),
      DI(25) => BU2_rd_data_count(0),
      DI(24) => BU2_rd_data_count(0),
      DI(23) => BU2_rd_data_count(0),
      DI(22) => BU2_rd_data_count(0),
      DI(21) => BU2_rd_data_count(0),
      DI(20) => BU2_rd_data_count(0),
      DI(19) => BU2_rd_data_count(0),
      DI(18) => BU2_rd_data_count(0),
      DI(17) => BU2_rd_data_count(0),
      DI(16) => BU2_rd_data_count(0),
      DI(15) => BU2_rd_data_count(0),
      DI(14) => BU2_rd_data_count(0),
      DI(13) => BU2_rd_data_count(0),
      DI(12) => BU2_rd_data_count(0),
      DI(11) => BU2_rd_data_count(0),
      DI(10) => BU2_rd_data_count(0),
      DI(9) => BU2_rd_data_count(0),
      DI(8) => BU2_rd_data_count(0),
      DI(7) => BU2_rd_data_count(0),
      DI(6) => BU2_rd_data_count(0),
      DI(5) => BU2_rd_data_count(0),
      DI(4) => BU2_rd_data_count(0),
      DI(3) => BU2_rd_data_count(0),
      DI(2) => BU2_rd_data_count(0),
      DI(1) => din_2(1),
      DI(0) => din_2(0),
      DIP(3) => BU2_rd_data_count(0),
      DIP(2) => BU2_rd_data_count(0),
      DIP(1) => BU2_rd_data_count(0),
      DIP(0) => BU2_rd_data_count(0),
      DO(31) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_31_UNCONNECTED,
      DO(30) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_30_UNCONNECTED,
      DO(29) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_29_UNCONNECTED,
      DO(28) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_28_UNCONNECTED,
      DO(27) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_27_UNCONNECTED,
      DO(26) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_26_UNCONNECTED,
      DO(25) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_25_UNCONNECTED,
      DO(24) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_24_UNCONNECTED,
      DO(23) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_23_UNCONNECTED,
      DO(22) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_22_UNCONNECTED,
      DO(21) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_21_UNCONNECTED,
      DO(20) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_20_UNCONNECTED,
      DO(19) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_19_UNCONNECTED,
      DO(18) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_18_UNCONNECTED,
      DO(17) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_17_UNCONNECTED,
      DO(16) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_16_UNCONNECTED,
      DO(15) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_15_UNCONNECTED,
      DO(14) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_14_UNCONNECTED,
      DO(13) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_13_UNCONNECTED,
      DO(12) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_12_UNCONNECTED,
      DO(11) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_11_UNCONNECTED,
      DO(10) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_10_UNCONNECTED,
      DO(9) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_9_UNCONNECTED,
      DO(8) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_8_UNCONNECTED,
      DO(7) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_7_UNCONNECTED,
      DO(6) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_6_UNCONNECTED,
      DO(5) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_5_UNCONNECTED,
      DO(4) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_4_UNCONNECTED,
      DO(3) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_3_UNCONNECTED,
      DO(2) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DO_2_UNCONNECTED,
      DO(1) => dout_3(1),
      DO(0) => dout_3(0),
      DOP(3) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_3_UNCONNECTED,
      DOP(2) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_2_UNCONNECTED,
      DOP(1) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_1_UNCONNECTED,
      DOP(0) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_DOP_0_UNCONNECTED,
      RDCOUNT(8) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_8_UNCONNECTED,
      RDCOUNT(7) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_7_UNCONNECTED,
      RDCOUNT(6) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_6_UNCONNECTED,
      RDCOUNT(5) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_5_UNCONNECTED,
      RDCOUNT(4) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_4_UNCONNECTED,
      RDCOUNT(3) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_3_UNCONNECTED,
      RDCOUNT(2) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_2_UNCONNECTED,
      RDCOUNT(1) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_1_UNCONNECTED,
      RDCOUNT(0) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDCOUNT_0_UNCONNECTED,
      WRCOUNT(8) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_8_UNCONNECTED,
      WRCOUNT(7) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_7_UNCONNECTED,
      WRCOUNT(6) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_6_UNCONNECTED,
      WRCOUNT(5) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_5_UNCONNECTED,
      WRCOUNT(4) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_4_UNCONNECTED,
      WRCOUNT(3) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_3_UNCONNECTED,
      WRCOUNT(2) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_2_UNCONNECTED,
      WRCOUNT(1) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_1_UNCONNECTED,
      WRCOUNT(0) => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRCOUNT_0_UNCONNECTED
    );
  BU2_U0_gbiv5_bi_rstbt_rd_rst_reg : FDPE
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      CE => BU2_U0_gbiv5_bi_rstbt_rd_rst_fb_14,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_rd_rst_reg_13
    );
  BU2_U0_gbiv5_bi_rstbt_wr_rst_fb : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_16,
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_wr_rst_fb_15
    );
  BU2_U0_gbiv5_bi_rstbt_wr_rst_reg : FDPE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_gbiv5_bi_rstbt_wr_rst_fb_15,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_16
    );
  BU2_U0_gbiv5_bi_rstbt_rd_rst_fb : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_gbiv5_bi_rstbt_rd_rst_reg_13,
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_rd_rst_fb_14
    );
  BU2_XST_GND : GND
    port map (
      G => BU2_rd_data_count(0)
    );

end STRUCTURE;

-- synthesis translate_on
