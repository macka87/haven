--------------------------------------------------------------------------------
-- Copyright (c) 1995-2008 Xilinx, Inc.  All rights reserved.
--------------------------------------------------------------------------------
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor: Xilinx
-- \   \   \/     Version: K.39
--  \   \         Application: netgen
--  /   /         Filename: asfifo_data_in.vhd
-- /___/   /\     Timestamp: Wed Dec  3 21:28:17 2008
-- \   \  /  \ 
--  \___\/\___\
--             
-- Command	: -intstyle ise -w -sim -ofmt vhdl /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_data_in.ngc /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_data_in.vhd 
-- Device	: 5vlx110tff1136-1
-- Input file	: /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_data_in.ngc
-- Output file	: /home/local/kajan/xilinx_fifo/tmp/_cg/asfifo_data_in.vhd
-- # of Entities	: 1
-- Design Name	: asfifo_data_in
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

entity asfifo_data_in is
  port (
    valid : out STD_LOGIC; 
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
end asfifo_data_in;

architecture STRUCTURE of asfifo_data_in is
  signal NlwRenamedSig_OI_empty : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_76 : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_wr_rst_fb_75 : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_rd_rst_fb_74 : STD_LOGIC; 
  signal BU2_U0_gbiv5_bi_rstbt_rd_rst_reg_73 : STD_LOGIC; 
  signal NLW_VCC_P_UNCONNECTED : STD_LOGIC; 
  signal NLW_GND_G_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTEMPTY_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTFULL_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDERR_UNCONNECTED : STD_LOGIC; 
  signal NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRERR_UNCONNECTED : STD_LOGIC; 
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
  signal din_2 : STD_LOGIC_VECTOR ( 31 downto 0 ); 
  signal dout_3 : STD_LOGIC_VECTOR ( 31 downto 0 ); 
  signal BU2_rd_data_count : STD_LOGIC_VECTOR ( 0 downto 0 ); 
begin
  empty <= NlwRenamedSig_OI_empty;
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
      RST => BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_76,
      RDCLK => rd_clk,
      WRCLK => wr_clk,
      ALMOSTEMPTY => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTEMPTY_UNCONNECTED,
      ALMOSTFULL => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_ALMOSTFULL_UNCONNECTED,
      EMPTY => NlwRenamedSig_OI_empty,
      FULL => full,
      RDERR => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_RDERR_UNCONNECTED,
      WRERR => NLW_BU2_U0_gbiv5_bi_fblk_gextw_1_inst_extd_gonep_inst_prim_gw36_sngfifo18_WRERR_UNCONNECTED,
      DI(31) => din_2(31),
      DI(30) => din_2(30),
      DI(29) => din_2(29),
      DI(28) => din_2(28),
      DI(27) => din_2(27),
      DI(26) => din_2(26),
      DI(25) => din_2(25),
      DI(24) => din_2(24),
      DI(23) => din_2(23),
      DI(22) => din_2(22),
      DI(21) => din_2(21),
      DI(20) => din_2(20),
      DI(19) => din_2(19),
      DI(18) => din_2(18),
      DI(17) => din_2(17),
      DI(16) => din_2(16),
      DI(15) => din_2(15),
      DI(14) => din_2(14),
      DI(13) => din_2(13),
      DI(12) => din_2(12),
      DI(11) => din_2(11),
      DI(10) => din_2(10),
      DI(9) => din_2(9),
      DI(8) => din_2(8),
      DI(7) => din_2(7),
      DI(6) => din_2(6),
      DI(5) => din_2(5),
      DI(4) => din_2(4),
      DI(3) => din_2(3),
      DI(2) => din_2(2),
      DI(1) => din_2(1),
      DI(0) => din_2(0),
      DIP(3) => BU2_rd_data_count(0),
      DIP(2) => BU2_rd_data_count(0),
      DIP(1) => BU2_rd_data_count(0),
      DIP(0) => BU2_rd_data_count(0),
      DO(31) => dout_3(31),
      DO(30) => dout_3(30),
      DO(29) => dout_3(29),
      DO(28) => dout_3(28),
      DO(27) => dout_3(27),
      DO(26) => dout_3(26),
      DO(25) => dout_3(25),
      DO(24) => dout_3(24),
      DO(23) => dout_3(23),
      DO(22) => dout_3(22),
      DO(21) => dout_3(21),
      DO(20) => dout_3(20),
      DO(19) => dout_3(19),
      DO(18) => dout_3(18),
      DO(17) => dout_3(17),
      DO(16) => dout_3(16),
      DO(15) => dout_3(15),
      DO(14) => dout_3(14),
      DO(13) => dout_3(13),
      DO(12) => dout_3(12),
      DO(11) => dout_3(11),
      DO(10) => dout_3(10),
      DO(9) => dout_3(9),
      DO(8) => dout_3(8),
      DO(7) => dout_3(7),
      DO(6) => dout_3(6),
      DO(5) => dout_3(5),
      DO(4) => dout_3(4),
      DO(3) => dout_3(3),
      DO(2) => dout_3(2),
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
      CE => BU2_U0_gbiv5_bi_rstbt_rd_rst_fb_74,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_rd_rst_reg_73
    );
  BU2_U0_gbiv5_bi_rstbt_wr_rst_fb : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      D => BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_76,
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_wr_rst_fb_75
    );
  BU2_U0_gbiv5_bi_rstbt_wr_rst_reg : FDPE
    generic map(
      INIT => '0'
    )
    port map (
      C => wr_clk,
      CE => BU2_U0_gbiv5_bi_rstbt_wr_rst_fb_75,
      D => BU2_rd_data_count(0),
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_wr_rst_reg_76
    );
  BU2_U0_gbiv5_bi_rstbt_rd_rst_fb : FDP
    generic map(
      INIT => '0'
    )
    port map (
      C => rd_clk,
      D => BU2_U0_gbiv5_bi_rstbt_rd_rst_reg_73,
      PRE => rst,
      Q => BU2_U0_gbiv5_bi_rstbt_rd_rst_fb_74
    );
  BU2_XST_GND : GND
    port map (
      G => BU2_rd_data_count(0)
    );

end STRUCTURE;

-- synthesis translate_on
