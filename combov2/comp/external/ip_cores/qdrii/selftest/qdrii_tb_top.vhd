--*****************************************************************************
-- DISCLAIMER OF LIABILITY
--
-- This text/file contains proprietary, confidential
-- information of Xilinx, Inc., is distributed under license
-- from Xilinx, Inc., and may be used, copied and/or
-- disclosed only pursuant to the terms of a valid license
-- agreement with Xilinx, Inc. Xilinx hereby grants you a
-- license to use this text/file solely for design, simulation,
-- implementation and creation of design files limited
-- to Xilinx devices or technologies. Use with non-Xilinx
-- devices or technologies is expressly prohibited and
-- immediately terminates your license unless covered by
-- a separate agreement.
--
-- Xilinx is providing this design, code, or information
-- "as-is" solely for use in developing programs and
-- solutions for Xilinx devices, with no obligation on the
-- part of Xilinx to provide support. By providing this design,
-- code, or information as one possible implementation of
-- this feature, application or standard, Xilinx is making no
-- representation that this implementation is free from any
-- claims of infringement. You are responsible for
-- obtaining any rights you may require for your implementation.
-- Xilinx expressly disclaims any warranty whatsoever with
-- respect to the adequacy of the implementation, including
-- but not limited to any warranties or representations that this
-- implementation is free from claims of infringement, implied
-- warranties of merchantability or fitness for a particular
-- purpose.
--
-- Xilinx products are not intended for use in life support
-- appliances, devices, or systems. Use in such applications is
-- expressly prohibited.
--
-- Any modifications that are made to the Source Code are
-- done at the user's sole risk and will be unsupported.
--
-- Copyright (c) 2006-2007 Xilinx, Inc. All rights reserved.
--
-- This copyright and support notice must be retained as part
-- of this text at all times.
--------------------------------------------------------------------------------
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor             : Xilinx
-- \   \   \/     Version            : 2.2
--  \   \         Application        : MIG
--  /   /         Filename           : qdrii_tb_top.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. serves as the top level synthesizable user backend module.
--       2. Instantiates the write data generation, address generation modules
--          as well the compare modules to check for error.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

entity qdrii_tb_top is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    ADDR_WIDTH   : integer := 19;
    BURST_LENGTH : integer := 4;
    BW_WIDTH     : integer := 8;
    DATA_WIDTH   : integer := 72
    );
  port(
    clk0           : in  std_logic;
    user_rst_0     : in  std_logic;
    user_wr_full   : in  std_logic;
    user_rd_full   : in  std_logic;
    user_qrl       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    user_qrh       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    user_qr_valid  : in  std_logic;
    cal_done       : in  std_logic;
    user_ad_w_n    : out std_logic;
    user_d_w_n     : out std_logic;
    user_ad_wr     : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    user_bwh_n     : out std_logic_vector(BW_WIDTH-1 downto 0);
    user_bwl_n     : out std_logic_vector(BW_WIDTH-1 downto 0);
    user_dwl       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    user_dwh       : out std_logic_vector(DATA_WIDTH-1 downto 0);
    user_r_n       : out std_logic;
    user_ad_rd     : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    compare_error  : out std_logic
    );
end entity qdrii_tb_top;

architecture arch_qdrii_tb_top of qdrii_tb_top is

  signal test_w_n      : std_logic;
  signal dwl_comp      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dwh_comp      : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal dummy_wr_en   : std_logic;
  signal user_d_w_n_i  : std_logic;
  signal user_ad_w_n_i : std_logic;
  signal user_r_n_i    : std_logic;
  signal wr_begin_i    : std_logic;

  component qdrii_test_wr_rd_sm
    generic(
      BURST_LENGTH : integer := BURST_LENGTH
      );
    port(
      clk          : in  std_logic;
      reset        : in  std_logic;
      cal_done     : in  std_logic;
      user_wr_full : in  std_logic;
      user_rd_full : in  std_logic;
      test_w_n     : out std_logic;
      user_ad_w_n  : out std_logic;
      user_d_w_n   : out std_logic;
      user_r_n     : out std_logic;
      wr_begin     : out std_logic
      );
  end component qdrii_test_wr_rd_sm;

  component qdrii_test_q_sm
    generic(
      DATA_WIDTH : integer := DATA_WIDTH
      );
    port(
      clk           : in  std_logic;
      reset         : in  std_logic;
      cal_done      : in  std_logic;
      user_qr_valid : in  std_logic;
      user_qrl      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      user_qrh      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      dwl_comp      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      dwh_comp      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      compare_error : out std_logic
      );
  end component qdrii_test_q_sm;

  component qdrii_test_data_gen
    generic(
      DATA_WIDTH : integer := DATA_WIDTH;
      BW_WIDTH   : integer := BW_WIDTH
      );
    port(
      clk         : in  std_logic;
      reset       : in  std_logic;
      user_w_n    : in  std_logic;
      test_w_n    : in  std_logic;
      user_qr_valid  : in  std_logic;
      wr_begin    : in  std_logic;
      user_dwl    : out std_logic_vector(DATA_WIDTH-1 downto 0);
      user_dwh    : out std_logic_vector(DATA_WIDTH-1 downto 0);
      dwl_comp    : out std_logic_vector(DATA_WIDTH-1 downto 0);
      dwh_comp    : out std_logic_vector(DATA_WIDTH-1 downto 0)
      );
  end component qdrii_test_data_gen;

  component qdrii_test_addr_gen
    generic(
      ADDR_WIDTH   : integer := ADDR_WIDTH;
      BURST_LENGTH : integer := BURST_LENGTH
      );
    port(
      clk        : in  std_logic;
      reset      : in  std_logic;
      user_w_n   : in  std_logic;
      test_w_n   : in  std_logic;
      user_r_n   : in  std_logic;
      user_ad_wr : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      user_ad_rd : out std_logic_vector(ADDR_WIDTH-1 downto 0)
      );
  end component qdrii_test_addr_gen;

begin

  user_bwh_n  <= (others => '0');  -- Byte Write enables all enabled in this testbench
  user_bwl_n  <= (others => '0');
  user_d_w_n  <= user_d_w_n_i;
  user_ad_w_n <= user_ad_w_n_i;
  user_r_n    <= user_r_n_i;

  U_QDRII_TEST_WR_RD_SM : qdrii_test_wr_rd_sm
    port map(
      clk          => clk0,
      reset        => user_rst_0,
      cal_done     => cal_done,
      user_wr_full => user_wr_full,
      user_rd_full => user_rd_full,
      test_w_n     => test_w_n,
      user_d_w_n   => user_d_w_n_i,
      user_ad_w_n  => user_ad_w_n_i,
      user_r_n     => user_r_n_i,
      wr_begin     => wr_begin_i
      );

  U_QDRII_TEST_Q_SM : qdrii_test_q_sm
    generic map(
      DATA_WIDTH => DATA_WIDTH
      )
    port map(
      clk           => clk0,
      reset         => user_rst_0,
      cal_done      => cal_done,
      user_qr_valid => user_qr_valid,
      user_qrl      => user_qrl,
      user_qrh      => user_qrh,
      dwl_comp      => dwl_comp,
      dwh_comp      => dwh_comp,
      compare_error => compare_error
      );

  U_QDRII_TEST_DATA_GEN : qdrii_test_data_gen
    generic map(
      DATA_WIDTH => DATA_WIDTH,
      BW_WIDTH   => BW_WIDTH
      )
    port map(
      clk        => clk0,
      reset      => user_rst_0,
      user_w_n   => user_d_w_n_i,
      test_w_n   => test_w_n,
      user_qr_valid  => user_qr_valid,
      wr_begin   => wr_begin_i,
      user_dwl   => user_dwl,
      user_dwh   => user_dwh,
      dwl_comp   => dwl_comp,
      dwh_comp   => dwh_comp
      );

   U_QDRII_TEST_ADDR_GEN : qdrii_test_addr_gen
     generic map(
       ADDR_WIDTH   => ADDR_WIDTH,
       BURST_LENGTH => BURST_LENGTH
       )
     port map(
       clk        => clk0,
       reset      => user_rst_0,
       user_w_n   => user_ad_w_n_i,
       test_w_n   => test_w_n,
       user_r_n   => user_r_n_i,
       user_ad_wr => user_ad_wr,
       user_ad_rd => user_ad_rd
       );
end architecture arch_qdrii_tb_top;
