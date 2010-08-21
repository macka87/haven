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
--  /   /         Filename           : qdrii_top_user_interface.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. serves as the interface between the user backend and the phy layer,
--          to store user write address, write data, read address and read data.
--       2. Instantiates the write interface and read interface modules.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;

entity qdrii_top_user_interface is
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
    clk0          : in std_logic;
    user_rst_0    : in std_logic;
    clk270        : in std_logic;
    user_rst_270  : in std_logic;
    user_ad_w_n   : in std_logic;
    user_d_w_n    : in std_logic;
    user_ad_wr    : in std_logic_vector(ADDR_WIDTH-1 downto 0);
    user_bw_h     : in std_logic_vector(BW_WIDTH-1 downto 0);
    user_bw_l     : in std_logic_vector(BW_WIDTH-1 downto 0);
    user_dwl      : in std_logic_vector(DATA_WIDTH-1 downto 0);
    user_dwh      : in std_logic_vector(DATA_WIDTH-1 downto 0);
    wr_init_n     : in std_logic;
    wr_init2_n    : in std_logic;
    user_r_n      : in std_logic;
    user_ad_rd    : in std_logic_vector(ADDR_WIDTH-1 downto 0);
    rd_init_n     : in std_logic;
    dummy_wrl     : in std_logic_vector(DATA_WIDTH-1 downto 0);
    dummy_wrh     : in std_logic_vector(DATA_WIDTH-1 downto 0);
    dummy_wren    : in std_logic;
    user_wr_full  : out std_logic;
    fifo_ad_wr    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    fifo_bw_h     : out std_logic_vector(BW_WIDTH-1 downto 0);
    fifo_bw_l     : out std_logic_vector(BW_WIDTH-1 downto 0);
    fifo_dwl      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    fifo_dwh      : out std_logic_vector(DATA_WIDTH-1 downto 0);
    fifo_wr_empty : out std_logic;
    user_rd_full  : out std_logic;
    fifo_ad_rd    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    fifo_rd_empty : out std_logic
    );
end entity qdrii_top_user_interface;

architecture arch_qdrii_top_user_interface of qdrii_top_user_interface is

  component qdrii_top_rd_interface
    generic(
       ADDR_WIDTH   : integer := ADDR_WIDTH
       );
    port(
       clk0           : in  std_logic;
       user_rst_0     : in  std_logic;
       user_r_n       : in  std_logic;
       user_ad_rd     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
       rd_init_n      : in  std_logic;
       user_rd_full   : out std_logic;
       fifo_ad_rd     : out std_logic_vector(ADDR_WIDTH-1 downto 0);
       fifo_rd_empty  : out std_logic
       );
  end component qdrii_top_rd_interface;

  component qdrii_top_wr_interface
    generic(
      ADDR_WIDTH   : integer := ADDR_WIDTH;
      BURST_LENGTH : integer := BURST_LENGTH;
      BW_WIDTH     : integer := BW_WIDTH;
      DATA_WIDTH   : integer := DATA_WIDTH
      );
    port(
      clk0           : in  std_logic;
      user_rst_0     : in  std_logic;
      clk270         : in  std_logic;
      user_rst_270   : in  std_logic;
      dummy_wrl      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      dummy_wrh      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      dummy_wren     : in std_logic;
      user_ad_w_n    : in  std_logic;
      user_d_w_n     : in  std_logic;
      user_ad_wr     : in  std_logic_vector(ADDR_WIDTH - 1 downto 0);
      user_bw_h      : in  std_logic_vector(BW_WIDTH - 1 downto 0);
      user_bw_l      : in  std_logic_vector(BW_WIDTH - 1 downto 0);
      user_dwl       : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      user_dwh       : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      wr_init_n      : in  std_logic;
      wr_init2_n     : in  std_logic;
      user_wr_full   : out std_logic;
      fifo_ad_wr     : out std_logic_vector(ADDR_WIDTH - 1 downto 0);
      fifo_bw_h      : out std_logic_vector(BW_WIDTH - 1 downto 0);
      fifo_bw_l      : out std_logic_vector(BW_WIDTH - 1 downto 0);
      fifo_dwl       : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      fifo_dwh       : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      fifo_wr_empty  : out std_logic
      );
  end component qdrii_top_wr_interface;

begin

  U_QDRII_TOP_RD_INTERFACE : qdrii_top_rd_interface
    generic map(
      ADDR_WIDTH   => ADDR_WIDTH
      )
    port map(
      clk0          => clk0,
      user_rst_0    => user_rst_0,
      user_r_n      => user_r_n,
      user_ad_rd    => user_ad_rd,
      rd_init_n     => rd_init_n,
      user_rd_full  => user_rd_full,
      fifo_ad_rd    => fifo_ad_rd,
      fifo_rd_empty => fifo_rd_empty
      );

  U_QDRII_TOP_WR_INTERFACE : qdrii_top_wr_interface
    generic map(
      ADDR_WIDTH   => ADDR_WIDTH,
      BURST_LENGTH => BURST_LENGTH,
      BW_WIDTH     => BW_WIDTH,
      DATA_WIDTH   => DATA_WIDTH
      )
    port map(
      clk0          => clk0,
      user_rst_0    => user_rst_0,
      clk270        => clk270,
      user_rst_270  => user_rst_270,
      dummy_wrl     => dummy_wrl,
      dummy_wrh     => dummy_wrh,
      dummy_wren    => dummy_wren,
      user_ad_w_n   => user_ad_w_n,
      user_d_w_n    => user_d_w_n,
      user_ad_wr    => user_ad_wr,
      user_bw_h     => user_bw_h,
      user_bw_l     => user_bw_l,
      user_dwl      => user_dwl,
      user_dwh      => user_dwh,
      wr_init_n     => wr_init_n,
      wr_init2_n    => wr_init2_n,
      user_wr_full  => user_wr_full,
      fifo_ad_wr    => fifo_ad_wr,
      fifo_bw_h     => fifo_bw_h,
      fifo_bw_l     => fifo_bw_l,
      fifo_dwl      => fifo_dwl,
      fifo_dwh      => fifo_dwh,
      fifo_wr_empty => fifo_wr_empty
      );

end architecture arch_qdrii_top_user_interface;