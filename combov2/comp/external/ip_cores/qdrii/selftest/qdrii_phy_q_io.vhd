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
--  /   /         Filename           : qdrii_phy_q_io.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Is used to capture data inside the FPGA and transfer the captured
--          data in the FPGA clock domain.
--       2. instantiates phy_v5_q_io module
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;

entity qdrii_phy_q_io is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    CQ_WIDTH   : integer := 2;
    DATA_WIDTH : integer := 72;
    Q_PER_CQ   : integer := 18
    );
  port(
    qdr_q      : in  std_logic_vector(Q_PER_CQ-1 downto 0);
    bufio_clk  : in  std_logic;
    q_dly_ce   : in  std_logic;
    q_dly_inc  : in  std_logic;
    q_dly_rst  : in  std_logic;
    cal_clk    : in  std_logic;
    qdr_q_rise : out std_logic_vector(Q_PER_CQ-1 downto 0);
    qdr_q_fall : out std_logic_vector(Q_PER_CQ-1 downto 0)
    );
end entity qdrii_phy_q_io;

architecture arch_qdrii_phy_q_io of qdrii_phy_q_io is

  component qdrii_phy_v5_q_io
    port(
      qdr_q      : in  std_logic;
      bufio_clk  : in  std_logic;
      q_dly_ce   : in  std_logic;
      q_dly_inc  : in  std_logic;
      q_dly_rst  : in  std_logic;
      cal_clk    : in  std_logic;
      qdr_q_rise : out std_logic;
      qdr_q_fall : out std_logic
      );
  end component qdrii_phy_v5_q_io;

begin

  QI : for mw_i in 0 to (Q_PER_CQ - 1) generate
    U_QDRII_PHY_V5_Q_IO : qdrii_phy_v5_q_io
      port map(
        qdr_q      => qdr_q(mw_i),
        bufio_clk  => bufio_clk,
        q_dly_ce   => q_dly_ce,
        q_dly_inc  => q_dly_inc,
        q_dly_rst  => q_dly_rst,
        cal_clk    => cal_clk,
        qdr_q_rise => qdr_q_rise(mw_i),
        qdr_q_fall => qdr_q_fall(mw_i)
        );
  end generate QI;

end architecture arch_qdrii_phy_q_io;


