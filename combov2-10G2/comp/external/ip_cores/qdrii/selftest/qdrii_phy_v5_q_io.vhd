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
--  /   /         Filename           : qdrii_phy_v5_q_io.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. is used to capture data inside the FPGA and transfer the captured
--          data in the FPGA clock domain
--       2. instantiates the Input buffer and ISERDES, clocked by the negative
--          edge of the memory clock.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_phy_v5_q_io is
  port (
    qdr_q      : in  std_logic;
    bufio_clk  : in  std_logic;
    q_dly_ce   : in  std_logic;
    q_dly_inc  : in  std_logic;
    q_dly_rst  : in  std_logic;
    cal_clk    : in  std_logic;
    qdr_q_rise : out std_logic;
    qdr_q_fall : out std_logic
    );
end entity qdrii_phy_v5_q_io;

architecture arch_qdrii_phy_v5_q_io of qdrii_phy_v5_q_io is

  signal qdr_q_int    : std_logic;
  signal data_rise    : std_logic;
  signal data_fall    : std_logic;
  signal qdr_q_delay  : std_logic;
  signal iserdes_clk  : std_logic;
  signal iserdes_clkb : std_logic;

begin

  QDR_Q_IBUF : IBUF
     port map(
       I => qdr_q,
       O => qdr_q_int
       );

  U_IODELAY : IODELAY
    generic map(
      DELAY_SRC             => "I",
      IDELAY_TYPE           => "VARIABLE",
      HIGH_PERFORMANCE_MODE => TRUE,
      IDELAY_VALUE          => 0,
      ODELAY_VALUE          => 0
      )
    port map(
      DATAOUT => qdr_q_delay,
      C       => cal_clk,
      CE      => q_dly_ce,
      DATAIN  => '0',
      IDATAIN => qdr_q_int,
      INC     => q_dly_inc,
      ODATAIN => '0',
      RST     => q_dly_rst,
      T       => '1'
      );

  iserdes_clk  <= bufio_clk;
  iserdes_clkb <= not bufio_clk;

  U_ISERDES_NODELAY : ISERDES_NODELAY
    generic map (
      BITSLIP_ENABLE => FALSE,
      DATA_RATE      => "DDR",
      DATA_WIDTH     => 4,
      INTERFACE_TYPE => "MEMORY",
      NUM_CE         => 2,
      SERDES_MODE    => "MASTER"
      )
    port map(
      Q1        => data_fall,
      Q2        => data_rise,
      Q3        => open,
      Q4        => open,
      Q5        => open,
      Q6        => open,
      SHIFTOUT1 => open,
      SHIFTOUT2 => open,
      BITSLIP   => '0',
      CE1       => '1',
      CE2       => '1',
      CLK       => iserdes_clk,
      CLKB      => iserdes_clkb,
      CLKDIV    => cal_clk,
      D         => qdr_q_delay,
      OCLK      => cal_clk,
      RST       => '0',
      SHIFTIN1  => '0',
      SHIFTIN2  => '0'
      );

  qdr_q_rise <= data_rise;
  qdr_q_fall <= data_fall;

end architecture arch_qdrii_phy_v5_q_io;