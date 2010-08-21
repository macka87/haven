--*****************************************************************************
-- DISCLAIMER OF LIABILITY
--
-- This file contains proprietary and confidential information of
-- Xilinx, Inc. ("Xilinx"), that is distributed under a license
-- from Xilinx, and may be used, copied and/or disclosed only
-- pursuant to the terms of a valid license agreement with Xilinx.
--
-- XILINX IS PROVIDING THIS DESIGN, CODE, OR INFORMATION
-- ("MATERIALS") "AS IS" WITHOUT WARRANTY OF ANY KIND, EITHER
-- EXPRESSED, IMPLIED, OR STATUTORY, INCLUDING WITHOUT
-- LIMITATION, ANY WARRANTY WITH RESPECT TO NONINFRINGEMENT,
-- MERCHANTABILITY OR FITNESS FOR ANY PARTICULAR PURPOSE. Xilinx
-- does not warrant that functions included in the Materials will
-- meet the requirements of Licensee, or that the operation of the
-- Materials will be uninterrupted or error-free, or that defects
-- in the Materials will be corrected. Furthermore, Xilinx does
-- not warrant or make any representations regarding use, or the
-- results of the use, of the Materials in terms of correctness,
-- accuracy, reliability or otherwise.
--
-- Xilinx products are not designed or intended to be fail-safe,
-- or for use in any application requiring fail-safe performance,
-- such as life-support or safety devices or systems, Class III
-- medical devices, nuclear facilities, applications related to
-- the deployment of airbags, or any other applications that could
-- lead to death, personal injury or severe property or
-- environmental damage (individually and collectively, "critical
-- applications"). Customer assumes the sole risk and liability
-- of any use of Xilinx products in critical applications,
-- subject only to applicable laws and regulations governing
-- limitations on product liability.
--
-- Copyright 2006, 2007, 2008 Xilinx, Inc.
-- All rights reserved.
--
-- This disclaimer and copyright notice must be retained as part
-- of this file at all times.
--*****************************************************************************
--   ____  ____
--  /   /\/   /
-- /___/  \  /    Vendor             : Xilinx
-- \   \   \/     Version            : 3.3
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
--   Rev 1.1 - Parameter IODELAY_GRP added and constraint IODELAY_GROUP added
--             on IODELAY primitive. PK. 11/27/08
--*****************************************************************************

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_phy_v5_q_io is
  generic(
    HIGH_PERFORMANCE_MODE : boolean := TRUE;
    IODELAY_GRP           : string  := "IODELAY_MIG"
    );
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

  attribute IODELAY_GROUP : string;
  attribute IODELAY_GROUP of U_IODELAY : label is IODELAY_GRP;

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
      HIGH_PERFORMANCE_MODE => HIGH_PERFORMANCE_MODE,
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