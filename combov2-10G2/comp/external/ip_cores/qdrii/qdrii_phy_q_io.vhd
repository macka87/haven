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
--   Rev 1.1 - Parameter IODELAY_GRP added. PK. 11/27/08
--*****************************************************************************

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
    CQ_WIDTH              : integer := 2;
    DATA_WIDTH            : integer := 72;
    HIGH_PERFORMANCE_MODE : boolean := TRUE;
    IODELAY_GRP           : string  := "IODELAY_MIG";
    Q_PER_CQ              : integer := 18
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
    generic(
      HIGH_PERFORMANCE_MODE : boolean := HIGH_PERFORMANCE_MODE;
      IODELAY_GRP           : string  := IODELAY_GRP
      );
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
      generic map(
        HIGH_PERFORMANCE_MODE => HIGH_PERFORMANCE_MODE,
        IODELAY_GRP           => IODELAY_GRP
        )
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