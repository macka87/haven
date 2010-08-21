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
--  /   /         Filename           : qdrii_phy_bw_io.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--      1. Is the I/O module of the QDR Byte Write control data, using ODDR
--         Flip flops.
--
--Revision History:
--
--*****************************************************************************

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_phy_bw_io is
  port (
    clk270   : in  std_logic;
    bwl      : in  std_logic;
    bwh      : in  std_logic;
    qdr_bw_n : out std_logic
    );
end entity qdrii_phy_bw_io;

architecture arch_qdrii_phy_bw_io of qdrii_phy_bw_io is

  component ODDR
    generic (
      DDR_CLK_EDGE : string
      );
    port(
      C  : in std_logic;
      CE : in std_logic;
      D1 : in std_logic;
      D2 : in std_logic;
      R  : in std_logic;
      S  : in std_logic;
      Q  : out std_logic
      );
  end component;

  component OBUFT
    port(
      I : in std_logic;
      T : in std_logic;
      O : out std_logic
      );
  end component;

  signal qdr_bw_int : std_logic;

begin

  ODDR_QDR_BW : ODDR
    generic map (
      DDR_CLK_EDGE => "SAME_EDGE"
      )
    port map (
      Q  => qdr_bw_int,
      C  => clk270,
      CE => '1',
      D1 => bwh,
      D2 => bwl,
      R  => '0',
      S  => '0'
      );

  QDR_BW_OBUF : OBUFT
    port map (
      I => qdr_bw_int,
      O => qdr_bw_n,
      T => '0'
      );

end architecture arch_qdrii_phy_bw_io;