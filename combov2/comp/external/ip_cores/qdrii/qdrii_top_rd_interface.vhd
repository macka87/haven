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
--  /   /         Filename           : qdrii_top_rd_interface.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Responsible for storing the Read requests made by the user design.
--       2. Instantiates the FIFOs for Read address, data, and control storage.
--
--Revision History:
--
--*****************************************************************************

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;


entity qdrii_top_rd_interface is
  generic (
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    ADDR_WIDTH : integer := 19
    );
  port (
    clk0          : in  std_logic;
    user_rst_0    : in  std_logic;
    user_r_n      : in  std_logic;
    user_ad_rd    : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    rd_init_n     : in  std_logic;
    user_rd_full  : out std_logic;
    fifo_ad_rd    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    fifo_rd_empty : out std_logic
    );
end entity qdrii_top_rd_interface;

architecture arch_qdrii_top_rd_interface of qdrii_top_rd_interface is

  component qdrii_top_rd_addr_interface
    generic(
      ADDR_WIDTH : integer := ADDR_WIDTH
      );
    port(
      clk0          : in  std_logic;
      user_rst_0    : in  std_logic;
      user_r_n      : in  std_logic;
      user_ad_rd    : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      rd_init_n     : in  std_logic;
      usr_rd_full   : out std_logic;
      fifo_ad_rd    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      fifo_rd_empty : out std_logic
      );
  end component qdrii_top_rd_addr_interface;

begin

   U_QDRII_TOP_RD_ADDR_INTERFACE : qdrii_top_rd_addr_interface
     generic map (
       ADDR_WIDTH  => ADDR_WIDTH
       )
     port map (
       clk0          => clk0,
       user_rst_0    => user_rst_0,
       user_r_n      => user_r_n,
       user_ad_rd    => user_ad_rd,
       rd_init_n     => rd_init_n,
       usr_rd_full   => user_rd_full,
       fifo_ad_rd    => fifo_ad_rd,
       fifo_rd_empty => fifo_rd_empty
       );

end architecture arch_qdrii_top_rd_interface;