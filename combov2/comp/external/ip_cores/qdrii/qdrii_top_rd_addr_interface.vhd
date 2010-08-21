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
--  /   /         Filename           : qdrii_top_rd_addr_interface.vhd
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
--       2. Instantiates the FIFOs for Read address and control storage.
--
--Revision History:
--
--*****************************************************************************

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;


entity qdrii_top_rd_addr_interface is
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
    usr_rd_full   : out std_logic;
    fifo_ad_rd    : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    fifo_rd_empty : out std_logic
    );
end entity qdrii_top_rd_addr_interface;

architecture arch_qdrii_top_rd_addr_interface of qdrii_top_rd_addr_interface is

   signal fifo_input_address  : std_logic_vector(31 downto 0);
   signal fifo_output_address : std_logic_vector(31 downto 0);
   signal not_rd_init_n       : std_logic;
   signal not_user_r_n        : std_logic;

begin

   fifo_input_address(ADDR_WIDTH-1 downto 0) <= user_ad_rd(ADDR_WIDTH-1 downto 0);
   fifo_input_address(31 downto ADDR_WIDTH)  <= (others=>'0');

   fifo_ad_rd <= fifo_output_address(ADDR_WIDTH-1 downto 0);

   not_rd_init_n <= not(rd_init_n);
   not_user_r_n  <= not(user_r_n);

   -- Read Address FIFO
   U_FIFO36 : FIFO36
     generic map (
       almost_full_offset      => X"0080",
       almost_empty_offset     => X"0080",
       data_width              => 36,
       first_word_fall_through => TRUE,
       do_reg                  => 1,
       en_syn                  => FALSE
       )
     port map (
       di          => fifo_input_address,
       dip         => "0000",
       rdclk       => clk0,
       rden        => not_rd_init_n,
       rst         => user_rst_0,
       wrclk       => clk0,
       wren        => not_user_r_n,
       almostempty => open,
       almostfull  => usr_rd_full,
       do          => fifo_output_address,
       dop         => open,
       empty       => fifo_rd_empty,
       full        => open,
       rdcount     => open,
       rderr       => open,
       wrcount     => open,
       wrerr       => open
       );

end architecture arch_qdrii_top_rd_addr_interface;