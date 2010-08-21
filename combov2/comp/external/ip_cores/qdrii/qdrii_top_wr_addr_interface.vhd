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
--  /   /         Filename           : qdrii_top_wr_addr_interface.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--   1. Responsible for storing the Write requests made by the user design.
--      Instantiates the FIFOs for Write address and control storage.
--
--Revision History:
--
--*****************************************************************************

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_top_wr_addr_interface is
  generic (
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    ADDR_WIDTH : integer := 19
    );
  port (
    clk0         : in  std_logic;
    user_rst_0   : in  std_logic;
    user_w_n     : in  std_logic;
    user_ad_wr   : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    wr_init_n    : in  std_logic;
    fifo_ad_wr   : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    wr_adr_empty : out std_logic;
    wr_adr_full  : out std_logic
    );
end entity qdrii_top_wr_addr_interface;

architecture arch_qdrii_top_wr_addr_interface of qdrii_top_wr_addr_interface is

   signal fifo_address_input   : std_logic_vector(31 downto 0);
   signal fifo_adddress_output : std_logic_vector(31 downto 0);
   signal not_wr_init_n        : std_logic;
   signal not_user_w_n         : std_logic;

begin

   fifo_ad_wr <= fifo_adddress_output(ADDR_WIDTH-1 downto 0);
   fifo_address_input(ADDR_WIDTH-1 downto 0) <= user_ad_wr(ADDR_WIDTH-1 downto 0);
   fifo_address_input(31 downto  ADDR_WIDTH) <= (others=>'0');

   not_wr_init_n <= not(wr_init_n);
   not_user_w_n  <= not(user_w_n);

   U_FIFO36 : FIFO36
     generic map (
       ALMOST_FULL_OFFSET      => X"0080",
       ALMOST_EMPTY_OFFSET     => X"0080",
       DATA_WIDTh              => 36,
       FIRST_WORD_FALL_THROUGH => TRUE,
       DO_REG                  => 1,
       EN_SYN                  => FALSE
       )
     port map (
       di          => fifo_address_input,
       dip         => "0000",
       rdclk       => clk0,
       rden        => not_wr_init_n,
       rst         => user_rst_0,
       wrclk       => clk0,
       wren        => not_user_w_n,
       almostempty => open,
       almostfull  => wr_adr_full,
       do          => fifo_adddress_output,
       dop         => open,
       empty       => wr_adr_empty,
       full        => open,
       rdcount     => open,
       rderr       => open,
       wrcount     => open,
       wrerr       => open
       );

end architecture arch_qdrii_top_wr_addr_interface;