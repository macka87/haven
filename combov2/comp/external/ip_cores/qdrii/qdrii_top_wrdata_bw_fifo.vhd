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
--  /   /         Filename           : qdrii_top_wrdata_bw_fifo.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Responsible for storing the Byte Write requests made by the
--          user design. Instantiates the FIFOs for Byte Write data storage.
--
--Revision History:
--
--*****************************************************************************

library ieee;
library unisim;
use ieee.std_logic_1164.all;
use unisim.vcomponents.all;

entity qdrii_top_wrdata_bw_fifo is
  generic (
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    BW_WIDTH : integer := 8
    );
  port (
     clk0         : in  std_logic;
     clk270       : in  std_logic;
     user_rst_270 : in  std_logic;
     idata        : in  std_logic_vector((2*BW_WIDTH)-1 downto 0);
     rdenb        : in  std_logic;
     wrenb        : in  std_logic;
     odata        : out std_logic_vector((2*BW_WIDTH)-1 downto 0)
  );
end entity qdrii_top_wrdata_bw_fifo;

architecture arch_qdrii_top_wrdata_bw_fifo of qdrii_top_wrdata_bw_fifo is

   signal fifo_data_in  : std_logic_vector(35 downto 0);
   signal fifo_data_out : std_logic_vector(35 downto 0);

begin

   fifo_data_in((2*BW_WIDTH)-1 downto 0) <= idata((2*BW_WIDTH)-1 downto 0);
   fifo_data_in(35 downto (2*BW_WIDTH))  <= (others =>'0');
   odata <= fifo_data_out((2*BW_WIDTH)-1 downto 0);

   U_FIFO36 : FIFO36
     generic map (
       almost_full_offset       => X"0080",
       almost_empty_offset      => X"0080",
       data_width               => 36,
       first_word_fall_through  => FALSE,
       do_reg                   => 1,
       en_syn                   => FALSE
       )
     port map (
       di          => fifo_data_in(31 downto 0),
       dip         => fifo_data_in(35 downto 32),
       rdclk       => clk270,
       rden        => rdenb,
       rst         => user_rst_270,
       wrclk       => clk0,
       wren        => wrenb,
       almostempty => open,
       almostfull  => open,
       do          => fifo_data_out(31 downto 0),
       dop         => fifo_data_out(35 downto 32),
       empty       => open,
       full        => open,
       rdcount     => open,
       rderr       => open,
       wrcount     => open,
       wrerr       => open
       );

end architecture arch_qdrii_top_wrdata_bw_fifo;