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
--------------------------------------------------------------------------------

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

