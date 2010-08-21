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
--------------------------------------------------------------------------------

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
