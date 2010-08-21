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
--------------------------------------------------------------------------------

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

