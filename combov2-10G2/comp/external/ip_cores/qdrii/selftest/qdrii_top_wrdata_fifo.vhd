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
--  /   /         Filename           : qdrii_top_wrdata_fifo.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--       1. Responsible for storing the Write/Read requests made by the user
--          design. Instantiates the FIFOs for Write/Read data storage.
--
--Revision History:
--
--------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_top_wrdata_fifo is
  generic(
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
    DATA_WIDTH : integer := 72
    );
  port(
    clk0         : in  std_logic;
    clk270       : in  std_logic;
    user_rst_270 : in  std_logic;
    idata_lsb    : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
    idata_msb    : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
    rdenb        : in  std_logic;
    wrenb        : in  std_logic;
    odata_lsb    : out std_logic_vector(DATA_WIDTH - 1 downto 0);
    odata_msb    : out std_logic_vector(DATA_WIDTH - 1 downto 0)
    );
end entity qdrii_top_wrdata_fifo;

architecture arch_qdrii_top_wrdata_fifo of qdrii_top_wrdata_fifo is

  constant fifo_data_input_zeros : std_logic_vector(71 downto DATA_WIDTH):= (others => '0');

  signal fifo_data_lsb_input  : std_logic_vector(71 downto 0);
  signal fifo_data_msb_input  : std_logic_vector(71 downto 0);
  signal fifo_data_lsb_output : std_logic_vector(71 downto 0);
  signal fifo_data_msb_output : std_logic_vector(71 downto 0);

begin

  fifo_data_lsb_input <= idata_lsb when (DATA_WIDTH = 72) else
                         (fifo_data_input_zeros(71 downto DATA_WIDTH) & idata_lsb);
  fifo_data_msb_input <= idata_msb when (DATA_WIDTH = 72) else
                         (fifo_data_input_zeros(71 downto DATA_WIDTH) & idata_msb);

  odata_lsb <= fifo_data_lsb_output(DATA_WIDTH - 1 downto 0);
  odata_msb <= fifo_data_msb_output(DATA_WIDTH - 1 downto 0);

  -- Write Data FIFO - Low Word

  U_FIFO36_72_LSB : FIFO36_72
    generic map(
      almost_full_offset      => X"0080",
      almost_empty_offset     => X"0080",
      first_word_fall_through => FALSE,
      do_reg                  => 1,
      en_syn                  => FALSE
      )
    port map(
      di          => fifo_data_lsb_input(63 downto 0),
      dip         => fifo_data_lsb_input(71 downto 64),
      rdclk       => clk270,
      rden        => rdenb,
      rst         => user_rst_270,
      wrclk       => clk0,
      wren        => wrenb,
      dbiterr     => open,
      eccparity   => open,
      sbiterr     => open,
      almostempty => open,
      almostfull  => open,
      do          => fifo_data_lsb_output(63 downto 0),
      dop         => fifo_data_lsb_output(71 downto 64),
      empty       => open,
      full        => open,
      rdcount     => open,
      rderr       => open,
      wrcount     => open,
      wrerr       => open
      );

  -- Write Data FIFO - High Word

  U_FIFO36_72_MSB : FIFO36_72
    generic map(
      almost_full_offset      => X"0080",
      almost_empty_offset     => X"0080",
      first_word_fall_through => FALSE,
      do_reg                  => 1,
      en_syn                  => FALSE
      )
    port map(
      di          => fifo_data_msb_input(63 downto 0),
      dip         => fifo_data_msb_input(71 downto 64),
      rdclk       => clk270,
      rden        => rdenb,
      rst         => user_rst_270,
      wrclk       => clk0,
      wren        => wrenb,
      dbiterr     => open,
      eccparity   => open,
      sbiterr     => open,
      almostempty => open,
      almostfull  => open,
      do          => fifo_data_msb_output(63 downto 0),
      dop         => fifo_data_msb_output(71 downto 64),
      empty       => open,
      full        => open,
      rdcount     => open,
      rderr       => open,
      wrcount     => open,
      wrerr       => open
      );

end architecture arch_qdrii_top_wrdata_fifo;