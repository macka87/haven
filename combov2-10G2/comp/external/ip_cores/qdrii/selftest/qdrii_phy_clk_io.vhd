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
--  /   /         Filename           : qdrii_phy_clk_io.vhd
-- /___/   /\     Timestamp          : 15 May 2006
-- \   \  /  \    Date Last Modified : $Date$
--  \___\/\___\
--
--Device: Virtex-5
--Design: QDRII
--
--Purpose:
--    This module
--  1. Generates the memory C/C# and K/K# clocks and the DLL Disable signal.
--
--Revision History:
--
--------------------------------------------------------------------------------


library ieee;
use ieee.std_logic_1164.all;
library unisim;
use unisim.vcomponents.all;

entity qdrii_phy_clk_io is
    -- Following parameters are for 72-bit design (for ML561 Reference board
    -- design). Actual values may be different. Actual parameters values are
    -- passed from design top module qdrii_sram module. Please refer to the
    -- qdrii_sram module for actual values.
  generic(
    CLK_WIDTH : integer := 2
    );
  port(
    clk0          : in std_logic;
    user_rst_0    : in std_logic;
    init_cnt_done : in std_logic;
    qdr_c         : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_c_n       : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_k         : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_k_n       : out std_logic_vector(CLK_WIDTH-1 downto 0);
    qdr_dll_off_n : out std_logic
    );
end entity qdrii_phy_clk_io;

architecture arch_qdrii_phy_clk_io of qdrii_phy_clk_io is

  signal clk_out         : std_logic_vector(CLK_WIDTH-1 downto 0);
  signal clk_outb        : std_logic_vector(CLK_WIDTH-1 downto 0);
  signal qdr_dll_off_int : std_logic;
  signal qdr_dll_off_out : std_logic;

  attribute syn_useioff : boolean;
  attribute IOB : string;

  attribute syn_useioff of QDR_DLL_OFF_FF : label is true;
  attribute IOB of QDR_DLL_OFF_FF : label is "true";

begin

  qdr_c   <= (others => '1');
  qdr_c_n <= (others => '1');

  --QDR_DLL_OFF is asserted high after the 200 us initial count
  process(clk0)
    begin
      if(clk0'event and clk0 = '1') then
        if(user_rst_0 = '1') then
          qdr_dll_off_int <= '0';
        elsif(init_cnt_done = '1') then
          qdr_dll_off_int <= '1';
        end if;
      end if;
  end process;

  QDR_DLL_OFF_FF : FDC
    port map(
      Q   => qdr_dll_off_out,
      D   => qdr_dll_off_int,
      C   => clk0,
      CLR => user_rst_0
      );

  obuf_dll_off_n : OBUF
    port map(
      I => qdr_dll_off_out,
      O => qdr_dll_off_n
      );

  clk_inst : for clk_i in 0 to (CLK_WIDTH-1) generate
    oddr_k_clk0 : ODDR
      generic map(
        ddr_clk_edge => "OPPOSITE_EDGE"
        )
      port map (
        Q  => clk_out(clk_i),
        C  => clk0,
        CE => '1',
        D1 => '1',
        D2 => '0',
        R  => '0',
        S  => '0'
        );

    oddr_k_clkb : ODDR
      generic map(
        DDR_CLK_EDGE => "OPPOSITE_EDGE"
        )
      port map (
        Q  => clk_outb(clk_i),
        C  => clk0,
        CE => '1',
        D1 => '0',
        D2 => '1',
        R  => '0',
        S  => '0'
        );

    obuf_k_clk : OBUF
      port map(
        I => clk_out(clk_i),
        O => qdr_k(clk_i)
        );

    obuf_k_clkb : OBUF
      port map(
        I => clk_outb(clk_i),
        O => qdr_k_n(clk_i)
        );

  end generate clk_inst;

end architecture arch_qdrii_phy_clk_io;


