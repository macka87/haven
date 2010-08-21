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
--*****************************************************************************


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
  attribute IOB of QDR_DLL_OFF_FF : label is "force";

begin

  qdr_c   <= (others => '1');
  qdr_c_n <= (others => '1');

  --QDR_DLL_OFF is asserted high after the 200 us initial count
--  process(clk0)
--    begin
--      if(rising_edge(clk0)) then
--        if(user_rst_0 = '1') then
--          qdr_dll_off_int <= '0';
--        elsif(init_cnt_done = '1') then
--          qdr_dll_off_int <= '1';
--        end if;
--      end if;
--  end process;

  process(clk0)
    begin
      if(rising_edge(clk0)) then
        if(init_cnt_done = '1') then
          qdr_dll_off_int <= '1';
        else
          qdr_dll_off_int <= '0';
        end if;
      end if;
  end process;

  QDR_DLL_OFF_FF : FDRSE
    generic map (
      INIT => '0'
      )
    port map (
      Q  => qdr_dll_off_out,
      C  => clk0,
      CE => '1',
      D  => qdr_dll_off_int,
      R  => '0',
      S  => '0'
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