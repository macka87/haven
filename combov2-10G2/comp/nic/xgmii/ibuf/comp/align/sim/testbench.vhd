-- testbench.vhd: Testbench for Align
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.xgmii_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   -- Constant declaration
   constant clkper            : time := 6.4 ns; 
   constant reset_time        : time := 10*clkper;
   constant idle_time         : time := 2*reset_time;

   -- Signals declaration
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT input signals
   signal rxd                 : std_logic_vector(63 downto 0);
   signal rxc                 : std_logic_vector(7 downto 0);

   -- UUT output signals
   signal rxd_aligned         : std_logic_vector(63 downto 0);
   signal rxc_aligned         : std_logic_vector(7 downto 0);
   signal sop_aligned         : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   ALIGN
   -- -------------------------------------------------------------------------
   uut: entity work.ALIGN
      port map (
         CLK               => CLK,
         RESET             => RESET,

         RXD               => rxd,
         RXC               => rxc,

         RXD_ALIGNED       => rxd_aligned,
         RXC_ALIGNED       => rxc_aligned,
         SOP_ALIGNED       => sop_aligned
      );

   -- ----------------------------------------------------
   -- CLK generator
   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process
   begin
      -- Idle
      rxd <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
             C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE; 
      rxc <= (others => '1');
      wait for idle_time;
--       wait for clkper/10;

      -- Start of the first packet (aligned)
      rxd <= C_PREAMBLE;
      rxc(7 downto 1) <= (others => '0');
      rxc(0) <= '1';
      wait for clkper;

      -- End of the first packet
      rxd(63 downto 56) <= C_XGMII_TERMINATE;
      rxd(55 downto 0) <= X"0B0A0908070605";
      rxc(6 downto 0) <= (others => '0');
      rxc(7) <= '1';
      wait for clkper;

      -- Start of the second packet (unaligned)
      rxd(63 downto 32) <= C_PREAMBLE(31 downto 0);
      rxd(31 downto 0) <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE;
      rxc(7 downto 5) <= (others => '0');
      rxc(4 downto 0) <= (others => '1');
      wait for clkper;

      -- End of the second packet
      rxd(63 downto 56) <= C_XGMII_TERMINATE;
      rxd(55 downto 0) <= X"070605" & C_PREAMBLE(63 downto 32);
      rxc(7) <= '1';
      rxc(6 downto 0) <= (others => '0');
      wait for clkper;

      -- Idle
      rxd <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
             C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE; 
      rxc <= (others => '1');
      wait for 5*clkper;



      -- Start of the third packet (unaligned)
      rxd(63 downto 32) <= C_PREAMBLE(31 downto 0);
      rxd(31 downto 0) <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE;
      rxc(7 downto 5) <= (others => '0');
      rxc(4 downto 0) <= (others => '1');
      wait for clkper;

      -- Third packet
      rxd <= X"00070605" & C_PREAMBLE(63 downto 32);
      rxc <= X"00";
      wait for clkper;

      -- End of the third packet
      rxd(63 downto 56) <= C_XGMII_TERMINATE;
      rxd(55 downto 0) <= (others => '1');
      rxc(7) <= '1';
      rxc(6 downto 0) <= (others => '0');
      wait for clkper;

      -- Idle
      rxd <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
             C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE; 
      rxc <= (others => '1');

      wait;
   end process;
end architecture behavioral;
