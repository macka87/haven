-- testbench.vhd: Testbench for XGMII_DEC
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
   signal input_data          : std_logic_vector(63 downto 0);
   signal input_control       : std_logic_vector(7 downto 0);
   signal input_sop           : std_logic;

   -- UUT output signals
   signal output_data         : std_logic_vector(63 downto 0);
   signal output_sop          : std_logic;
   signal output_eop          : std_logic;
   signal output_eop_pos      : std_logic_vector(2 downto 0);
   signal output_err          : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   ALIGN
   -- -------------------------------------------------------------------------
   uut: entity work.XGMII_DEC
      port map (
         CLK               => CLK,
         RESET             => RESET,

         RXD_ALIGNED       => input_data,
         RXC_ALIGNED       => input_control,
         SOP_ALIGNED       => input_sop,

         DATA              => output_data,
         SOP               => output_sop,
         EOP               => output_eop,
         EOP_POS           => output_eop_pos,
         ERR               => output_err
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
      input_data <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                    C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE; 
      input_control <= (others => '1');
      input_sop <= '0';

      wait for idle_time;
      wait for clkper/10;

      -- Start of the first packet (OK)
      input_data <= C_PREAMBLE;
      input_control <= "00000001";
      input_sop <= '1';
      wait for clkper;

      -- First packet
      input_data <= C_PREAMBLE;
      input_control <= (others => '0');
      input_sop <= '0';
      wait for clkper;

      -- First packet (EOP should be here)
      input_data <= C_PREAMBLE;
      input_control <= (others => '0');
      input_sop <= '0';
      wait for clkper;

      -- End of the first packet
      input_data <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_TERMINATE;
      input_control <= (others => '1');
      input_sop <= '0';
      wait for clkper;

      -- Start of the 2nd packet (ERR)
      input_data <= C_PREAMBLE;
      input_control <= "00000001";
      input_sop <= '1';
      wait for clkper;

      -- 2nd packet
      input_data <= C_PREAMBLE;
      input_control <= (others => '0');
      input_sop <= '0';
      wait for clkper;

      -- 2nd packet with error (EOP should be here)
      input_data <= C_PREAMBLE;
      input_control <= "00000001";
      input_sop <= '0';
      wait for clkper;

      -- End of the 2nd packet
      input_data <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_TERMINATE;
      input_control <= (others => '1');
      input_sop <= '0';
      wait for clkper;

      -- Start of the 3rd packet (OK)
      input_data <= C_PREAMBLE;
      input_control <= "00000001";
      input_sop <= '1';
      wait for clkper;

      -- 3rd packet
      input_data <= C_PREAMBLE;
      input_control <= (others => '0');
      input_sop <= '0';
      wait for clkper;

      -- 3rd packet
      input_data <= C_PREAMBLE;
      input_control <= "00000000";
      input_sop <= '0';
      wait for clkper;

      -- End of the 3rd packet
      input_data <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                C_XGMII_TERMINATE & X"000000";
      input_control <= (7 downto 3 => '1') & "000";
      input_sop <= '0';
      wait for clkper;


      -- EOP before SOP
      wait for clkper;

      -- 2 SOPs and EOP
      input_data <= C_PREAMBLE;
      input_control <= "00000001";
      input_sop <= '1';
      wait for clkper;
      wait for clkper;
      input_data <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                C_XGMII_TERMINATE & X"000000";
      input_control <= (7 downto 3 => '1') & "000";
      input_sop <= '0';
      wait for clkper;

      -- Idle
      input_data <= C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE &
                    C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE & C_XGMII_IDLE; 
      input_control <= (others => '1');
      input_sop <= '0';
      wait;
   end process;
end architecture behavioral;
