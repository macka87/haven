-- clk_gen_tb.vhd: Clock generation entity testbench
-- Copyright (C) 2003 CESNET, Liberouter project
-- Author(s): Jan Korenek <korenek@liberouter.org>
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
-- TODO:
--

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

-- ----------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant item : integer := 8;

   signal u1_addr   : std_logic_vector(2 downto 0);
   signal u1_do     : std_logic_vector(7 downto 0);
   signal u1_enable : std_logic;

   signal u2_addr   : std_logic_vector(2 downto 0);
   signal u2_di     : std_logic_vector(7 downto 0);
   signal u2_enable : std_logic;

begin


   -- ------------------- Clock generation component ----------------
   uut1 : entity work.dec1fn_enable
   generic map (

      ITEMS => item

   )

   port map (
      -- Input
      
      ADDR            => u1_addr,
      DO	      => u1_do,
      ENABLE          => u1_enable
      
   );

   uut2 : entity work.dec1fn2b
   generic map (

      ITEMS => item

   )

   port map (
      -- Input
      
      ADDR            => u2_addr,
      DI              => u2_di,
      ENABLE          => u2_enable
      
   );

-- ----------------------------------------------------------------
--                           Testbench Body
-- ----------------------------------------------------------------

   u2_di <= u1_do;

   sim : process
   begin
   
   
   -- after start
   
      
   wait for 400 ns;
   

--    u2_enable <= '1';
--    wait for 20 ns;
-- 
--    u2_di <= "10000000";
--    wait for 100 ns;
--    u2_di <= "01000000";
--    wait for 100 ns;
--    u2_di <= "00100000";
--    wait for 100 ns;
--    u2_di <= "00010000";
--    wait for 100 ns;
--    u2_di <= "00001000";
--    wait for 100 ns;
--    u2_di <= "00000100";
--    wait for 100 ns;
--    u2_di <= "00000010";
--    wait for 100 ns;
--    u2_di <= "00000001";
--    wait for 100 ns;
-- 
--    u2_enable <= '0';
--    wait for 20 ns;
-- 
--    u2_di <= "10000000";
--    wait for 100 ns;
--    u2_di <= "01000000";
--    wait for 100 ns;
--    u2_di <= "00100000";
--    wait for 100 ns;
--    u2_di <= "00010000";
--    wait for 100 ns;
--    u2_di <= "00001000";
--    wait for 100 ns;
--    u2_di <= "00000100";
--    wait for 100 ns;
--    u2_di <= "00000010";
--    wait for 100 ns;
--    u2_di <= "00000001";
--    wait for 100 ns;

   u1_enable <= '1';
   u2_enable <= '1';
   wait for 20 ns;

   u1_addr <= "000";
   wait for 100 ns;
   u1_addr <= "001";
   wait for 100 ns;
   u1_addr <= "010";
   wait for 100 ns;
   u1_addr <= "011";
   wait for 100 ns;
   u1_addr <= "100";
   wait for 100 ns;
   u1_addr <= "101";
   wait for 100 ns;
   u1_addr <= "110";
   wait for 100 ns;
   u1_addr <= "111";
   wait for 100 ns;

   u1_enable <= '0';
   wait for 20 ns;

   u1_addr <= "000";
   wait for 100 ns;
   u1_addr <= "001";
   wait for 100 ns;
   u1_addr <= "010";
   wait for 100 ns;
   u1_addr <= "011";
   wait for 100 ns;
   u1_addr <= "100";
   wait for 100 ns;
   u1_addr <= "101";
   wait for 100 ns;
   u1_addr <= "110";
   wait for 100 ns;
   u1_addr <= "111";
   wait for 100 ns;

   u1_enable <= '1';
   u2_enable <= '0';
   wait for 20 ns;

   u1_addr <= "000";
   wait for 100 ns;
   u1_addr <= "001";
   wait for 100 ns;
   u1_addr <= "010";
   wait for 100 ns;
   u1_addr <= "011";
   wait for 100 ns;
   u1_addr <= "100";
   wait for 100 ns;
   u1_addr <= "101";
   wait for 100 ns;
   u1_addr <= "110";
   wait for 100 ns;
   u1_addr <= "111";
   wait for 100 ns;

   u1_enable <= '0';
   wait for 20 ns;

   u1_addr <= "000";
   wait for 100 ns;
   u1_addr <= "001";
   wait for 100 ns;
   u1_addr <= "010";
   wait for 100 ns;
   u1_addr <= "011";
   wait for 100 ns;
   u1_addr <= "100";
   wait for 100 ns;
   u1_addr <= "101";
   wait for 100 ns;
   u1_addr <= "110";
   wait for 100 ns;
   u1_addr <= "111";
   wait for 100 ns;

   wait;
   
   end process;

end behavioral;
