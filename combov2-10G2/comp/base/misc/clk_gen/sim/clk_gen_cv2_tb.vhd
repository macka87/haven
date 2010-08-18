-- clk_gen_cv2_tb.vhd: Clock generation entity testbench
-- Copyright (C) 2009 CESNET, Liberouter project
-- Author(s): Viktor Pus <pus@liberouter.org>
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

   signal clk_in    : std_logic;  -- Input clock frequency
   signal reset       : std_logic;  -- Global reset signal

   signal clk62_5_out      : std_logic;
   signal clk100_out       : std_logic;
   signal clk125_out       : std_logic;
   signal clk250_out       : std_logic;
   signal clk200_out       : std_logic;
   signal clk166_out       : std_logic;
   signal clk_ics_out      : std_logic;
   signal clk_user0_out    : std_logic;
   signal clk_user1_out    : std_logic;
   signal clk_user2_out    : std_logic;
   signal clk_user3_out    : std_logic;
   signal clk_user4_out    : std_logic;

   signal lock        : std_logic;

   constant period : time := 4 ns;
begin

   -- ------------------- Generation of input clock -----------------
   c_gen : process
   begin
      clk_in <= '0';
      wait for period / 2;
      clk_in <= '1';
      wait for period / 2;
   end process c_gen;

   -- ------------------------ Reset generation ---------------------
   res : process
   begin
      reset<='1';
      wait for 300 ns;
      reset<='0';
      wait;
   end process res;

   -- ------------------- Clock generation component ----------------
   uut : entity work.clk_gen_cv2
   port map (
      -- Input
      CLK_IN       => clk_in,     -- Input clock freqvency 
      RESET        => reset,        -- Global reset signal
      -- Output
      CLK62_5_OUT      => clk62_5_out,
      CLK100_OUT       => clk100_out,
      CLK125_OUT       => clk125_out,
      CLK250_OUT       => clk250_out,
      CLK200_OUT       => clk200_out,
      CLK166_OUT       => clk166_out,
      CLK_ICS_OUT      => clk_ics_out,
      CLK_USER0_OUT    => clk_user0_out,
      CLK_USER1_OUT    => clk_user1_out,
      CLK_USER2_OUT    => clk_user2_out,
      CLK_USER3_OUT    => clk_user3_out,
      CLK_USER4_OUT    => clk_user4_out,

      LOCK         => lock
   );

end behavioral;
