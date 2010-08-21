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

-- Component instantion
component CLK_GEN is
   Port (
      -- Input
      CLK50_IN    : in  std_logic;     -- Input clock freqvency (50MHz)
      RESET       : in  std_logic;     -- Global reset signal
      -- Output
      CLK25       : out std_logic;  -- 25MHz  output clock
      CLK25_PH90  : out std_logic;  -- 25MHz  output clock (90' phase shift)
      CLK50_OUT   : out std_logic;  -- 50MHz  output clock
      CLK50_PH90  : out std_logic;  -- 50MHz  output clock (90' phase shift)
      CLK50_PH180 : out std_logic;  -- 50MHz  output clock (180' phase shift)
      CLK100      : out std_logic;  -- 100MHz output clock
      CLK100_PH180: out std_logic;  -- 100MHz output clock (180' phase shift)
      CLK200      : out std_logic;  -- 200MHz output clock
      LOCK        : out std_logic
   );
end component CLK_GEN;

   signal clk50_in    : std_logic;  -- Input clock freqvency (50MHz)
   signal reset       : std_logic;  -- Global reset signal
   signal clk25       : std_logic;  -- 25MHz  output clock
   signal clk25_ph90  : std_logic;  -- 25MHz  output clock (90' phase shift)
   signal clk50_out   : std_logic;  -- 50MHz  output clock
   signal clk50_ph90  : std_logic;  -- 50MHz  output clock (90' phase shift)
   signal clk50_ph180 : std_logic;  -- 50MHz  output clock (180' phase shift)
   signal clk100      : std_logic;  -- 100MHz output clock
   signal clk100_ph180: std_logic;  -- 100MHz output clock (180' phase shift)
   signal clk200      : std_logic;  -- 200MHz output clock
   signal lock        : std_logic;

   constant period : time := 20 ns;
begin

   -- ------------------- Generation of input clock -----------------
   c_gen : process
   begin
      clk50_in <= '0';
      wait for period / 2;
      clk50_in <= '1';
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
   uut : clk_gen
   port map (
      -- Input
      CLK50_IN     => clk50_in,     -- Input clock freqvency (50MHz)
      RESET        => reset,        -- Global reset signal
      -- Output
      CLK25        => clk25,        -- 25MHz  output clock
      CLK25_PH90   => clk25_ph90,   -- 25MHz  output clock (90' phase shift)
      CLK50_OUT    => clk50_out,    -- 50MHz  output clock
      CLK50_PH90   => clk50_ph90,   -- 50MHz  output clock (90' phase shift)
      CLK50_PH180  => clk50_ph180,  -- 50MHz  output clock (180' phase shift)
      CLK100       => clk100,       -- 100MHz output clock
      CLK100_PH180 => clk100_ph180, -- 100MHz output clock (180' phase shift)
      CLK200       => clk200,       -- 200MHz output clock
      LOCK         => lock
   );

end behavioral;
