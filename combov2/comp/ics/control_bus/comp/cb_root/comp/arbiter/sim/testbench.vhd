-- testbench.vhd: arbiter testbench
-- Copyright (C) 2006 CESNET
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

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

constant clkper   :time := 10 ns;

signal CLK        : std_logic;
signal RESET      : std_logic;
signal VECTOR     : std_logic_vector(15 downto 0);
signal STEP       : std_logic;
signal ADDR       : std_logic_vector(3 downto 0);
signal VLD        : std_logic;

begin

uut: entity work.arbiter
   generic map(
      VECTOR_WIDTH   => 16
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      VECTOR         => VECTOR,
      STEP           => STEP,
      ADDR           => ADDR,
      VLD            => VLD
   );

-- Clock generation
local_clock: process
begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
end process;

-- Test process
test: process
begin
   wait for 2 ns;
   RESET <= '1';
   VECTOR <= "0000000000000000";
   STEP <= '0';
   wait for 5*clkper;
   RESET <= '0';
   wait for 20*clkper;
   VECTOR <= "0000100000000010";
   wait for 20*clkper;
   STEP <= '1';
   wait for clkper;
   STEP <= '0';
   VECTOR <= "0000100000000000";
   wait for 5*clkper;
   STEP <= '1';
   wait for clkper;
   STEP <= '0';
   wait for 5*clkper;
   STEP <= '1';
   wait for clkper;
   STEP <= '0';
   VECTOR <= "0000000000000000";
   wait for 5*clkper;
   STEP <= '1';
   wait for clkper;
   STEP <= '0';
   wait for 5*clkper;
   STEP <= '1';
   wait for clkper;
   STEP <= '0';
 
   wait;
end process;

end;
