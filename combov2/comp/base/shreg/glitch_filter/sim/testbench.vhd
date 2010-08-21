-- testbench.vhd: glitch filter testbench file
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <Pus@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

library work;
use work.math_pack.all;

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER         : time      := 10 ns;
constant RESET_TIME     : time      := 10*CLKPER + 1 ns;

signal clk           : std_logic;
signal reset         : std_logic;

signal din           : std_logic;
signal dout          : std_logic;

begin

uut: entity work.GLITCH_FILTER
   generic map(
      FILTER_LENGTH   => 8,
      FILTER_SAMPLING => 2,
      INIT            => '1'
   )
   port map(
      CLK            => clk,
      RESET          => reset,
      --
      DIN            => din,
      DOUT           => dout
   );

clkgen: process
   begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
   end process;

reset_gen : process
   begin
      RESET <= '1';
      wait for RESET_TIME;
      RESET <= '0';
      wait;
   end process reset_gen;

tb_main:process
begin
   din <= '0';
   wait for RESET_TIME;

   wait for 20*clkper;
   din <= '1';
   wait for 8*clkper;
   din <= '0';
   wait for 8*clkper;
   din <= '1';

   wait;
end process;


end;
