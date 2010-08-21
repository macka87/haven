-- testbench.vhd: queue_bram testbench
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
-- library containing log2 function
use work.math_pack.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

constant clkper :time := 10 ns;
constant ITEMS_B : integer := 2048;

signal RESET    : std_logic;

signal CLKA     : std_logic;
signal REA      : std_logic;
signal WEA      : std_logic;
signal ADDRA    : std_logic_vector(LOG2(ITEMS_B/4)-1 downto 0);
signal DIA      : std_logic_vector(63 downto 0);
signal DMA      : std_logic_vector(7 downto 0);
signal DOA_DV   : std_logic;
signal DOA      : std_logic_vector(63 downto 0);

signal CLKB     : std_logic;
signal REB      : std_logic;
signal WEB      : std_logic;
signal ADDRB    : std_logic_vector(LOG2(ITEMS_B)-1 downto 0);
signal DIB      : std_logic_vector(15 downto 0);
signal DOB_DV   : std_logic;
signal DOB      : std_logic_vector(15 downto 0);

begin

uut: entity work.queue_bram
   generic map(
      ITEMS_B  => ITEMS_B
   )
   port map(
      RESET    => RESET,
      
      -- PPC interface - 64 bit
      CLKA     => CLKA,
      REA      => REA,
      WEA      => WEA,
      ADDRA    => ADDRA,
      DIA      => DIA,
      DMA      => DMA,
      DOA_DV   => DOA_DV,
      DOA      => DOA,

      -- Control Bus interface - 16 bit, aligned to 32 bits internally
      CLKB     => CLKB,
      REB      => REB,
      WEB      => WEB,
      ADDRB    => ADDRB,
      DIB      => DIB,
      DOB_DV   => DOB_DV,
      DOB      => DOB
   );

-- Clock generation
local_clock: process
begin
   CLKA <= '1';
   wait for clkper/2;
   CLKA <= '0';
   wait for clkper/2;
end process;

CLKB <= CLKA;

-- Test process
test: process
begin
   wait for 2 ns;
   RESET <= '1';
   REA <= '0';
   WEA <= '0';
   ADDRA <= (others => '0');
   DIA <= (others => '0');
   DMA <= (others => '1');
   REB <= '0';
   WEB <= '0';
   ADDRB <= (others => '0');
   DIB <= (others => '0');
   wait for 5*clkper;

   RESET <= '0';
   wait for 5*clkper;

   -- Interface B writing:

   -- Write 32 bits
   WEB <= '1';
   ADDRB <= conv_std_logic_vector(6, ADDRB'length);
   DIB <= conv_std_logic_vector(6, DIB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(7, ADDRB'length);
   DIB <= conv_std_logic_vector(7, DIB'length);
   wait for clkper;
   WEB <= '0';
   
   
   -- Write 64 bits
   WEB <= '1';
   ADDRB <= conv_std_logic_vector(12, ADDRB'length);
   DIB <= conv_std_logic_vector(12, DIB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(13, ADDRB'length);
   DIB <= conv_std_logic_vector(13, DIB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(14, ADDRB'length);
   DIB <= conv_std_logic_vector(14, DIB'length);
   wait for clkper;
   WEB <= '0';
   wait for clkper;
   WEB <= '1';
   ADDRB <= conv_std_logic_vector(15, ADDRB'length);
   DIB <= conv_std_logic_vector(15, DIB'length);
   wait for clkper;
   WEB <= '0';
   
   wait for clkper;
      
   -- Write 32 bits
   WEB <= '1';
   ADDRB <= conv_std_logic_vector(24, ADDRB'length);
   DIB <= conv_std_logic_vector(24, DIB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(25, ADDRB'length);
   DIB <= conv_std_logic_vector(25, DIB'length);
   wait for clkper;
   WEB <= '0';
   wait for 5*clkper;

   -- Interface A reading:
   REA <= '1';
   ADDRA <= conv_std_logic_vector(0, ADDRA'length);
   wait for clkper;
   ADDRA <= conv_std_logic_vector(1, ADDRA'length);
   wait for clkper;
   ADDRA <= conv_std_logic_vector(2, ADDRA'length);
   wait for clkper;
   ADDRA <= conv_std_logic_vector(3, ADDRA'length);
   wait for clkper;
   REA <= '0';
   wait for 5*clkper;

   -- Interface A writing:
   WEA <= '1';
   ADDRA <= conv_std_logic_vector(0, ADDRA'length);
   DIA <= X"0003000200010000";
   wait for clkper;
   ADDRA <= conv_std_logic_vector(1, ADDRA'length);
   DIA <= X"0013001200110010";
   DMA <= "00001111";
   wait for clkper;
   ADDRA <= conv_std_logic_vector(2, ADDRA'length);
   DIA <= X"0023002200210020";
   DMA <= "11111111";
   wait for clkper;
   ADDRA <= conv_std_logic_vector(3, ADDRA'length);
   DIA <= X"0033003200310030";
   wait for clkper;
   WEA <= '0';
   wait for 5*clkper;

   -- Interface B reading:
   REB <= '1';
   ADDRB <= conv_std_logic_vector(0, ADDRB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(1, ADDRB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(2, ADDRB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(3, ADDRB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(4, ADDRB'length);
   wait for clkper;
   REB <= '0';
   wait for clkper;
   REB <= '1';
   ADDRB <= conv_std_logic_vector(5, ADDRB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(6, ADDRB'length);
   wait for clkper;
   ADDRB <= conv_std_logic_vector(7, ADDRB'length);
   wait for clkper;
   REB <= '0';

   wait;
end process;

end;
