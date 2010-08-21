-- testbench.vhd: cntr_array testbench
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

constant clkper :time := 10 ns;

signal CLK      : std_logic;
signal RESET    : std_logic;

signal VALUE_RD : std_logic_vector(7 downto 0);
signal ADDR_RD  : std_logic_vector(3 downto 0);

signal ADDR_SUB : std_logic_vector(3 downto 0);
signal VALUE_SUB: std_logic_vector(7 downto 0);
signal OUT_SUB  : std_logic_vector(7 downto 0);
signal VLD_SUB  : std_logic;
      
signal ADDR_ADD : std_logic_vector(3 downto 0);
signal VALUE_ADD: std_logic_vector(7 downto 0);
signal VLD_ADD  : std_logic;
signal FULL_ADD : std_logic;

signal MASK     : std_logic_vector(15 downto 0);
signal PEND_REQ : std_logic_vector(15 downto 0);

begin

uut: entity work.cntr_array
   generic map(
      DATA_WIDTH=>8,
      SWAP_PORTS=>true,
      FIFO_ITEMS=>4,
      MASK_SET => 0,
      MASK_BITS=> 128
   )
   port map(
      CLK      => CLK,
      RESET    => RESET,

      VALUE_RD => VALUE_RD,
      ADDR_RD  => ADDR_RD,

      ADDR_SUB => ADDR_SUB,
      VALUE_SUB=> VALUE_SUB,
      VLD_SUB  => VLD_SUB,
      OUT_SUB  => OUT_SUB,
      
      ADDR_ADD => ADDR_ADD,
      VALUE_ADD=> VALUE_ADD,
      VLD_ADD  => VLD_ADD,
      FULL_ADD => FULL_ADD,

      MASK     => MASK,
      PEND_REQ => PEND_REQ
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
   ADDR_RD <= "0000";
   ADDR_SUB <= "0000";
   VALUE_SUB <= "00000000";
   VLD_SUB <= '0';
   ADDR_ADD <= "0000";
   VALUE_ADD <= "00000000";
   VLD_ADD <= '0';
   wait for 5*clkper;

   RESET <= '0';
   wait for 5*clkper;

   -- Add 2 to counter 0
   VALUE_ADD <= "00000010";
   VLD_ADD <= '1';
   wait for clkper;
   VLD_ADD <= '0';
   wait for clkper;
   
   -- Add 3 to counter 0
   VALUE_ADD <= "10000011";
   VLD_ADD <= '1';
   wait for clkper;
   VLD_ADD <= '0';
   wait for clkper;

   -- Substract 2 from counter 0
   VALUE_SUB <= "00000010";
   VLD_SUB <= '1';
   wait for clkper;
   VLD_SUB <= '0';
   
   -- Substract 1 from counter 0
   VALUE_SUB <= "00000001";
   VLD_SUB <= '1';
   wait for clkper;
   VLD_SUB <= '0';
   
   -- Add 3 to counter 1
   VALUE_ADD <= "00000011";
   ADDR_ADD <= "0001";
   VLD_ADD <= '1';
   wait for clkper;
   VLD_ADD <= '0';

   -- Add 3 to counter 1
   VALUE_ADD <= "00000011";
   VLD_ADD <= '1';
   wait for clkper;
   VLD_ADD <= '0';

   -- Substract 1 from counter 1
   VALUE_SUB <= "00000001";
   ADDR_SUB <= "0001";
   VLD_SUB <= '1';
   wait for clkper;
   VLD_SUB <= '0';
   
   -- Substract 2 from counter 0
   VALUE_SUB <= "00000010";
   ADDR_SUB <= "0000";
   VLD_SUB <= '1';
   wait for clkper;
   VLD_SUB <= '0';
   
   wait;
end process;

end;
