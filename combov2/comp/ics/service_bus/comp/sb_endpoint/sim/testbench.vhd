-- testbench.vhd: sb_endpoint testbench
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

constant clkper : time := 10 ns;

signal CLK            : std_logic;
signal RESET          : std_logic;

signal TDI            : std_logic;
signal TDI_DV         : std_logic;
signal TDO            : std_logic;
signal TDO_DV         : std_logic;

signal ADDR           : std_logic_vector(7 downto 0);
signal RD             : std_logic;
signal WR             : std_logic;
signal DWR            : std_logic_vector(7 downto 0);
signal DRD            : std_logic_vector(7 downto 0);
signal DRDY           : std_logic;

signal message        : std_logic_vector(24 downto 0);
signal message_out     : std_logic_vector(24 downto 0);

begin

uut: entity work.sb_endpoint
port map(
   CLK            => CLK,
   RESET          => RESET,
   TDI            => TDI,
   TDI_DV         => TDI_DV,
   TDO            => TDO,
   TDO_DV         => TDO_DV,
   ADDR           => ADDR,
   RD             => RD,
   WR             => WR,
   DWR            => DWR,
   DRD            => DRD,
   DRDY           => DRDY
);

TDI <= message(24);

msg_out_p : process(CLK, RESET)
begin
   if RESET = '1' then
      message_out <= (others => '0');
   elsif CLK'event and CLK = '1' then
      if TDO_DV = '1' then
         message_out <= message_out(23 downto 0) & TDO;
      end if;
   end if;
end process;

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

   TDI_DV <= '0';
   message <= "00000000" & "0" & "00000000" & "00000000";

   DRD <= "00000000";
   DRDY <= '0';

   RESET <= '1'; 
   wait for 5*clkper;
   RESET <= '0';
   wait for 5*clkper;

   -- Send init message with write to addr 0 - load endpoint Identification
   message <= "00000000" & "1" & "00000000" & "00000011";
              --  ID        WR      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';
   wait for 10*clkper;

   -- Send another init message - this one must be resent to another endpoint
   message <= "00000000" & "1" & "00000000" & "00000111";
              --  ID        WR      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';
   wait for 30*clkper;

   -- Send write message to this endpoint
   message <= "00000011" & "1" & "00010000" & "10000111";
              --  ID        WR      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';
   wait for 10*clkper;

   -- Send write message to another endpoint
   message <= "00010011" & "1" & "00010100" & "10000110";
              --  ID        WR      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';
   wait for 30*clkper;

   -- Send read message to this endpoint
   message <= "00000011" & "0" & "00010001" & "00000000";
              --  ID        RD      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';
   wait for clkper;
   DRDY <= '1'; -- Get data immediately
   DRD <= "10000001";
   wait for clkper;
   DRDY <= '0';
   wait for 30*clkper;

   -- Send read message to this endpoint
   message <= "00000011" & "0" & "00110011" & "00000000";
              --  ID        RD      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';
   wait for 2*clkper;
   DRDY <= '1'; -- Get data after 1 cycle
   DRD <= "11000011";
   wait for clkper;
   DRDY <= '0';

   wait for 30*clkper;

   -- Send read message to this endpoint
   message <= "00000011" & "0" & "01110111" & "00000000";
              --  ID        RD      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';
   wait for 3*clkper;
   DRDY <= '1'; -- Get data after 2 cycles
   DRD <= "11100111";
   wait for clkper;
   DRDY <= '0';
   wait for 30*clkper;

   -- Send read message to another endpoint
   message <= "00001011" & "0" & "01110111" & "00000000";
              --  ID        RD      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';   
   wait for 30*clkper;
   
   -- Send read message to this endpoint, address is 0 - read Id
   message <= "00000011" & "0" & "00000000" & "00000000";
              --  ID        RD      ADDR         DATA
   TDI_DV <= '1';
   for i in 0 to 24 loop
      wait for clkper;
      message <= message(23 downto 0) & "0";
   end loop;
   TDI_DV <= '0';

   wait;
end process;

end;
