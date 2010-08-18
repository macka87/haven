
--
-- TB_CRC32.vhd: Test Bench for CRC32 16-bit Encoder
-- Copyright (C) 2005 CESNET
-- Author(s): Bidlo Michal <bidlom@fit.vutbr.cz>
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
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TB_CRC32 is
end entity TB_CRC32;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture TB_CRC32_arch of TB_CRC32 is

constant period: time := 10 ns;

signal DI: std_logic_vector(15 downto 0);
signal CLK: std_logic := '0';
signal RESET: std_logic := '1';
signal DI_DV: std_logic;
signal DI_MASK: std_logic_vector(1 downto 0);
signal EOP: std_logic;
signal RDY: std_logic;
signal CRC: std_logic_vector(31 downto 0);
signal DO_DV: std_logic;

component CRC32 is
   port(
      DI: in std_logic_vector(15 downto 0);
      CLK: in std_logic;
      RESET: in std_logic;
      DI_DV: in std_logic;
      DI_MASK: in std_logic_vector(1 downto 0);
      EOP: in std_logic;

      RDY: out std_logic;
      CRC: out std_logic_vector(31 downto 0);
      DO_DV: out std_logic
   );
end component;

begin

CRC32_instance : CRC32
port map(
   DI => DI,
   CLK => CLK,
   RESET => RESET,
   DI_DV => DI_DV,
   DI_MASK => DI_MASK,
   EOP => EOP,

   RDY => RDY,
   CRC => CRC,
   DO_DV => DO_DV
);

clk <= not clk after period / 2;

TB_proc: process

file in_file: text;
variable in_line: line;
variable data: std_logic_vector(7 downto 0);
variable good: boolean;

begin

   RESET    <= '1';
   DI_DV    <= '0';
   EOP      <= '0';
   DI_MASK  <= "00";
   wait until CLK'event AND CLK = '1';
   RESET    <= '0';
   DI_DV    <= '1';

   -- open input file
   file_open(in_file, "rx_packet_01_exp.txt", READ_MODE);
   -- write packet
   while not (endfile(in_file)) loop
      readline(in_file, in_line);
      hread(in_line, data, good);
      DI(7 downto 0) <= data(7 downto 0);
      if (endfile(in_file)) then
         DI(15 downto 8) <= "00000000";
         EOP <= '1';
         DI_MASK <= "01";
      else
         readline(in_file, in_line);
         hread(in_line, data, good);
         DI(15 downto 8) <= data(7 downto 0);
         if (endfile(in_file)) then
            EOP <= '1';
         end if;
      end if;
      wait for period;
   end loop;
   DI_DV <= '0';
   EOP <= '0';
   -- close input file
   file_close(in_file);

   wait until DO_DV = '1';
   DI_MASK <= "00";
   wait;

end process;

end architecture TB_CRC32_arch;


