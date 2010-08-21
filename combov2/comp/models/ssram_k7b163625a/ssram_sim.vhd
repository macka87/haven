-- cam_sin.vhd: CAM simulation model
-- Copyright (C) 2004 CESNET
-- Author(s): Tobola Jiri    <tobola@liberouter.org>
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
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

entity SSRAM_SIM is
   generic (
      sram_data_file      : string
   );

   port (
      RESET    : in    std_logic;

      -- SRAM interface
      SD       : inout std_logic_vector(35 downto 0);
      SA       : in std_logic_vector(18 downto 0);
      SADSP    : in std_logic;
      SADSC    : in std_logic;
      SADV     : in std_logic;
      SCS1     : in std_logic;
      SCS2     : in std_logic;
      SGW      : in std_logic;
      SBW      : in std_logic;
      SWE      : in std_logic_vector(3 downto 0);
      SOE      : in std_logic;
      SMODE    : in std_logic;
      SCLK     : in std_logic
   );

end SSRAM_SIM;

-- ----------------------------------------------------------------------
--                    Architecture declaration
-- ----------------------------------------------------------------------
architecture behavioral of SSRAM_SIM is

   constant SSIZE        :    integer := 512*1024;
   subtype ssram_word    is   std_logic_vector(35 downto 0);
   type    sram_memory_t is array (SSIZE - 1 downto 0) of ssram_word;

begin

-- ---------------------------------------------------------------------
-- ------------------------- SSRAM simulation --------------------------
-- ---------------------------------------------------------------------
ssram_sim : process(SCLK, SOE) is
   variable memory      : sram_memory_t;
   variable address     : integer := 0;
   variable fill_sram   : integer := 1;
   file input           : text;
   variable good        : boolean;
   variable l           : line;
   variable aux         : std_logic_vector(35 downto 0);
   variable j           : integer := 0;

begin

   -- Fill SRAM memory
   if fill_sram = 1 then
      fill_sram := 0;
      for i in 0 to SSIZE - 1 loop
         memory(i) := conv_std_logic_vector(i, 36);
      end loop;
      file_open(input, sram_data_file, READ_MODE);
      j:=0;
      while not (endfile(input)) loop
         readline(input, l);
         read(l, aux, good);
         memory(j) := aux;
         j:=j+1;
      end loop;
   end if;

   -- SRAM read cycle
   if reset = '0' then
      if SCLK'event and SCLK = '1' then
         SD <= (others => 'Z');
         if (SCS1  = '0' and SCS2 = '0')and(SADSP='0' or SADSC = '0') then
            address := conv_integer(SA);  -- latch address
         end if;
         if SGW = '0' then                -- write
            memory(address) := SD;
         else                             -- read
            if SOE = '0' then
               SD <= memory(address) after 3 ns;
            end if;
         end if;
      end if;

      -- Tristate output control - direction of SD bus
      if SOE = '1' then
         SD <= (others => 'Z') after 4 ns;
      end if;
   end if;

end process ssram_sim;

SD <= (others => 'Z');

end architecture behavioral;
-- ----------------------------------------------------
