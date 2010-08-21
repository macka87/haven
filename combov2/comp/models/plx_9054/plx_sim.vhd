--
-- plx_sim.vhd: PLX - simulation component
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
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
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

use work.plx_oper.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity plx_sim is
   generic(
      PLX_HOLD       : time := 3 ns;
      DEBUG_REPORT   : boolean := false;
      RESET_DELAY    : time := 10 us;
      RESET_TIME     : time := 10 us
   );
   port(
      -- PLX interface -----------------------------------------------------
      LCLKF       : in    std_logic;
      LAD         : inout std_logic_vector(31 downto 0);
      LBE         : inout std_logic_vector(3 downto 0);
      LHOLDA      : inout std_logic;
      LFRAME      : inout std_logic;
      ADS         : out   std_logic;
      BLAST       : out   std_logic;
      LWR         : out   std_logic;
      READY       : inout std_logic;
      LHOLD       : out   std_logic;
      LINT        : inout std_logic;
      LRESET      : out   std_logic;
      USERO       : out   std_logic;

      -- Simulation interface ----------------------------------------------
      STATUS      : out   t_plx_status;
      OPER        : in    t_plx_oper;
      PARAMS      : in    t_plx_params;
      STROBE      : in    std_logic;
      BUSY        : out   std_logic
   );
end entity plx_sim;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of plx_sim is

   constant clkper      : time := 20 ns;

begin

main : process

-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------

-- ----------------------------------------------------------------
-- procedure plx_init initializes local bus signals and sets up
-- lreset signals,
-- 
-- Parameters:
--    no parameters
-- 
procedure plx_init is
begin
   lreset   <= '0';
   lad      <= (others => 'Z');
   ads      <= '1';
   lwr      <= '1';
   blast    <= 'Z';
   lhold    <= '0';
   STATUS   <= ((others => '0'), '0');
   wait for RESET_TIME;
   lreset   <= '1';


   wait for RESET_DELAY;
end plx_init;

-- ----------------------------------------------------------------
-- procedure plx_read reads 'n' words from local bus at address
-- 'addr', and saves data to file, if parameter 'file_name' is set
--
-- Parameters:
--       addr     - start read address
--       n        - number of words to read (default = 1)
--       file_name- output text file (default = "")
-- 
procedure plx_read(addr        : in integer;
                  n           : in integer := 1;
                  file_name   : in string := "") is

variable i        : integer;
file out_file     : text;
variable out_line : line;

begin
   -- open output file
   if (file_name /= "") then
      file_open(out_file, file_name, WRITE_MODE);
   end if;

   wait until (LCLKF'event and LCLKF='1');
   wait for PLX_HOLD;
   -- set LHOLD and wait for LHOLDA
   BLAST <= '1';
   LHOLD <= '1';
   wait until (LCLKF'event and LCLKF='1' and LHOLDA='1');
   wait for PLX_HOLD;
   ADS   <= '0';
   LAD   <= conv_std_logic_vector(addr, 32);
   LWR   <= '0';
   wait until (LCLKF'event and LCLKF='1' and LHOLDA='1');
   -- read num_of_words
   for i in 1 to n loop
      wait for PLX_HOLD;
      ADS   <= '1';
      LAD   <= (others => 'Z');
      -- BLAST setting
      if (i = n) then
          BLAST <= '0';
      end if;
      -- if ready
      wait until (LCLKF'event and LCLKF='1' and READY = '0');
      -- put read value to STATUS port
      STATUS.DO <= LAD;
      STATUS.DV <= '1';
      -- write data to file
      if (file_name /= "") then
         hwrite(out_line, LAD);
         writeline(out_file, out_line);
      end if;
   end loop;
   -- finish
   wait for PLX_HOLD;
   LWR   <= '1';
   BLAST <= '1';
   LAD   <= (others => 'Z');
   wait for clkper - PLX_HOLD;
   STATUS.DV <= '0';
   wait for PLX_HOLD;
   LHOLD <= '0';
   wait until (LCLKF'event and LCLKF='1');

   -- close output file
   if (file_name /= "") then
      file_close(out_file);
   end if;
end plx_read;

-- ----------------------------------------------------------------
-- procedure plx_read_noburst reads 'n' words from local bus at address
-- 'addr'
--
-- Parameters:
--       addr     - start read address
--       n        - number of words to read (default = 1)
-- 
procedure plx_read_noburst(addr   : in integer;
                          n      : in integer := 1) is
variable i        : integer;

begin
   for i in 0 to n-1 loop
   	plx_read(addr+i*4);
   end loop;
end plx_read_noburst;

-- ----------------------------------------------------------------
-- procedure plx_write writes one word of data 'data' to address 'addr'
--
-- Parameters:
--       addr     - start address to write
--       data     - input data
--
procedure plx_write(addr : in integer;
                    data : in std_logic_vector(31 downto 0)) is
variable i: integer;

begin
   wait until (LCLKF'event and LCLKF='1');
   wait for PLX_HOLD;
   -- set LHOLD and wait for LHOLDA
   BLAST <= '1';
   LHOLD <= '1';
   wait until (LCLKF'event and LCLKF='1' and LHOLDA='1');
   wait for PLX_HOLD;
   ADS   <= '0';
   LAD   <= conv_std_logic_vector(addr, 32);
   LWR   <= '1';
   wait for clkper;
   ADS   <= '1';
   -- write
   LAD   <= data;
   BLAST <= '0';
   wait until (LCLKF'event and LCLKF='1' and READY='0');
   wait for PLX_HOLD;
   LWR   <= '1';
   BLAST <= '1';
   LAD   <= (others => 'Z');
   wait for clkper;
   LHOLD <= '0';
   wait until (LCLKF'event and LCLKF='1');
end plx_write;

-- ----------------------------------------------------------------
-- procedure plx_write_file writes data from file 'file_name' to local
-- bus at address 'addr'
--
-- Parameters:
--       addr     - start address to write
--       file_name- file name of input data
--
procedure plx_write_file(addr        : in integer;
                        file_name   : in string) is
variable i        : integer;
file in_file      : text;
variable in_line  : line;
variable good     : boolean;
variable lad_aux  : std_logic_vector(31 downto 0);

begin
   -- open input file
   file_open(in_file, file_name, READ_MODE);

   wait until (LCLKF'event and LCLKF='1');
   wait for PLX_HOLD;
   -- set LHOLD and wait for LHOLDA
   LHOLD <= '1';
   BLAST <= '1';
   wait until (LCLKF'event and LCLKF='1' and LHOLDA='1');
   wait for PLX_HOLD;
   ADS   <= '0';
   LAD   <= conv_std_logic_vector(addr, 32);
   LWR   <= '1';
   wait for clkper;
   ADS   <= '1';
   -- write - first word
   readline(in_file, in_line);
   hread(in_line, lad_aux, good);
   lad <= lad_aux;

   while not (endfile(in_file)) loop
      -- if ready => increment
      wait until (LCLKF'event and LCLKF='1' and READY='0');
      -- read next word
      readline(in_file, in_line);
      hread(in_line, lad_aux, good);
      wait for PLX_HOLD;
      lad <= lad_aux;
   end loop;

   -- last word
   BLAST <= '0';
   wait until (LCLKF'event and LCLKF='1' and READY='0');
   wait for PLX_HOLD;
   LWR   <= '1';
   BLAST <= '1';
   LAD   <= (others => 'Z');
   wait for clkper;
   LHOLD <= '0';
   wait until (LCLKF'event and LCLKF='1');

   -- close input file
   file_close(in_file);
end plx_write_file;

-- ----------------------------------------------------------------
-- procedure plx_write_file_noburst writes data from file 'file_name' to local
-- bus at address 'addr' not in burst mode
--
-- Parameters:
--       addr     - start address to write
--       file_name- file name of input data
--
procedure plx_write_file_noburst(addr : in integer;
                        file_name   : in string) is
variable i       : integer;
file in_file     : text;
variable in_line : line;
variable good    : boolean;
variable lad_aux : std_logic_vector(31 downto 0);
variable a       : integer;
begin
   -- open input file
   file_open(in_file, file_name, READ_MODE);
   a := 0;
   while not (endfile(in_file)) loop
      wait until (LCLKF'event and LCLKF='1');
      wait for PLX_HOLD;
      -- set LHOLD and wait for LHOLDA
      LHOLD <= '1';
      BLAST <= '1';
      wait until (LCLKF'event and LCLKF='1' and LHOLDA='1');
      wait for PLX_HOLD;
      ADS   <= '0';
      LAD   <= conv_std_logic_vector(addr + a, 32);
      LWR   <= '1';
      wait for clkper;
      ADS   <= '1';
      BLAST <= '0';
      -- write - first word
      readline(in_file, in_line);
      hread(in_line, lad_aux, good);
      lad <= lad_aux;
      -- if ready => increment
      wait until (LCLKF'event and LCLKF='1' and READY='0');
      a := a + 4;
      wait for PLX_HOLD;
      LWR   <= '1';
      BLAST <= '1';
      LAD   <= (others => 'Z');
      wait for clkper;
      LHOLD <= '0';
      wait until LHOLDA = '0';
      wait until (LCLKF'event and LCLKF='1');
   end loop;
   file_close(in_file);
end plx_write_file_noburst;

-- ----------------------------------------------------------------
--                        Process Body
-- ----------------------------------------------------------------
begin
   lholda <= 'Z';
   ready  <= 'Z';
   usero  <= '0';
   BUSY   <= '0';
   BLAST  <= 'Z';

   wait until (LCLKF'event and LCLKF='1');

   if (STROBE = '1') then
      BUSY <= '1';
      wait for 0 ns;

      -- Debug report information
      if (DEBUG_REPORT) then
         report "---------------- PLX operation ----------------" severity NOTE;
      end if;

      case OPER is
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Init operation
         when INIT => plx_init;
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Read operation
         when READ =>
            if (PARAMS.no_burst) then
               plx_read_noburst(PARAMS.addr, PARAMS.count);
            else
               plx_read(PARAMS.addr, PARAMS.count, conv_fn_string(PARAMS.file_name));
            end if;
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Write operation
         when WRITE_DATA => plx_write(PARAMS.addr, PARAMS.data);
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         -- Write File operation
         when WRITE_FILE =>
            if (PARAMS.no_burst) then
               plx_write_file_noburst(PARAMS.addr, conv_fn_string(PARAMS.file_name));
            else
               plx_write_file(PARAMS.addr, conv_fn_string(PARAMS.file_name));
            end if;
         -- - - - - - - - - - - - - - - - - - - - - - - - - - - - -
         when others => null;
      end case;

      BUSY <= '0';
   end if;

end process;

end architecture behavioral;

