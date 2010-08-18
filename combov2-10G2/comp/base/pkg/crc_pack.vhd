--
-- crc_pack.vhd: Crc computation package
-- Copyright (C) 2003 CESNET
-- Author(s): Tomas Martinek :martinek@liberouter.org>
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
-- ------------------------------------------------------------------
--                   Packake Interface
-- ------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

package crc_pack is

   function crc32(crcreg : std_logic_vector(31 downto 0);
                  din    : std_logic_vector(7 downto 0))
                  return std_logic_vector;

   function crc32_file(file_name : in string)
                  return std_logic_vector;

end crc_pack;

-- ------------------------------------------------------------------
--                     Packake Body
-- ------------------------------------------------------------------
package body crc_pack is

   -- ----------------------------------------------------------------------
   function crc32(crcreg : std_logic_vector(31 downto 0);
                  din    : std_logic_vector(7 downto 0))
                  return std_logic_vector is

   variable next_crc : std_logic_vector(31 downto 0);

   begin
      next_crc(0) := din(6) xor din(0) xor crcreg(24) xor crcreg(30);
      next_crc(1) := din(7) xor din(6) xor din(1) xor din(0) xor crcreg(24)
                     xor crcreg(25) xor crcreg(30) xor crcreg(31);
      next_crc(2) := din(7) xor din(6) xor din(2) xor din(1) xor din(0) xor
                     crcreg(24) xor crcreg(25) xor crcreg(26) xor crcreg(30)
                     xor crcreg(31);
      next_crc(3) := din(7) xor din(3) xor din(2) xor din(1) xor crcreg(25)
                     xor crcreg(26) xor crcreg(27) xor crcreg(31);
      next_crc(4) := din(6) xor din(4) xor din(3) xor din(2) xor din(0) xor
                     crcreg(24) xor crcreg(26) xor crcreg(27) xor crcreg(28)
                     xor crcreg(30);
      next_crc(5) := din(7) xor din(6) xor din(5) xor din(4) xor din(3) xor
                     din(1) xor din(0) xor crcreg(24) xor crcreg(25) xor
                     crcreg(27) xor crcreg(28) xor crcreg(29) xor crcreg(30)
                     xor crcreg(31);
      next_crc(6) := din(7) xor din(6) xor din(5) xor din(4) xor din(2) xor
                     din(1) xor crcreg(25) xor crcreg(26) xor crcreg(28) xor
                     crcreg(29) xor crcreg(30) xor crcreg(31);
      next_crc(7) := din(7) xor din(5) xor din(3) xor din(2) xor din(0) xor
                     crcreg(24) xor crcreg(26) xor crcreg(27) xor crcreg(29)
                     xor crcreg(31);
      next_crc(8) := din(4) xor din(3) xor din(1) xor din(0) xor crcreg(0)
                     xor crcreg(24) xor crcreg(25) xor crcreg(27) xor
                     crcreg(28);
      next_crc(9) := din(5) xor din(4) xor din(2) xor din(1) xor crcreg(1)
                     xor crcreg(25) xor crcreg(26) xor crcreg(28) xor
                     crcreg(29);
      next_crc(10) := din(5) xor din(3) xor din(2) xor din(0) xor crcreg(2)
                      xor crcreg(24) xor crcreg(26) xor crcreg(27) xor
                      crcreg(29);
      next_crc(11) := din(4) xor din(3) xor din(1) xor din(0) xor crcreg(3)
                      xor crcreg(24) xor crcreg(25) xor crcreg(27) xor
                      crcreg(28);
      next_crc(12) := din(6) xor din(5) xor din(4) xor din(2) xor din(1) xor
                      din(0) xor crcreg(4) xor crcreg(24) xor crcreg(25) xor
                      crcreg(26) xor crcreg(28) xor crcreg(29) xor crcreg(30);
      next_crc(13) := din(7) xor din(6) xor din(5) xor din(3) xor din(2) xor
                      din(1) xor crcreg(5) xor crcreg(25) xor crcreg(26) xor
                      crcreg(27) xor crcreg(29) xor crcreg(30) xor crcreg(31);
      next_crc(14) := din(7) xor din(6) xor din(4) xor din(3) xor din(2) xor
                      crcreg(6) xor crcreg(26) xor crcreg(27) xor crcreg(28)
                      xor crcreg(30) xor crcreg(31);
      next_crc(15) := din(7) xor din(5) xor din(4) xor din(3) xor crcreg(7)
                      xor crcreg(27) xor crcreg(28) xor crcreg(29) xor
                      crcreg(31);
      next_crc(16) := din(5) xor din(4) xor din(0) xor crcreg(8) xor
                      crcreg(24) xor crcreg(28) xor crcreg(29);
      next_crc(17) := din(6) xor din(5) xor din(1) xor crcreg(9) xor
                      crcreg(25) xor crcreg(29) xor crcreg(30);
      next_crc(18) := din(7) xor din(6) xor din(2) xor crcreg(10) xor
                      crcreg(26) xor crcreg(30) xor crcreg(31);
      next_crc(19) := din(7) xor din(3) xor crcreg(11) xor crcreg(27)
                      xor crcreg(31);
      next_crc(20) := din(4) xor crcreg(12) xor crcreg(28);
      next_crc(21) := din(5) xor crcreg(13) xor crcreg(29);
      next_crc(22) := din(0) xor crcreg(14) xor crcreg(24);
      next_crc(23) := din(6) xor din(1) xor din(0) xor crcreg(15) xor crcreg(24)
                      xor crcreg(25) xor crcreg(30);
      next_crc(24) := din(7) xor din(2) xor din(1) xor crcreg(16) xor crcreg(25)
                      xor crcreg(26) xor crcreg(31);
      next_crc(25) := din(3) xor din(2) xor crcreg(17) xor crcreg(26) xor
                      crcreg(27);
      next_crc(26) := din(6) xor din(4) xor din(3) xor din(0) xor crcreg(18) xor
                      crcreg(24) xor crcreg(27) xor crcreg(28) xor crcreg(30);
      next_crc(27) := din(7) xor din(5) xor din(4) xor din(1) xor crcreg(19) xor
                      crcreg(25) xor crcreg(28) xor crcreg(29) xor crcreg(31);
      next_crc(28) := din(6) xor din(5) xor din(2) xor crcreg(20) xor crcreg(26)
                      xor crcreg(29) xor crcreg(30);
      next_crc(29) := din(7) xor din(6) xor din(3) xor crcreg(21) xor crcreg(27)
                      xor crcreg(30) xor crcreg(31);
      next_crc(30) := din(7) xor din(4) xor crcreg(22) xor crcreg(28) xor
                      crcreg(31);
      next_crc(31) := din(5) xor crcreg(23) xor crcreg(29);

      return next_crc;
   end crc32;

   -- ----------------------------------------------------------------------
   function crc32_file(file_name : in string) return std_logic_vector is

   file     in_file   : text;
   variable in_line   : line;
   variable din32     : std_logic_vector(31 downto 0);
   variable din8      : std_logic_vector(7 downto 0);
   variable rdin8     : std_logic_vector(7 downto 0);
   variable crcreg    : std_logic_vector(31 downto 0) := X"FFFFFFFF";
   variable rn_crcreg : std_logic_vector(31 downto 0);
   variable len       : integer;


   begin
      -- open input file
      file_open(in_file, file_name, READ_MODE);

      -- Read packet data until line width is different from 32
      readline(in_file, in_line);
      while ((in_line'length /= 0) and (not endfile(in_file))) loop
         din32 := (others => '0');
         len := in_line'length / 2;
         hread(in_line, din32(((in_line'length)*4)-1 downto 0));

         for i in 0 to len-1 loop
            din8 := din32(((i+1)*8)-1 downto (i*8));
            for i in 0 to 7 loop
               rdin8(i) := din8(7-i);
            end loop;
            crcreg := crc32(crcreg, rdin8);
         end loop;
         readline(in_file, in_line);
      end loop;

      -- open input file
      file_close(in_file);

      for i in 0 to 31 loop
         rn_crcreg(i) := not crcreg(31-i);
      end loop;

      return rn_crcreg;
   end crc32_file;

   -- ----------------------------------------------------------------------
end crc_pack;

