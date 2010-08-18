--
-- math_pack.vhd: Math package
-- Copyright (C) 2003 CESNET
-- Author(s): Zdenek Salvet <salvet@ics.muni.cz>
--            Tomas Martinek <martinek@liberouter.org>
--            Viktor Pus <pus@liberouter.org>
--            Petr Kobiersky <kobiersky@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

package math_pack is

   function log2 (n : integer) return integer;
   function log2 (n : std_logic_vector(31 downto 0)) return integer;
   function max(l, r: integer) return integer;
   function min(l, r: integer) return integer;
   function minimum(l, r: integer) return integer;

end math_pack;

-- ------------------------------------------------------------------
--                     Package Body
-- ------------------------------------------------------------------
package body math_pack is

   -- ----------------------------------------------------------------------
   function log2 (n : integer) return integer is
      variable a, m : integer;
   begin
      if (n = 1) then
         return 0;
      end if;
      a := 0;
      m := 1;
      while m < n loop
         a := a + 1;
         m := m * 2;
      end loop;
      return a;
   end log2;

   -- ----------------------------------------------------------------------
   function log2 (n : std_logic_vector(31 downto 0)) return integer is
      variable m     : std_logic_vector(32 downto 0);
      variable aux_n : std_logic_vector(32 downto 0);
      variable a     : integer;
   begin
      if (n = X"00000001") then
         return 0;
      end if;
      a     := 0;
      m     := '0' & X"00000001";
      aux_n := '0' & n;
      while m < aux_n loop
         a := a + 1;
         m := m(31 downto 0) & '0';
      end loop;
      return a;
   end log2;

   -- ----------------------------------------------------------------------
   function max(L, R: integer) return integer is
   begin
      if L > R then
         return L;
      else
         return R;
      end if;
   end;
   
   -- ----------------------------------------------------------------------
   function min(L, R: integer) return integer is
   begin
      if L < R then
         return L;
      else
         return R;
      end if;
   end;
   
   -- ----------------------------------------------------------------------
   function minimum(L, R: integer) return integer is
   begin
      if L < R then
         return L;
      else
         return R;
      end if;
   end;

   -- ----------------------------------------------------------------------
end math_pack;

