--
-- distmem_func.vhd: Auxilarity function and constant neeeded by dp_distmem
-- Copyright (C) 2004 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
-- README: This package contains functions and constant for enumerating
--         address width, data width, distmem rows and columns etc.
--         from generic paremeters form dp_distmem
--
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Package declaration
-- ----------------------------------------------------------------------------
Package DISTMEM_FUNC is


-- ------------------------Constant declaration--------------------------------




-- ------------------------Function declaration--------------------------------

-- PRIVATE FUNCTIONS

-- function CEIL (x : real) return integer;
   -- Round up real value
   -- e.g. 2.1 -> 3, 2.8 -> 3, 2.0 -> 2

-- dp_distmem_distram.vhd functions
   function DISTMEM_ADDR_WIDTH(DISTMEM_TYPE : integer) return integer;

-- dp_bmem.vhd functions
   function DISTGENMEM_COLUMN_COUNT(DISTMEM_TYPE: integer; ITEMS: integer )
                                                            return integer;
   -- Returns number of DISTGENMEM columns
   -- DISTMEM_TYPE can be only 16, 32, 64,

   function DISTGENMEM_COL_ADDR_WIDTH(COLUMN_COUNT: integer) return integer;
   -- Returns adress width of DISTGENMEM columns

   function DISTGENMEM_ADDR_WIDTH(DISTMEM_TYPE: integer; ITEMS: integer)
                                                            return integer;
   -- Returns adress width of generic memory



end  DISTMEM_FUNC;




-- ----------------------------------------------------------------------------
--                      Package body declaration
-- ----------------------------------------------------------------------------

Package body DISTMEM_FUNC is

-- ----------------------------------------------------------------------------
   function CEIL (x : real) return integer is
   -- Round up real value
   -- e.g. 2.1 -> 3, 2.8 -> 3, 2.0 -> 2
   variable rounded: real;
   begin
      rounded := real (integer(x));
      if x>0.0 then
         if rounded >= x then
            return integer(rounded);
         else
            return integer(rounded+1.0);
         end if;
      elsif  X = 0.0  then
         return integer(0.0);
      else
         if rounded <= x then
            return integer(rounded);
         else
            return integer(rounded-1.0);
         end if;
      end if;
   end CEIL;


-- ----------------------------------------------------------------------------
   function DISTMEM_ADDR_WIDTH(DISTMEM_TYPE : integer) return integer is
   -- Returns adress width of 1 distmem of DISTMEM_TYPE
   -- Distmem_type can be only 16,32,64
   begin
      case DISTMEM_TYPE is
         when 16  => return 4;
         when 32  => return 5;
         when 64  => return 6;
         when others => assert false
            report "illegal distmem type, only - 16,32,64 is allowed"
            severity error;
            return -1;
      end case;
   end DISTMEM_ADDR_WIDTH;


-- ----------------------------------------------------------------------------
   function DISTGENMEM_COLUMN_COUNT(DISTMEM_TYPE: integer; ITEMS: integer)
                                          return integer is
   -- Returns number of DISTGENMEM columns
   -- DISTMEM_TYPE can be only 16, 32, 64,
   variable aux : real;
   begin
      -- count of columns
      aux:=real(ITEMS) / real(DISTMEM_TYPE);
      return ceil(aux); -- round up
   end DISTGENMEM_COLUMN_COUNT;


-- ----------------------------------------------------------------------------
   function DISTGENMEM_COL_ADDR_WIDTH(COLUMN_COUNT: integer) return integer is
   -- Returns adress width of DISTGENMEM columns
   begin
      return log2(COLUMN_COUNT);
   end;



-- ----------------------------------------------------------------------------
  function DISTGENMEM_ADDR_WIDTH(DISTMEM_TYPE: integer; ITEMS: integer)
                                                         return integer is
-- Returns adress width of generic memory
  variable aux : integer;
  begin
     aux := DISTGENMEM_COLUMN_COUNT(DISTMEM_TYPE,ITEMS);
     aux := DISTGENMEM_COL_ADDR_WIDTH(aux);
     return DISTMEM_ADDR_WIDTH(DISTMEM_TYPE) + aux;
  end;

end DISTMEM_FUNC;
