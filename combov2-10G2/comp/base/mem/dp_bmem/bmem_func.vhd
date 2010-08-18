--
-- bmem_func.vhd: Auxilarity function and constant neeeded by dp_bmem
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
--         address width, data width, Blockram rows and columns etc.
--         from generic paremeters form dp_bmem
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
Package BMEM_FUNC is


-- ------------------------Constant declaration--------------------------------
   --no parity bram capacity
   constant NOPAR_BRAM_CAP : integer := 16384;

   -- parity bram capacity
   constant PAR_BRAM_CAP : integer := 18432;

   -- output register type
   type TOUTPUT_REG is (true, false, auto);


-- ------------------------Function declaration--------------------------------

-- PRIVATE FUNCTIONS
-- function CEIL (x : real) return integer;
   -- Round up real value
   -- e.g. 2.1 -> 3, 2.8 -> 3, 2.0 -> 2


-- function BRAM_CAPACITY(BRAM_TYPE : integer ) return integer;
   -- Returns the capacity of bram_type
   -- Bram_type can be only 1,2,4,9,18,36

-- dp_bmem_bram.vhd functions

   function BRAM_PARITY_WIDTH(BRAM_TYPE : integer ) return integer;
   -- Return parity width of bram type
   -- Output 0, 1, 2, 4

   function BRAM_DATA_WIDTH(BRAM_TYPE : integer ) return integer;
   -- Return data width of bram type
   -- Output: 0, 1, 2, 4, 8, 16, 32

   function BRAM_ADDR_WIDTH(BRAM_TYPE : integer) return integer;
   -- Returns adress width of 1 bram of BRAM_TYPE
   -- Bram_type can be only 1,2,4,9,18,36

   function GET_BRAM_TYPE(DATA_WIDTH : integer; ITEMS : integer) return integer;
   -- Returns the best BRAM_TYPE (1,2,4,9,18,36) for width and count of items


-- dp_bmem.vhd functions

   function BRAM_OUT_REG_TO_BOOL(OUT_REG : TOUTPUT_REG; COLUMN_COUNT: integer)
                                    return boolean;
   -- Transfer enumerated type to boolean
   -- if auto and coumn_count > 1 => true else false

   function BRAM_ROWS_COUNT(BRAM_TYPE : integer; DATA_WIDTH : integer )
               return integer;
   -- Returns number of bram rows
   -- Bram_type can be only 1,2,4,9,18,36

   function BRAM_COLUMN_COUNT(BRAM_TYPE : integer; ITEMS_COUNT : integer ) return integer;
   -- Returns number of bram column
   -- Bram_type can be only 1,2,4,9,18,36

   function COLUMN_ADDR_WIDTH(BRAM_COLUMN_COUNT : integer) return integer;
   -- Returns adress width of bram columns

   function GENMEM_ADDR_WIDTH(BRAM_TYPE : integer; ITEMS_COUNT : integer) return integer;
   -- Returns adress width of generic memory

end  BMEM_FUNC;







-- ----------------------------------------------------------------------------
--                      Package body declaration
-- ----------------------------------------------------------------------------

Package body BMEM_FUNC is


-- ----------------------------------------------------------------------------
   function BRAM_OUT_REG_TO_BOOL(OUT_REG : TOUTPUT_REG; COLUMN_COUNT: integer)
                                    return boolean is
   -- Transfer enumerated type to boolean
   -- if auto and coumn_count > 1 => true else false
   begin
      if ( (OUT_REG = true) or ((OUT_REG = auto) and (COLUMN_COUNT > 1)) ) then
        return true;
      else
        return false;
      end if;
   end BRAM_OUT_REG_TO_BOOL;


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
   function BRAM_DATA_WIDTH(BRAM_TYPE : integer ) return integer is
   -- Return parity width of bram type
   -- Output 0, 1, 2, 4
   begin
      case BRAM_TYPE is
         when 1 => return 1;
         when 2 => return 2;
         when 4 => return 4;
         when 9  => return 8;
         when 18  => return 16;
         when 36  => return 32;
         when others => assert false
            report "illegal bram type - only 1,2,4,9,18,36 is allowed"
            severity error;
            return -1;
      end case;
   end BRAM_DATA_WIDTH;



-- ----------------------------------------------------------------------------
   function BRAM_PARITY_WIDTH(BRAM_TYPE : integer ) return integer is
   -- Return parity width of bram type
   -- Output 0, 1, 2, 4
   begin
      case BRAM_TYPE is
         when 1 | 2 | 4  => return 0;
         when 9  => return 1;
         when 18  => return 2;
         when 36  => return 4;
         when others => assert false
            report "illegal bram type - only 1,2,4,9,18,36 is allowed"
            severity error;
            return -1;
      end case;
   end BRAM_PARITY_WIDTH;


-- ----------------------------------------------------------------------------
   function BRAM_CAPACITY(BRAM_TYPE : integer ) return integer is
   -- Returns the capacity of bram_type
   -- Bram_type can be only 1,2,4,9,18,36
   begin
      case BRAM_TYPE is
         when 1 | 2 | 4  => return NOPAR_BRAM_CAP;
         when 9 | 18 | 36 => return PAR_BRAM_CAP;
         when others => assert false
            report "illegal bram type - only 1,2,4,9,18,36 is allowed"
            severity error;
            return -1;
      end case;
    end BRAM_CAPACITY;



-- ----------------------------------------------------------------------------
   function BRAM_ROWS_COUNT(BRAM_TYPE : integer; DATA_WIDTH : integer )
              return integer is
   -- Returns number of bram rows
   -- Bram_type can be only 1,2,4,9,18,36
   variable aux: integer;
   begin
      aux:= DATA_WIDTH mod BRAM_TYPE;
      if (aux = 0) then
        return DATA_WIDTH/BRAM_TYPE;
      else return (DATA_WIDTH/BRAM_TYPE+1);
      end if;
   end  BRAM_ROWS_COUNT;



-- ----------------------------------------------------------------------------
   function BRAM_COLUMN_COUNT(BRAM_TYPE : integer; ITEMS_COUNT : integer) return integer is
   -- Returns number of bram column
   -- Bram_type can be only 1,2,4,9,18,36
   variable aux : real;
   begin
      -- items count in one column
      aux:=real((BRAM_CAPACITY(BRAM_TYPE) / BRAM_TYPE));
      -- count of columns
      aux:=real(ITEMS_COUNT) / aux;
      return ceil(aux); -- round up
   end BRAM_COLUMN_COUNT;



-- ----------------------------------------------------------------------------
   function BRAM_ADDR_WIDTH(BRAM_TYPE : integer) return integer is
   -- Returns adress width of 1 bram of BRAM_TYPE
   -- Bram_type can be only 1,2,4,9,18,36
   begin
      case BRAM_TYPE is
         when 1  => return 14;
         when 2  => return 13;
         when 4  => return 12;
         when 9  => return 11;
         when 18  => return 10;
         when 36  => return 9;
         when others => assert false
            report "illegal bram type only - 1,2,4,9,18,36 is allowed"
            severity error;
            return -1;
      end case;
   end BRAM_ADDR_WIDTH;



-- ----------------------------------------------------------------------------
   function COLUMN_ADDR_WIDTH(BRAM_COLUMN_COUNT : integer) return integer is
   -- Returns adress width of bram columns
   begin
      return log2(BRAM_COLUMN_COUNT);
   end;



-- ----------------------------------------------------------------------------
  function GENMEM_ADDR_WIDTH(BRAM_TYPE : integer; ITEMS_COUNT : integer) return integer is
-- Returns adress width of generic memory
  begin
     return BRAM_ADDR_WIDTH(BRAM_TYPE) +
        COLUMN_ADDR_WIDTH(BRAM_COLUMN_COUNT(BRAM_TYPE,ITEMS_COUNT));
  end;

  
  
  
function GET_BRAM_TYPE (DATA_WIDTH : integer; ITEMS : integer) return integer is
   variable type1    : integer;
   variable type2    : integer;
   variable type4    : integer;
   variable type9    : integer;
   variable type18   : integer;
   variable type36   : integer;
   variable min      : integer;
   variable min_type : integer;

   begin
      type1  := CEIL(real(DATA_WIDTH / 1))  * CEIL(real(NOPAR_BRAM_CAP / ( 1*ITEMS)));
      type2  := CEIL(real(DATA_WIDTH / 2))  * CEIL(real(NOPAR_BRAM_CAP / ( 2*ITEMS)));
      type4  := CEIL(real(DATA_WIDTH / 4))  * CEIL(real(NOPAR_BRAM_CAP / ( 4*ITEMS)));
      type9  := CEIL(real(DATA_WIDTH / 9))  * CEIL(real(PAR_BRAM_CAP   / ( 9*ITEMS)));
      type18 := CEIL(real(DATA_WIDTH / 18)) * CEIL(real(PAR_BRAM_CAP   / (18*ITEMS)));
      type36 := CEIL(real(DATA_WIDTH / 36)) * CEIL(real(PAR_BRAM_CAP   / (36*ITEMS)));

      min      := type1;
      min_type := 1;

      if (type2 < min) then
         min      := type2;
         min_type := 2;
      end if;

      if (type4 < min) then
         min      := type4;
         min_type := 4;
      end if;

      if (type9 < min) then
         min      := type9;
         min_type := 9;
      end if;

      if (type18 < min) then
         min      := type18;
         min_type := 18;
      end if;

      if (type36 < min) then
         min      := type36;
         min_type := 36;
      end if;
   
     return min_type;
  end;

end BMEM_FUNC;
