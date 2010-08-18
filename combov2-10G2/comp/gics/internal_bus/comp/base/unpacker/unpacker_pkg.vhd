--
-- unpacker_pkg.vhd: Internal Bus Unpacker Package
-- Copyright (C) 2008 CESNET
-- Author(s):  Tomas Malek <tomalek@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Internal Bus Unpacker Package                        --
-- ----------------------------------------------------------------------------

package IB_UNPACKER_PKG is

   -- -------------------------------------------------------------------------
   --                                TYPES                                   --
   -- -------------------------------------------------------------------------

   type t_rec128 is record
      VEC : std_logic_vector(127 downto 0);
   end record; 

   type t_rec8 is record
      VEC : std_logic_vector(7 downto 0);
   end record;    

   -- -------------------------------------------------------------------------
   --                         FUNCTION PROTOTYPES                            --
   -- -------------------------------------------------------------------------

   function unpck_addr32_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                              data_width : integer) return t_rec128;

   function unpck_addr64_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                              data_width : integer) return t_rec128;                                              

   function unpck_tag_extracted_from_data  (data       : std_logic_vector(127 downto 0); 
                                            data_width : integer) return t_rec8;       

   function unpck_align_width (data_width : integer) return integer; 

   function unpck_length_we_width (data_width : integer) return integer;

   function unpck_addr_we_width (data_width : integer;
                           addr_width : integer) return integer;

end IB_UNPACKER_PKG;

-- ----------------------------------------------------------------------------
--                    Internal Bus Unpacker Package BODY                     --
-- ----------------------------------------------------------------------------

package body IB_UNPACKER_PKG is

   -- -------------------------------------------------------------------------
   --                          FUNCTION BODIES                               --
   -- -------------------------------------------------------------------------

   -- unpck_addr32_extracted_from_data ----------------------------------------
   -- extracts addr from data

   function unpck_addr32_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                              data_width : integer) return t_rec128 is 
      variable aux : t_rec128;
   begin

      if (data_width <= 32) then
         aux.vec := data;
      else
         aux.vec := X"000000000000000000000000"&data(63 downto 32);
      end if;
      
      return aux;
   end unpck_addr32_extracted_from_data;

   -- unpck_addr64_extracted_from_data ----------------------------------------
   -- extracts addr from data

   function unpck_addr64_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                              data_width : integer) return t_rec128 is 
      variable aux : t_rec128;
   begin

      if (data_width <= 64) then
         aux.vec := data;
      else
         aux.vec := X"000000000000000000000000"&data(95 downto 64);
      end if;
      
      return aux;
   end unpck_addr64_extracted_from_data;   

   -- unpck_tag_extracted_from_data -------------------------------------------
   -- extracts tag from data

   function unpck_tag_extracted_from_data  (data       : std_logic_vector(127 downto 0); 
                                            data_width : integer) return t_rec8 is
      variable aux : t_rec8;
   begin

      if (data_width < 32) then
         aux.vec := data(7 downto 0);
      else
         aux.vec := data(23 downto 16);
      end if;
      
      return aux;
   end unpck_tag_extracted_from_data;  

   -- unpck_align_width -------------------------------------------------------
   -- counts the width of address alignment for BE generation

   function unpck_align_width (data_width : integer) return integer is   
      variable aux : integer;
   begin

      if (data_width = 8) then
         aux := 1;
      else
         aux := log2(data_width/8);
      end if;
      
      return aux;
   end unpck_align_width;   

   -- unpck_length_we_width ---------------------------------------------------
   -- counts the number of parts which length register is composed of

   function unpck_length_we_width (data_width : integer) return integer is   
      variable aux : integer;
   begin

      if (data_width = 8) then
         aux := 2;
      else
         aux := 1;
      end if;
      
      return aux;
   end unpck_length_we_width;      

   -- unpck_addr_we_width -----------------------------------------------------
   -- counts the number of parts which address register is composed of

   function unpck_addr_we_width (data_width : integer;
                                 addr_width : integer) return integer is   
      variable aux : integer;
   begin

      if (data_width >= 32) then
         aux := 1;
      end if;

      if (data_width < 32) then
         aux := (addr_width+data_width-1)/data_width;
      end if;
      
      return aux;
   end unpck_addr_we_width;
    
end IB_UNPACKER_PKG;



