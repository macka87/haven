--
-- switch_pkg.vhd: Internal Bus Switch Package
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
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all;

-- ----------------------------------------------------------------------------
--                        Internal Bus Switch Package                        --
-- ----------------------------------------------------------------------------

package IB_SWITCH_PKG is

   -- -------------------------------------------------------------------------
   --                                TYPES                                   --
   -- -------------------------------------------------------------------------

   type t_rec128 is record
      VEC : std_logic_vector(127 downto 0);
   end record; 

   -- -------------------------------------------------------------------------
   --                         FUNCTION PROTOTYPES                            --
   -- -------------------------------------------------------------------------

   function ib_switch_buffer_data_depth (header_num : integer; 
                                         data_width : integer) return integer;

   function ib_switch_buffer_request_depth (header_num : integer; 
                                            data_width : integer) return integer;

   function addr_comparison_width (data_width : integer; 
                                   cmp_limit  : integer) return integer;

   function addr_input_width (data_width : integer) return integer;                                   

   function addr_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                      data_width : integer) return t_rec128;
 
   function type_lg_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                         data_width : integer) return std_logic; 

   function cnt_bits_const (addr_width : integer;
                            cmp_width  : integer) return integer;                                         

   function address_splitter_enable (data_width : integer;
                                     cmp_limit  : integer) return boolean;                                                                     

end IB_SWITCH_PKG;

-- ----------------------------------------------------------------------------
--                      Internal Bus Switch Package BODY                     --
-- ----------------------------------------------------------------------------

package body IB_SWITCH_PKG is

   -- -------------------------------------------------------------------------
   --                          FUNCTION BODIES                               --
   -- -------------------------------------------------------------------------

   -- ib_switch_buffer_data_depth ---------------------------------------------
   -- counts the number of items in data buffer

   function ib_switch_buffer_data_depth (header_num : integer; 
                                         data_width : integer) return integer is
      variable aux : integer;
   begin
      --aux := (C_IB_HEADER_WIDTH / data_width) * header_num;
      --
      --if ((aux mod 16) /= 0) then
      --   aux := aux + (16 - (aux mod 16));
      --end if;

      aux := (C_IB_HEADER_WIDTH / data_width) * header_num;

      if (aux = 1) then
         aux := 2;
      end if;

      return aux;
   end ib_switch_buffer_data_depth; 

   -- ib_switch_buffer_request_depth ------------------------------------------
   -- counts the number of items in request buffer

   function ib_switch_buffer_request_depth (header_num : integer; 
                                            data_width : integer) return integer is
      variable aux : integer;
   begin
      --aux := (C_IB_HEADER_WIDTH / data_width) * header_num;
      --
      --if ((aux mod 16) /= 0) then
      --   aux := aux + (16 - (aux mod 16));
      --end if;
      --
      --aux := aux / (C_IB_HEADER_WIDTH / data_width);

      aux := (C_IB_HEADER_WIDTH / data_width) * header_num;

      if (aux = 1) then
         aux := 2;
      else
         aux := header_num;
      end if;

      return aux;
   end ib_switch_buffer_request_depth;   

   -- addr_comparison_width ---------------------------------------------------
   -- counts the width of address part which is compared

   function addr_comparison_width (data_width : integer; 
                                   cmp_limit  : integer) return integer is   
      variable aux : integer;
   begin

      if (data_width <= cmp_limit) then
         aux := data_width;
      else
         aux := cmp_limit;
      end if;
      
      return aux;
   end addr_comparison_width; 

   -- addr_input_width --------------------------------------------------------
   -- counts the width of address in data word

   function addr_input_width (data_width : integer) return integer is   
      variable aux : integer;
   begin

      if (data_width <= 32) then
         aux := data_width;
      else
         aux := 32;
      end if;
      
      return aux;
   end addr_input_width;

   -- addr_extracted_from_data ------------------------------------------------
   -- extracts addr from data

   function addr_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                      data_width : integer) return t_rec128 is 
      variable aux : t_rec128;
   begin

      if (data_width <= 32) then
         aux.vec := data;
      else
         aux.vec := X"000000000000000000000000"&data(63 downto 32);
      end if;
      
      return aux;
   end addr_extracted_from_data;

   -- type_lg_extracted_from_data ---------------------------------------------
   -- extracts type_lg from data

   function type_lg_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                         data_width : integer) return std_logic is
      variable aux : std_logic;
   begin

      if (data_width = 1) then
         aux := data(0);
      else
         aux := data(1);
      end if;
      
      return aux;
   end type_lg_extracted_from_data; 

   -- cnt_bits_const ----------------------------------------------------------
   -- determines the value of const CNT_BITS
   
   function cnt_bits_const (addr_width : integer;
                            cmp_width  : integer) return integer is
      variable aux : integer;
   begin

      if (addr_width = cmp_width) then
         aux := 1;
      else
         aux := log2(addr_width/cmp_width);
      end if;
     
      return aux;
   end cnt_bits_const;     

   -- address_splitter_enable -------------------------------------------------
   -- determines the enable for address splitter generation

   function address_splitter_enable (data_width : integer;
                                     cmp_limit  : integer) return boolean is                                           
      variable aux : boolean;
   begin

      if (data_width > 32) then
         aux := (32 > cmp_limit);
      else
         aux := (data_width > cmp_limit);
      end if;
     
      return aux;
   end address_splitter_enable; 
        
end IB_SWITCH_PKG;



