--
-- transformer_pkg.vhd: Internal Bus Transformer Package
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
--                      Internal Bus Transformer Package                     --
-- ----------------------------------------------------------------------------

package IB_TRANSFORMER_PKG is

   -- -------------------------------------------------------------------------
   --                                TYPES                                   --
   -- -------------------------------------------------------------------------

   type t_rec128 is record
      VEC : std_logic_vector(127 downto 0);
   end record; 

   -- -------------------------------------------------------------------------
   --                         FUNCTION PROTOTYPES                            --
   -- -------------------------------------------------------------------------

   function boolean2integer (bool  : boolean) return integer;

   function part_sel_width (in_data_width  : integer; 
                            out_data_width : integer) return integer;

   function align_we_width (in_data_width  : integer; 
                            out_data_width : integer) return integer;

   function align_width (in_data_width  : integer; 
                         out_data_width : integer) return integer;                            

   function addr_align_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                            data_width : integer) return t_rec128;

   function len_align_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                           data_width : integer) return t_rec128;                                                                  

end IB_TRANSFORMER_PKG;

-- ----------------------------------------------------------------------------
--                     Internal Bus Transformer Package BODY                 --
-- ----------------------------------------------------------------------------

package body IB_TRANSFORMER_PKG is

   -- -------------------------------------------------------------------------
   --                          FUNCTION BODIES                               --
   -- -------------------------------------------------------------------------

   -- boolean2integer ---------------------------------------------------------
   -- converts boolean to integer

   function boolean2integer (bool  : boolean) return integer is
      variable aux : integer;
   begin
      if (bool) then
         aux := 1;
      else
         aux := 0;
      end if;
   
      return aux;
   end boolean2integer;

   -- part_sel_width ----------------------------------------------------------
   -- counts the width of first/last part_sel signal

   function part_sel_width (in_data_width  : integer; 
                            out_data_width : integer) return integer is
      variable aux : integer;
   begin
  
      aux := log2( max(IN_DATA_WIDTH,OUT_DATA_WIDTH)/work.math_pack.min(IN_DATA_WIDTH,OUT_DATA_WIDTH) );
   
      return aux;
   end part_sel_width; 

   -- align_we_width ----------------------------------------------------------
   -- counts the width of align write enable signal

   function align_we_width (in_data_width  : integer; 
                            out_data_width : integer) return integer is
      variable aux : integer;
   begin
       
      aux := max(IN_DATA_WIDTH,OUT_DATA_WIDTH)/8;

      if (aux <= 1) then
         aux := 1;
      else      
         aux := log2(max(IN_DATA_WIDTH,OUT_DATA_WIDTH)/8);
         
         if (IN_DATA_WIDTH = 1) then
            aux := aux;
         elsif (IN_DATA_WIDTH = 2) then
            aux := (aux+1)/2;
         else
            aux := 1;
         end if;   
      end if;
   
      return aux;
   end align_we_width;    

   -- align_width -------------------------------------------------------------
   -- counts the width of align

   function align_width (in_data_width  : integer; 
                         out_data_width : integer) return integer is
      variable aux : integer;
   begin
  
      aux := max(IN_DATA_WIDTH,OUT_DATA_WIDTH)/8;

      if (aux <= 1) then
         aux := 1;
      else
         aux := log2(max(IN_DATA_WIDTH,OUT_DATA_WIDTH)/8);
      end if;   
   
      return aux;
   end align_width;       

   -- addr_align_extracted_from_data ------------------------------------------
   -- extracts address alignment from data

   function addr_align_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                            data_width : integer) return t_rec128 is 
      variable aux : t_rec128;
   begin

      if (data_width <= 32) then
         aux.vec := data;
      else
         aux.vec := X"000000000000000000000000"&data(63 downto 32);
      end if;
      
      return aux;
   end addr_align_extracted_from_data; 

   -- len_align_extracted_from_data -------------------------------------------
   -- extracts length alignment from data

   function len_align_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                           data_width : integer) return t_rec128 is 
      variable aux    : t_rec128;
   begin

      if (data_width <= 4) then
         aux.vec := data;
      else
         aux.vec := X"0000000000000000000000000000000"&data(7 downto 4);
      end if;
      
      return aux;
   end len_align_extracted_from_data;    
   
end IB_TRANSFORMER_PKG;



