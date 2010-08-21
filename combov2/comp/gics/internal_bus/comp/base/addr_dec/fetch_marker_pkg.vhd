--
-- fetch_marker_pkg.vhd: Address Decoder Fetch Marker Package
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
--                   Address Decoder Fetch Marker Package                    --
-- ----------------------------------------------------------------------------

package ADDR_DEC_FETCH_MARKER_PKG is

   -- -------------------------------------------------------------------------
   --                                TYPES                                   --
   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   --                         FUNCTION PROTOTYPES                            --
   -- -------------------------------------------------------------------------

   function addr_input_width (data_width : integer) return integer;                                   

   function serial_cmp_of_addr (data_width : integer;
                                cmp_width  : integer) return boolean;

   function cnt_bits_const (addr_width : integer;
                            cmp_width  : integer) return integer;

   function type_lg_we_reg_cyc_width (data_width : integer) return integer;

   function addr_start_reg_cyc_width (data_width   : integer;
                                      cmp_parallel : boolean) return integer;

   function addr_last_reg_cyc_width (data_width    : integer;
                                     cmp_parallel  : boolean) return integer;   

end ADDR_DEC_FETCH_MARKER_PKG;

-- ----------------------------------------------------------------------------
--                   Address Decoder Fetch Marker Package BODY               --
-- ----------------------------------------------------------------------------

package body ADDR_DEC_FETCH_MARKER_PKG is

   -- -------------------------------------------------------------------------
   --                          FUNCTION BODIES                               --
   -- -------------------------------------------------------------------------

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

   -- serial_cmp_of_addr ------------------------------------------------------
   -- determines if comparison is serial

   function serial_cmp_of_addr (data_width : integer;
                                cmp_width  : integer) return boolean is
      variable aux : boolean;
   begin

      if (data_width = cmp_width) then
         aux := TRUE;
      else
         aux := FALSE;
      end if;
      
      return aux;
   end serial_cmp_of_addr;    

   -- type_lg_we_reg_cyc_width ------------------------------------------------
   -- determines the width of type_lg_we time mark sh_register

   function type_lg_we_reg_cyc_width (data_width : integer) return integer is
      variable aux : integer;
   begin

      if (data_width = 1) then
         aux := 2;
      else
         aux := 1;
      end if;
      
      return aux;
   end type_lg_we_reg_cyc_width; 

   -- addr_start_reg_cyc_width ------------------------------------------------
   -- determines the width of addr_start time mark sh_register   

   function addr_start_reg_cyc_width (data_width   : integer;
                                      cmp_parallel : boolean) return integer is 
      variable aux : integer;
   begin

      if (data_width < 64) then
         if (cmp_parallel) then
            aux := 32/data_width + 1;
         else
            aux := 32/data_width;
         end if;
      else
         aux := 1;
      end if;
      
      return aux;
   end addr_start_reg_cyc_width;

   -- addr_last_reg_cyc_width -------------------------------------------------
   -- determines the width of addr_start time mark sh_register      

   function addr_last_reg_cyc_width (data_width    : integer;
                                     cmp_parallel  : boolean) return integer is 
      variable aux : integer;
   begin

      if (data_width < 32) then
         if (cmp_parallel) then
            aux := 32/data_width + 1;
         else
            aux := 32/data_width;
         end if;
      else
         aux := 1;
      end if;
      
      return aux;
   end addr_last_reg_cyc_width;   

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
     
end ADDR_DEC_FETCH_MARKER_PKG;



