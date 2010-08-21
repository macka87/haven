--
-- endpoint_pkg.vhd: Internal Bus Endpoint Package
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
--                      Internal Bus Endpoint Package                        --
-- ----------------------------------------------------------------------------

package IB_ENDPOINT_PKG is

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

   function ib_endpoint_read_ctrl_pck_hbuf_depth (header_num : integer; 
                                                  data_width : integer) return integer;

   function ib_endpoint_read_ctrl_unpck_hbuf_depth (header_num : integer; 
                                                    data_width : integer) return integer;                                                  

   function ib_endpoint_addr_dec_buffer_data_depth (header_num : integer; 
                                                    data_width : integer) return integer;

   function ib_endpoint_addr_dec_buffer_req_depth (header_num : integer; 
                                                   data_width : integer) return integer;

   function addr_comparison_width (data_width : integer; 
                                   cmp_limit  : integer) return integer;

   function addr_input_width (data_width : integer) return integer;                                   

   function addr32_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                        data_width : integer) return t_rec128;

   function tag_extracted_from_data  (data       : std_logic_vector(127 downto 0); 
                                      data_width : integer) return t_rec8;       

   function align_width (data_width : integer) return integer; 

   function length_we_width (data_width : integer) return integer;

   function addr_we_width (data_width : integer;
                           addr_width : integer) return integer;

end IB_ENDPOINT_PKG;

-- ----------------------------------------------------------------------------
--                    Internal Bus Endpoint Package BODY                     --
-- ----------------------------------------------------------------------------

package body IB_ENDPOINT_PKG is

   -- -------------------------------------------------------------------------
   --                          FUNCTION BODIES                               --
   -- -------------------------------------------------------------------------

   -- ib_endpoint_read_ctrl_pck_hbuf_depth ------------------------------------
   -- counts the number of items in packed header buffer

   function ib_endpoint_read_ctrl_pck_hbuf_depth (header_num : integer; 
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
   end ib_endpoint_read_ctrl_pck_hbuf_depth;

   -- ib_endpoint_read_ctrl_unpck_hbuf_depth ----------------------------------
   -- counts the number of items in unpacked header buffer

   function ib_endpoint_read_ctrl_unpck_hbuf_depth (header_num : integer; 
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
   end ib_endpoint_read_ctrl_unpck_hbuf_depth;     

   -- ib_endpoint_addr_dec_buffer_data_depth ----------------------------------
   -- counts the number of items in data buffer

   function ib_endpoint_addr_dec_buffer_data_depth (header_num : integer; 
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
   end ib_endpoint_addr_dec_buffer_data_depth; 

   -- ib_endpoint_addr_dec_buffer_req_depth -----------------------------------
   -- counts the number of items in request buffer

   function ib_endpoint_addr_dec_buffer_req_depth (header_num : integer; 
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
   end ib_endpoint_addr_dec_buffer_req_depth;  

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

   -- addr32_extracted_from_data ----------------------------------------------
   -- extracts addr from data

   function addr32_extracted_from_data (data       : std_logic_vector(127 downto 0); 
                                        data_width : integer) return t_rec128 is 
      variable aux : t_rec128;
   begin

      if (data_width <= 32) then
         aux.vec := data;
      else
         aux.vec := X"000000000000000000000000"&data(63 downto 32);
      end if;
      
      return aux;
   end addr32_extracted_from_data;

   -- tag_extracted_from_data ------------------------------------------------
   -- extracts tag from data

   function tag_extracted_from_data  (data       : std_logic_vector(127 downto 0); 
                                      data_width : integer) return t_rec8 is
      variable aux : t_rec8;
   begin

      if (data_width < 32) then
         aux.vec := data(7 downto 0);
      else
         aux.vec := data(23 downto 16);
      end if;
      
      return aux;
   end tag_extracted_from_data;  

   -- align_width -------------------------------------------------------------
   -- counts the width of address alignment for BE generation

   function align_width (data_width : integer) return integer is   
      variable aux : integer;
   begin

      if (data_width = 8) then
         aux := 1;
      else
         aux := log2(data_width/8);
      end if;
      
      return aux;
   end align_width;   

   -- length_we_width ---------------------------------------------------------
   -- counts the number of parts which length register is composed of

   function length_we_width (data_width : integer) return integer is   
      variable aux : integer;
   begin

      if (data_width = 8) then
         aux := 2;
      else
         aux := 1;
      end if;
      
      return aux;
   end length_we_width;      

   -- addr_we_width -----------------------------------------------------------
   -- counts the number of parts which address register is composed of

   function addr_we_width (data_width : integer;
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
   end addr_we_width;
    
end IB_ENDPOINT_PKG;



