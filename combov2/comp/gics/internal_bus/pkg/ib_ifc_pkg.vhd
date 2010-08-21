--
-- ib_ifc_pkg.vhd: Internal Bus Interfaces Package
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

-- ----------------------------------------------------------------------------
--                       Internal Bus Interfaces Package                     --
-- ----------------------------------------------------------------------------

package IB_IFC_PKG is

   -- -------------------------------------------------------------------------
   --                     Internal Bus Interface Types                       --
   -- -------------------------------------------------------------------------

   -- Component type --------------------------------------
   type t_ib_comp is (SWITCH_SLAVE, SWITCH_MASTER, ROOT);    
   
   -- Data width : 1 bit ----------------------------------
   type t_ib_link1 is record
      DATA       : std_logic_vector(0 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib1 is record
      UP         : t_ib_link1;
      DOWN       : t_ib_link1;
   end record;

   -- Data width : 2 bit ----------------------------------
   type t_ib_link2 is record
      DATA       : std_logic_vector(1 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib2 is record
      UP         : t_ib_link2;
      DOWN       : t_ib_link2;
   end record;   

   -- Data width : 4 bit ----------------------------------
   type t_ib_link4 is record
      DATA       : std_logic_vector(3 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib4 is record
      UP         : t_ib_link4;
      DOWN       : t_ib_link4;
   end record;   

   -- Data width : 8 bit ----------------------------------
   type t_ib_link8 is record
      DATA       : std_logic_vector(7 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib8 is record
      UP         : t_ib_link8;
      DOWN       : t_ib_link8;
   end record;   

   -- Data width : 16 bit ---------------------------------
   type t_ib_link16 is record
      DATA       : std_logic_vector(15 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib16 is record
      UP         : t_ib_link16;
      DOWN       : t_ib_link16;
   end record;   

   -- Data width : 32 bit ----------------------------------
   type t_ib_link32 is record
      DATA       : std_logic_vector(31 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib32 is record
      UP         : t_ib_link32;
      DOWN       : t_ib_link32;
   end record;   

   -- Data width : 64 bit ---------------------------------
   type t_ib_link64 is record
      DATA       : std_logic_vector(63 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib64 is record
      UP         : t_ib_link64;
      DOWN       : t_ib_link64;
   end record;   

   -- Data width : 128 bit --------------------------------
   type t_ib_link128 is record
      DATA       : std_logic_vector(127 downto 0);
      SOF_N      : std_logic;
      EOF_N      : std_logic;
      SRC_RDY_N  : std_logic;
      DST_RDY_N  : std_logic;
   end record;

   type t_ib128 is record
      UP         : t_ib_link128;
      DOWN       : t_ib_link128;
   end record;

   -- -------------------------------------------------------------------------
   --                         Read Interface Types                           --
   -- -------------------------------------------------------------------------  

   -- Read type -------------------------------------------
   type t_ibrd_type is (CONTINUAL, PACKET);     

   -- Data width : 8 bit ----------------------------------
   type t_ibrd8 is record
      REQ         : std_logic;                           
      ARDY_ACCEPT : std_logic;                           
      ADDR        : std_logic_vector(31 downto 0);        
      LENGTH      : std_logic_vector(11 downto 0);       
      SOF         : std_logic;                           
      EOF         : std_logic;                    

      DATA        : std_logic_vector(7 downto 0);             
      SRC_RDY     : std_logic;                           
      DST_RDY     : std_logic;                    
   end record;    

   -- Data width : 16 bit ---------------------------------
   type t_ibrd16 is record
      REQ         : std_logic;                           
      ARDY_ACCEPT : std_logic;                           
      ADDR        : std_logic_vector(31 downto 0);        
      BE          : std_logic_vector(1 downto 0);       
      LENGTH      : std_logic_vector(11 downto 0);       
      SOF         : std_logic;                           
      EOF         : std_logic;                    

      DATA        : std_logic_vector(15 downto 0);             
      SRC_RDY     : std_logic;                           
      DST_RDY     : std_logic;                    
   end record;       

   -- Data width : 32 bit ---------------------------------
   type t_ibrd32 is record
      REQ         : std_logic;                           
      ARDY_ACCEPT : std_logic;                           
      ADDR        : std_logic_vector(31 downto 0);        
      BE          : std_logic_vector(3 downto 0);       
      LENGTH      : std_logic_vector(11 downto 0);       
      SOF         : std_logic;                           
      EOF         : std_logic;                    

      DATA        : std_logic_vector(31 downto 0);             
      SRC_RDY     : std_logic;                           
      DST_RDY     : std_logic;                    
   end record;       

   -- Data width : 64 bit ---------------------------------
   type t_ibrd64 is record
      REQ         : std_logic;                           
      ARDY_ACCEPT : std_logic;                           
      ADDR        : std_logic_vector(31 downto 0);        
      BE          : std_logic_vector(7 downto 0);       
      LENGTH      : std_logic_vector(11 downto 0);       
      SOF         : std_logic;                           
      EOF         : std_logic;                    

      DATA        : std_logic_vector(63 downto 0);             
      SRC_RDY     : std_logic;                           
      DST_RDY     : std_logic;                    
   end record;       

   -- Data width : 128 bit --------------------------------
   type t_ibrd128 is record
      REQ         : std_logic;                           
      ARDY_ACCEPT : std_logic;                           
      ADDR        : std_logic_vector(31 downto 0);        
      BE          : std_logic_vector(15 downto 0);       
      LENGTH      : std_logic_vector(11 downto 0);       
      SOF         : std_logic;                           
      EOF         : std_logic;                    

      DATA        : std_logic_vector(127 downto 0);             
      SRC_RDY     : std_logic;                           
      DST_RDY     : std_logic;                    
   end record;          

   -- -------------------------------------------------------------------------
   --                        Write Interface Types                           --
   -- -------------------------------------------------------------------------   

   -- Data width : 8 bit ----------------------------------
   type t_ibwr8 is record
      REQ       : std_logic;                           
      RDY       : std_logic;                              
      DATA      : std_logic_vector(7 downto 0);       
      ADDR      : std_logic_vector(31 downto 0);       
      LENGTH    : std_logic_vector(11 downto 0);       
      SOF       : std_logic;                           
      EOF       : std_logic;                           
   end record; 

   -- Data width : 16 bit ---------------------------------
   type t_ibwr16 is record
      REQ       : std_logic;                           
      RDY       : std_logic;                              
      DATA      : std_logic_vector(15 downto 0);       
      ADDR      : std_logic_vector(31 downto 0);       
      BE        : std_logic_vector(1 downto 0);        
      LENGTH    : std_logic_vector(11 downto 0);       
      SOF       : std_logic;                           
      EOF       : std_logic;                           
   end record; 

   -- Data width : 32 bit ---------------------------------
   type t_ibwr32 is record
      REQ       : std_logic;                           
      RDY       : std_logic;                              
      DATA      : std_logic_vector(31 downto 0);       
      ADDR      : std_logic_vector(31 downto 0);       
      BE        : std_logic_vector(3 downto 0);        
      LENGTH    : std_logic_vector(11 downto 0);       
      SOF       : std_logic;                           
      EOF       : std_logic;                           
   end record; 

   -- Data width : 64 bit ---------------------------------
   type t_ibwr64 is record
      REQ       : std_logic;                           
      RDY       : std_logic;                              
      DATA      : std_logic_vector(63 downto 0);       
      ADDR      : std_logic_vector(31 downto 0);       
      BE        : std_logic_vector(7 downto 0);        
      LENGTH    : std_logic_vector(11 downto 0);       
      SOF       : std_logic;                           
      EOF       : std_logic;                           
   end record; 
 
   -- Data width : 128 bit --------------------------------
   type t_ibwr128 is record
      REQ       : std_logic;                           
      RDY       : std_logic;                              
      DATA      : std_logic_vector(127 downto 0);       
      ADDR      : std_logic_vector(31 downto 0);       
      BE        : std_logic_vector(15 downto 0);        
      LENGTH    : std_logic_vector(11 downto 0);       
      SOF       : std_logic;                           
      EOF       : std_logic;                           
   end record;  

   -- -------------------------------------------------------------------------
   --                       Bus Master Interface Types                       --
   -- -------------------------------------------------------------------------

   -- Done interface --------------------------------------
   type t_ibbm_done is record
      TAG     : std_logic_vector(7 downto 0);
      TAG_VLD : std_logic;
   end record;   

   -- BM interfaces with different widths -----------------
   type t_ibbm8 is record
      TRANS : t_ib_link8;
      DONE  : t_ibbm_done;
   end record;   

   type t_ibbm16 is record
      TRANS : t_ib_link16;
      DONE  : t_ibbm_done;
   end record;   

   type t_ibbm32 is record
      TRANS : t_ib_link32;
      DONE  : t_ibbm_done;
   end record;   

   type t_ibbm64 is record
      TRANS : t_ib_link64;
      DONE  : t_ibbm_done;
   end record;   

   type t_ibbm128 is record
      TRANS : t_ib_link128;
      DONE  : t_ibbm_done;
   end record;   

end IB_IFC_PKG;

-- ----------------------------------------------------------------------------
--                    Internal Bus Interfaces Package BODY                   --
-- ----------------------------------------------------------------------------

package body IB_IFC_PKG is
       
end IB_IFC_PKG;



