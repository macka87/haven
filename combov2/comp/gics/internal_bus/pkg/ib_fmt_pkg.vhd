--
-- ib_fmt_pkg.vhd: Internal Bus Transaction Format Package
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
--                   Internal Bus Transaction Format Package                 --
-- ----------------------------------------------------------------------------

package IB_FMT_PKG is

   -- -------------------------------------------------------------------------
   --                  Internal Bus Transaction Format Constants             --
   -- -------------------------------------------------------------------------

   constant C_IB_HEADER_BASE            : integer :=   0;
   constant C_IB_HEADER_WIDTH           : integer := 128;
   constant C_IB_HEADER_LIMIT           : integer := C_IB_HEADER_BASE+C_IB_HEADER_WIDTH-1;   

   constant C_IB_TYPE_BASE              : integer :=   0;
   constant C_IB_TYPE_WIDTH             : integer :=   4;   
   constant C_IB_TYPE_LIMIT             : integer := C_IB_TYPE_BASE+C_IB_TYPE_WIDTH-1;   

   constant C_IB_LENGTH_BASE            : integer :=   4;
   constant C_IB_LENGTH_WIDTH           : integer :=  12;
   constant C_IB_LENGTH_LIMIT           : integer := C_IB_LENGTH_BASE+C_IB_LENGTH_WIDTH-1;   

   constant C_IB_TAG_BASE               : integer :=  16;
   constant C_IB_TAG_WIDTH              : integer :=   8;   
   constant C_IB_TAG_LIMIT              : integer := C_IB_TAG_BASE+C_IB_TAG_WIDTH-1;   

   constant C_IB_PRIMAR_ADDR_BASE       : integer :=  32;
   constant C_IB_PRIMAR_ADDR_WIDTH      : integer :=  32;   
   constant C_IB_PRIMAR_ADDR_LIMIT      : integer := C_IB_PRIMAR_ADDR_BASE+C_IB_PRIMAR_ADDR_WIDTH-1;   

   constant C_IB_SECUNDAR_ADDR_BASE     : integer :=  64;
   constant C_IB_SECUNDAR_ADDR_WIDTH    : integer :=  32;      
   constant C_IB_SECUNDAR_ADDR_LIMIT    : integer := C_IB_SECUNDAR_ADDR_BASE+C_IB_SECUNDAR_ADDR_WIDTH-1;      

   constant C_IB_PRIMAR_ADDR_HIGH_BASE  : integer :=  96;
   constant C_IB_PRIMAR_ADDR_HIGH_WIDTH : integer :=  32;   
   constant C_IB_PRIMAR_ADDR_HIGH_LIMIT : integer := C_IB_PRIMAR_ADDR_HIGH_BASE+C_IB_PRIMAR_ADDR_HIGH_WIDTH-1;      
      
   -- -------------------------------------------------------------------------
   --                  Internal Bus Transaction Types Constants              --
   -- -------------------------------------------------------------------------   

   -- 3.bit: not last/last, 2.bit: norm/cpl, 1.bit: local/global, 0.bit: no data/with data
   constant C_IB_L2LR : std_logic_vector(3 downto 0) := "0000";
   constant C_IB_L2LW : std_logic_vector(3 downto 0) := "0001";
   constant C_IB_G2LR : std_logic_vector(3 downto 0) := "0010";
   constant C_IB_L2GW : std_logic_vector(3 downto 0) := "0011";
   constant C_IB_RDC  : std_logic_vector(3 downto 0) := "0101";
   constant C_IB_RDCL : std_logic_vector(3 downto 0) := "1101";    

   constant C_IB_TYPE_DATA : integer :=  0;   
   constant C_IB_TYPE_GLOB : integer :=  1;   
   constant C_IB_TYPE_CPL  : integer :=  2;
   constant C_IB_TYPE_LAST : integer :=  3;

end IB_FMT_PKG;

-- ----------------------------------------------------------------------------
--                Internal Bus Transaction Format Package BODY               --
-- ----------------------------------------------------------------------------

package body IB_FMT_PKG is
       
end IB_FMT_PKG;



