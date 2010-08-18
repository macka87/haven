--
-- be_gen.vhd : IB Byte Enable Generator Entity
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

use work.math_pack.all;
use work.ib_ifc_pkg.all; 
use work.ib_fmt_pkg.all; 

-- ----------------------------------------------------------------------------
--              ENTITY DECLARATION -- IB Byte Enable Generator               -- 
-- ----------------------------------------------------------------------------

entity IB_BE_GEN is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH : integer:= 64
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  
      
      -- Input Interface ------------------------------------------------------
      LENGTH_ALIGN : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      ADDR_ALIGN   : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      SOF          : in  std_logic;
      EOF          : in  std_logic;
      
      -- Output Interface -----------------------------------------------------
      BE           : out std_logic_vector(DATA_WIDTH/8-1 downto 0)
   );
end IB_BE_GEN;



