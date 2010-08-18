--
-- unpacker.vhd : IB Unpacker Entity
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
use work.ib_unpacker_pkg.all;

-- ----------------------------------------------------------------------------
--                     ENTITY DECLARATION -- IB Unpacker                     --
-- ----------------------------------------------------------------------------

entity IB_UNPACKER is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH   : integer := 64;
      -- Address Width (1-32)
      ADDR_WIDTH   : integer := 32
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK          : in std_logic;  
      RESET        : in std_logic;  

      -- Input interface ------------------------------------------------------
      DATA         : in std_logic_vector(DATA_WIDTH-1 downto 0);

      -- Output Interface -----------------------------------------------------
      LENGTH       : out std_logic_vector(11 downto 0);      
      COUNT        : out std_logic_vector(13-log2(DATA_WIDTH/8)-1 downto 0);      
      ADDR32       : out std_logic_vector(ADDR_WIDTH-1 downto 0); -- (32+ADDR_WIDTH-1):32
      ADDR64       : out std_logic_vector(ADDR_WIDTH-1 downto 0); -- (64+ADDR_WIDTH-1):64     
      LEN_ALIGN    : out std_logic_vector(unpck_align_width(DATA_WIDTH)-1 downto 0);      
      A32_ALIGN    : out std_logic_vector(unpck_align_width(DATA_WIDTH)-1 downto 0); -- 3?:32
      A64_ALIGN    : out std_logic_vector(unpck_align_width(DATA_WIDTH)-1 downto 0); -- 6?:64
      TAG          : out std_logic_vector(7 downto 0);
      DONE_FLAG    : out std_logic;

      -- Control Interface ----------------------------------------------------
      LENGTH_WE    : in std_logic_vector(unpck_length_we_width(DATA_WIDTH)-1 downto 0);      
      ADDR32_WE    : in std_logic_vector(unpck_addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0);                  
      ADDR64_WE    : in std_logic_vector(unpck_addr_we_width(DATA_WIDTH, ADDR_WIDTH)-1 downto 0);                        
      ADDR32_CE    : in std_logic;
      ADDR64_CE    : in std_logic;      
      COUNT_CE     : in std_logic;
      TAG_WE       : in std_logic;
      DONE_FLAG_WE : in std_logic;
      HEADER_LAST  : in std_logic
   );
end IB_UNPACKER;



