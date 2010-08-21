--
-- done_unit.vhd : IB Endpoint Down Buffer Done Unit
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
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--         ENTITY DECLARATION -- IB Endpoint Down Buffer Done Unit           -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_DOWN_BUF_DONE_UNIT is 
   generic(
      -- Data Width (8-128)
      DATA_WIDTH   : integer:= 64
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK              : in std_logic;  
      RESET            : in std_logic;  

      -- Packed Header interface ----------------------------------------------
      IN_DATA          : in std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_SOF_N         : in std_logic;
      IN_EOF_N         : in std_logic;
      IN_SRC_RDY_N     : in std_logic;
      IN_DST_RDY_N     : in std_logic;

      -- Control Interface ----------------------------------------------------
      IN_TAG_VLD       : in std_logic;
      IN_TYPE_VLD      : in std_logic;
      IN_REQ           : in std_logic;

      -- Done Interface -------------------------------------------------------
      OUT_TAG          : out std_logic_vector(7 downto 0);      
      OUT_TAG_VLD      : out std_logic;
      OUT_DONE         : out std_logic
   );
end IB_ENDPOINT_DOWN_BUF_DONE_UNIT;

-- ----------------------------------------------------------------------------
--      ARCHITECTURE DECLARATION  --  IB Endpoint Down Buffer Done Unit      --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_down_buf_done_unit_arch of IB_ENDPOINT_DOWN_BUF_DONE_UNIT is

   constant ZEROES     : std_logic_vector(128-DATA_WIDTH-1 downto 0) := (others => '0');
   
   signal done_reg : std_logic;  
                                                                                                   
begin

   -- -------------------------------------------------------------------------
   --                            DATA_WIDTH < 32                             --
   -- -------------------------------------------------------------------------

   DATA_WIDTH_LT_32: if (DATA_WIDTH < 32) generate

      done_regp: process(RESET, CLK)
      begin
        if (CLK'event AND CLK = '1') then
            if (RESET = '1') then
               done_reg <= '0';
            else
               if (IN_TYPE_VLD = '1' and IN_SOF_N = '0' and IN_REQ = '1') then
                  done_reg <= IN_DATA(C_IB_TYPE_LAST);
               end if;
               if (IN_EOF_N = '0') then
                  done_reg <= '0';
               end if;
            end if;         
         end if;
      end process; 

      OUT_TAG     <= tag_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH).VEC;

      OUT_TAG_VLD <= done_reg and IN_TAG_VLD and not IN_SRC_RDY_N and not IN_DST_RDY_N;

      OUT_DONE    <= not IN_EOF_N; 

   end generate;

   -- -------------------------------------------------------------------------
   --                            DATA_WIDTH >= 32                            --
   -- -------------------------------------------------------------------------

   DATA_WIDTH_GTEQ_32: if (DATA_WIDTH >= 32) generate

      OUT_TAG     <= tag_extracted_from_data(ZEROES&IN_DATA, DATA_WIDTH).VEC;

      OUT_TAG_VLD <= not IN_SOF_N and IN_DATA(C_IB_TYPE_LAST) and IN_REQ;

      OUT_DONE    <= not IN_EOF_N; 

   end generate;   
    
end ib_endpoint_down_buf_done_unit_arch;

                     

