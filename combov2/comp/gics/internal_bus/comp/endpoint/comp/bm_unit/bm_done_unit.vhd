--
-- bm_done_unit.vhd : IB Endpoint Bus Master DONE unit
-- Copyright (C) 2008 CESNET
-- Author(s): Tomas Malek <tomalek@liberouter.org>
--            Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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

-- ----------------------------------------------------------------------------
--          ENTITY DECLARATION -- IB Endpoint Bus Master DONE Unit           -- 
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_BM_DONE_UNIT is 
   port (
      -- Common interface -----------------------------------------------------
      CLK            : in std_logic;  
      RESET          : in std_logic;  

      -- G2LR DONE interface --------------------------------------------------
      RD_TAG         : in std_logic_vector(7 downto 0);
      RD_TAG_VLD     : in std_logic;   
      RD_DONE        : in std_logic;   

      -- L2GW DONE interface --------------------------------------------------
      CPL_TAG        : in std_logic_vector(7 downto 0);
      CPL_TAG_VLD    : in std_logic;   

      -- BM DONE interface ----------------------------------------------------
      BM_TAG         : out std_logic_vector(7 downto 0);
      BM_TAG_VLD     : out std_logic               
   );
end IB_ENDPOINT_BM_DONE_UNIT;

-- ----------------------------------------------------------------------------
--       ARCHITECTURE DECLARATION  --  IB Endpoint Bus Master DONE Unit      --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_bm_done_unit_arch of IB_ENDPOINT_BM_DONE_UNIT is

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------
   
   signal rd_tag_reg       : std_logic_vector(7 downto 0);
   signal cpl_tag_reg      : std_logic_vector(7 downto 0);
   signal rd_start_reg     : std_logic;
   signal cpl_tag_vld_reg  : std_logic;
   signal local_op_done    : std_logic;
   signal tag_mux          : std_logic_vector(7 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                              OUTPUT LOGIC                              --
   -- -------------------------------------------------------------------------
   
   BM_TAG           <= tag_mux;
   BM_TAG_VLD       <= cpl_tag_vld_reg or local_op_done;

   local_op_done    <= RD_DONE and rd_start_reg;   
   
   tag_muxp: process(local_op_done, rd_tag_reg, cpl_tag_reg)
   begin
      case local_op_done is
         when '0' => tag_mux <= cpl_tag_reg;
         when '1' => tag_mux <= rd_tag_reg;
         when others => tag_mux <= (others => 'X');
      end case;
   end process;

   -- -------------------------------------------------------------------------
   --                                RD PART                                 --
   -- -------------------------------------------------------------------------
   
   rd_start_regp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         rd_start_reg <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (RD_TAG_VLD = '1') then
            rd_start_reg <= '1';
         end if;
         if (RD_DONE = '1') then
            rd_start_reg <= '0';
         end if;
      end if;
   end process;
   
   rd_tag_regp: process(RESET, CLK)
   begin
     if (CLK'event AND CLK = '1') then
         if (RD_TAG_VLD = '1') then
            rd_tag_reg <= RD_TAG;
         end if;
      end if;
   end process;
   
   -- -------------------------------------------------------------------------
   --                                CPL PART                                --
   -- -------------------------------------------------------------------------
   
   cpl_tag_regp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CPL_TAG_VLD = '1') then
            cpl_tag_reg <= CPL_TAG;
         end if;
      end if;
   end process;   
   
   cpl_tag_vld_regp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cpl_tag_vld_reg <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (CPL_TAG_VLD = '1') then
            cpl_tag_vld_reg <= '1';
         elsif (local_op_done = '0') then
            cpl_tag_vld_reg <= '0';
         end if;
      end if;
   end process;
   
end ib_endpoint_bm_done_unit_arch;

                     

