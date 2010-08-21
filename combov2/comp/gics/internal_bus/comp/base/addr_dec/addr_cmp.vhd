--
-- addr_cmp.vhd : Address Comparator
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

-- ----------------------------------------------------------------------------
--                    ENTITY DECLARATION -- Address Comparator               -- 
-- ----------------------------------------------------------------------------

entity ADDR_CMP is 
   generic(
      WIDTH    : integer:= 64;   -- width of operators to be compared
      CMP_TYPE : string := "LT"  -- comparison type ("LT"/"GT_EQ")
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK       : in std_logic;
      RESET     : in std_logic;
   
      -- Input interface ------------------------------------------------------
      CONST     : in std_logic_vector(WIDTH-1 downto 0);            
      ADDR      : in std_logic_vector(WIDTH-1 downto 0);
      ADDR_WE   : in std_logic;
      ADDR_NEXT : in std_logic;

      -- Output interface -----------------------------------------------------
      HIT       : out std_logic
   );
end ADDR_CMP;

-- ----------------------------------------------------------------------------
--               ARCHITECTURE DECLARATION  --  Address Comparator            --
-- ----------------------------------------------------------------------------

architecture addr_cmp_arch of ADDR_CMP is

   signal reg_history : std_logic;
   signal eq          : std_logic;
   signal lt_gt       : std_logic;
   signal hit_aux     : std_logic;
   signal reset_value : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                               COMPARATOR                               --
   -- ------------------------------------------------------------------------- 

   U_comparator: entity work.COMPARATOR 
   generic map (
      WIDTH  => WIDTH
   )
   port map (
      -- Input interface --
      ADDR   => ADDR,  
      CONST  => CONST,
      -- Output interface --
      EQ     => eq,
      LT_GT  => lt_gt
   );

   -- -------------------------------------------------------------------------
   --                            HISTORY REGISTER                            --
   -- -------------------------------------------------------------------------   

   reg_historyp: process(RESET, CLK, reset_value)
   begin
     if (CLK'event AND CLK = '1') then
        if (RESET = '1') then
           reg_history <= reset_value;
        else
           if (ADDR_WE = '1') then
               reg_history <= hit_aux;
           end if;
           if (ADDR_NEXT = '1') then
               reg_history <= reset_value;
           end if;        
        end if;
     end if;
   end process;

   LT_RESET: if (CMP_TYPE = "LT") generate
      reset_value <= '0';
   end generate;

   GT_EQ_RESET: if (CMP_TYPE = "GT_EQ") generate
      reset_value <= '1';   
   end generate;     

   -- -------------------------------------------------------------------------
   --                               HIT LOGIC                                --
   -- -------------------------------------------------------------------------

   LT_GENERATE: if (CMP_TYPE = "LT") generate
      with eq select
         hit_aux <= not lt_gt   when '0',
                    reg_history when others;
   end generate;

   GT_EQ_GENERATE: if (CMP_TYPE = "GT_EQ") generate
      with eq select
         hit_aux <= lt_gt       when '0',
                    reg_history when others;
   end generate;   

   HIT <= hit_aux;

end addr_cmp_arch;

                     

