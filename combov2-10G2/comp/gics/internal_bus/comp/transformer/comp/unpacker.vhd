--
-- unpacker.vhd : IB Transformer Unpacker
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
use work.ib_transformer_pkg.all;

-- ----------------------------------------------------------------------------
--               ENTITY DECLARATION -- IB Transformer Unpacker               --
-- ----------------------------------------------------------------------------

entity IB_TRANSFORMER_UNPACKER is 
   generic(
      -- Input Data Width (1-128)
      IN_DATA_WIDTH   : integer := 64;
      -- Output Data Width (1-128)
      OUT_DATA_WIDTH  : integer :=  8      
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK             : in std_logic;  
      RESET           : in std_logic;  

      -- Input interface ------------------------------------------------------
      DATA            : in std_logic_vector(IN_DATA_WIDTH-1 downto 0);

      -- Output Interface -----------------------------------------------------
      FIRST_PART_SEL  : out std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);      
      LAST_PART_SEL   : out std_logic_vector(part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);
      PAYLOAD_FLAG    : out std_logic;

      -- Control Interface ----------------------------------------------------
      LEN_ALIGN_WE    : in std_logic_vector(align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);      
      ADDR_ALIGN_WE   : in std_logic_vector(align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH)-1 downto 0);                  
      PAYLOAD_FLAG_WE : in std_logic
   );
end IB_TRANSFORMER_UNPACKER;

-- ----------------------------------------------------------------------------
--            ARCHITECTURE DECLARATION  --  IB Transformer Unpacker          --
-- ----------------------------------------------------------------------------

architecture ib_transformer_unpacker_arch of IB_TRANSFORMER_UNPACKER is

   -- -------------------------------------------------------------------------
   --                         Constant declaration                           --
   -- -------------------------------------------------------------------------

   constant ALIGN_PARTS_NUM  : integer := align_we_width(IN_DATA_WIDTH,OUT_DATA_WIDTH);
   constant PART_SEL_WIDTH   : integer := part_sel_width(IN_DATA_WIDTH,OUT_DATA_WIDTH);
   constant ALIGN_WIDTH      : integer := align_width(IN_DATA_WIDTH,OUT_DATA_WIDTH);

   constant ZEROES           : std_logic_vector(128-IN_DATA_WIDTH-1 downto 0) := (others => '0');
   constant PART_SEL_ZEROES  : std_logic_vector(PART_SEL_WIDTH-1 downto 0)    := (others => '0');
   constant PART_SEL_ONES    : std_logic_vector(PART_SEL_WIDTH-1 downto 0)    := (others => '1');   

   -- -------------------------------------------------------------------------
   --                           Signal declaration                           --
   -- -------------------------------------------------------------------------

   signal reg_payload_flag   : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
   signal reg_len_align      : std_logic_vector(ALIGN_PARTS_NUM*IN_DATA_WIDTH-1 downto 0);
   signal reg_addr_align     : std_logic_vector(ALIGN_PARTS_NUM*IN_DATA_WIDTH-1 downto 0);
   signal last_part_sel_aux  : std_logic_vector(ALIGN_WIDTH-1 downto 0);
                                                                        
begin

   -- -------------------------------------------------------------------------
   --                            LENGTH ALIGN REGISTER                       --
   -- -------------------------------------------------------------------------

   LEN_GEN: if (IN_DATA_WIDTH > 8 or OUT_DATA_WIDTH > 8) generate

      -- individual parts of length align register --------
      reg_len_alignp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
         
            -- write enabling
            for i in 0 to ALIGN_PARTS_NUM-1 loop
               if (LEN_ALIGN_WE(i) = '1') then
                  reg_len_align((i+1)*IN_DATA_WIDTH -1 downto i*IN_DATA_WIDTH) <= 
                     len_align_extracted_from_data(ZEROES&DATA, IN_DATA_WIDTH).VEC(IN_DATA_WIDTH-1 downto 0);
               end if;
            end loop;           
                    
         end if;         
      end process;

   end generate;

   -- -------------------------------------------------------------------------
   --                            ADDRESS ALIGN REGISTER                      --
   -- -------------------------------------------------------------------------

   ADDR_GEN: if (IN_DATA_WIDTH > 8 or OUT_DATA_WIDTH > 8) generate

      -- individual parts of address align register -------
      reg_addr_alignp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
         
            -- write enabling
            for i in 0 to ALIGN_PARTS_NUM-1 loop
               if (ADDR_ALIGN_WE(i) = '1') then
                  reg_addr_align((i+1)*IN_DATA_WIDTH -1 downto i*IN_DATA_WIDTH) <= 
                     addr_align_extracted_from_data(ZEROES&DATA, IN_DATA_WIDTH).VEC(IN_DATA_WIDTH-1 downto 0);
               end if;
            end loop;           
                    
         end if;         
      end process;

   end generate;   

   -- -------------------------------------------------------------------------
   --                          PAYLOAD FLAG REGISTER                         --
   -- -------------------------------------------------------------------------   

   -- payload flag register -------------------------------
   reg_payload_flagp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then

         if (PAYLOAD_FLAG_WE = '1') then
            reg_payload_flag <= DATA;
         end if;

      end if;
   end process;

   -- payload flag output assignment ----------------------
   PAYLOAD_FLAG <= reg_payload_flag(C_IB_TYPE_DATA);

   -- -------------------------------------------------------------------------
   --                          SELECTORS FOR LENGTH <= 8                     --
   -- -------------------------------------------------------------------------

   SEL_LE8: if (IN_DATA_WIDTH <= 8 and OUT_DATA_WIDTH <= 8) generate
   
      FIRST_PART_SEL <= PART_SEL_ZEROES;
      LAST_PART_SEL  <= PART_SEL_ONES;  
      
   end generate;

   -- -------------------------------------------------------------------------
   --                          SELECTORS FOR LENGTH > 8                      --
   -- -------------------------------------------------------------------------

   SEL_GT8: if (max(IN_DATA_WIDTH,OUT_DATA_WIDTH) > 8) generate
   
      -- first part selector ------------------------------
      FIRST_PART_SEL <= reg_addr_align(ALIGN_WIDTH-1 downto ALIGN_WIDTH - PART_SEL_WIDTH);
      
      -- last part selector -------------------------------
      last_part_sel_aux <= reg_len_align(ALIGN_WIDTH-1 downto 0) + reg_addr_align(ALIGN_WIDTH-1 downto 0) - 1;
      
      LAST_PART_SEL  <= last_part_sel_aux(ALIGN_WIDTH-1 downto ALIGN_WIDTH - PART_SEL_WIDTH);
      
   end generate;   

end ib_transformer_unpacker_arch;

                     
 
