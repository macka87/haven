-- mask.vhd: Masks input FL acording mask.
-- Copyright (C) 2009 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: MASK
-- ----------------------------------------------------------------------------
entity MASK is
   generic(
      -- the data width of the data input/output
      DATA_WIDTH     : integer := 128;
      -- defines UH size in bytes; min 16 - 128 bytes
      UH_SIZE        : integer := 64
   );
   port(
      -- common signals
      -- global FGPA clock
      CLK               : in  std_logic;

      -- global synchronous reset
      RESET             : in  std_logic;
      
      -- RX Framelink interface
      RX_DATA           : in  std_logic_vector(DATA_WIDTH - 1 downto 0);
      RX_REM            : in  std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
      RX_SOF_N          : in  std_logic;
      RX_EOF_N          : in  std_logic;
      RX_SOP_N          : in  std_logic;
      RX_EOP_N          : in  std_logic;
      RX_SRC_RDY_N      : in  std_logic;
      RX_DST_RDY_N      : out std_logic;
   

      -- TX FrameLink interface
      TX_DATA           : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      TX_REM            : out std_logic_vector(log2(DATA_WIDTH / 8 ) - 1 downto 0);
      TX_SOF_N          : out std_logic;
      TX_EOF_N          : out std_logic;
      TX_SOP_N          : out std_logic;
      TX_EOP_N          : out std_logic;
      TX_SRC_RDY_N      : out std_logic;
      TX_DST_RDY_N      : in  std_logic;
      
      -- Masking input, typically constant
      MASK              : in std_logic_vector(UH_SIZE-1 downto 0)
   );
end entity MASK;

-- ----------------------------------------------------------------------------
--  Architecture: MASK
-- ----------------------------------------------------------------------------
architecture full of MASK is
   type t_reg_mask   is array((UH_SIZE-1)/16 downto 0) of 
                        std_logic_vector(127 downto 0);
                        
    -- mask logic signals
   signal reg_mask      : t_reg_mask;  
   signal cnt_mask      : std_logic_vector(log2((UH_SIZE-1)/16+1)-1 downto 0);
   signal cnt_mask_adv  : std_logic;
   constant uh_words      : std_logic_vector(log2((UH_SIZE-1)/16+1)-1 downto 0)
      := conv_std_logic_vector((UH_SIZE-1)/16, log2((UH_SIZE-1)/16+1));
begin
   TX_DATA        <= reg_mask(conv_integer(cnt_mask)) and RX_DATA;
   TX_REM         <= RX_REM;
   TX_SOF_N       <= RX_SOF_N;
   TX_SOP_N       <= RX_SOP_N;
   TX_EOP_N       <= RX_EOP_N;
   TX_EOF_N       <= RX_EOF_N;
   TX_SRC_RDY_N   <= RX_SRC_RDY_N;
   RX_DST_RDY_N   <= TX_DST_RDY_N;
   
   cnt_mask_adv <= (not RX_SRC_RDY_N) and (not TX_DST_RDY_N);
   
   -- cnt_reg_mask counter
   cnt_maskp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            cnt_mask <= (others => '0');
         elsif (cnt_mask_adv = '1') then
            if (cnt_mask = uh_words) then
               cnt_mask <= (others => '0');
            else
               cnt_mask <= cnt_mask + 1;
            end if;
         end if;
      end if;
   end process;
   
   -- mask register
   GEN_REG_MASK: for i in UH_SIZE-1 downto 0 generate
   begin
         reg_maskp: process(CLK)
         begin
            if (CLK'event and CLK = '1') then
               if (MASK(i) = '0') then
                  reg_mask(i/16)(7+(i mod 16)*8 downto 0+(i mod 16)*8) <= (others => '0');
               else
                  reg_mask(i/16)(7+(i mod 16)*8 downto 0+(i mod 16)*8) <= (others => '1');
               end if;
            end if;
         end process;
   end generate;
   
end architecture full;
