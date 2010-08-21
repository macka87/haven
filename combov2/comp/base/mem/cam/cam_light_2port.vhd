-- cam_light_2port.vhd: 2 port (Match, Write) Lightweight CAM
-- Copyright (C) 2009 CESNET
-- Author(s): Martin kosek <kosek@liberouter.org>
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
-- NOTICE:  when clearing and writing to the same address, WRITE has higher priority
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CAM_2PORT is
   generic (
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer
   );
   port (
      -- common interface
      CLK               : in std_logic;
      RESET             : in std_logic;
      
      -- insert interface
      ADDR              : in std_logic_vector(log2(CAM_ROW_COUNT)-1 downto 0);
      DATA_IN           : in std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      WRITE_EN          : in std_logic;
      CLEAR             : in std_logic;
      CLEAR_ADDR        : in std_logic_vector(log2(CAM_ROW_COUNT)-1 downto 0);
      
      -- search interface
      MATCH_DATA        : in std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      MATCH_EN          : in std_logic;
      MATCH_BUS         : out std_logic_vector(CAM_ROW_COUNT-1 downto 0);
      MATCH_BUS_VLD     : out std_logic;
      MATCHED           : out std_logic
   );
end entity CAM_2PORT;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture light of CAM_2PORT is
   signal reg_data            : std_logic_vector(CAM_ROW_COUNT*CAM_ROW_WIDTH-1 
                                downto 0);
   signal reg_data_we         : std_logic_vector(CAM_ROW_COUNT-1 downto 0);
   signal reg_valid           : std_logic_vector(CAM_ROW_COUNT-1 downto 0);
   signal reg_valid_s         : std_logic_vector(CAM_ROW_COUNT-1 downto 0);
   signal reg_valid_c         : std_logic_vector(CAM_ROW_COUNT-1 downto 0);

   signal reg_match_bus       : std_logic_vector(CAM_ROW_COUNT-1 downto 0);
   signal reg_matched         : std_logic;
   signal reg_match_vld       : std_logic;
   signal cmp_matched         : std_logic_vector(CAM_ROW_COUNT-1 downto 0);
   signal sig_matched         : std_logic;

begin
   reg_valid_s    <= reg_data_we;

   -- mapping output ports
   MATCH_BUS      <= reg_match_bus;
   MATCH_BUS_VLD  <= reg_match_vld;
   MATCHED        <= reg_matched;

   -- decode address 
   DEC1FN_WRITE : entity work.cam_dec1fn
      generic map (
         ITEMS       => CAM_ROW_COUNT
      )
      port map (
         ADDR        => ADDR,
         ENABLE      => WRITE_EN,
         DO          => reg_data_we
      );

   -- decode address 
   DEC1FN_CLEAR : entity work.cam_dec1fn
      generic map (
         ITEMS       => CAM_ROW_COUNT
      )
      port map (
         ADDR        => CLEAR_ADDR,
         ENABLE      => CLEAR,
         DO          => reg_valid_c
      );
   
   GEN_REGS : for i in 0 to CAM_ROW_COUNT-1 generate
      -- register reg_data
      reg_datap: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (reg_data_we(i) = '1') then
               reg_data((i+1)*CAM_ROW_WIDTH-1 downto i*CAM_ROW_WIDTH) <= DATA_IN;
            end if;
         end if;
      end process;
   end generate;

   GEN_REG_DV : for i in 0 to CAM_ROW_COUNT-1 generate
      -- register reg_valid
      reg_validp: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (reg_valid_s(i) = '1') then
               reg_valid(i) <= '1';
            elsif (reg_valid_c(i) = '1') then
               reg_valid(i) <= '0';
            end if;
         end if;
      end process;
   end generate;

   GEN_CMPS : for i in 0 to CAM_ROW_COUNT-1 generate
      cmp_matched(i) <= '1' when 
                        ((reg_data((i+1)*CAM_ROW_WIDTH-1 downto i*CAM_ROW_WIDTH)
                        = MATCH_DATA) and (reg_valid(i) = '1'))
                        else  '0';
   end generate;

   -- register reg_match_bus
   reg_match_busp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_match_bus <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (MATCH_EN = '1') then
            reg_match_bus <= cmp_matched;
         end if;
      end if;
   end process;

   -- register reg_matched
   reg_matchedp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_matched <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (MATCH_EN = '1') then
            reg_matched <= sig_matched;
         end if;
      end if;
   end process;

   -- register reg_match_vld
   reg_match_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_match_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_match_vld <= MATCH_EN;
      end if;
   end process;

   -- sig_matched signal made from ORed cmp_matched bus
   sig_matchedp : process(cmp_matched)
      variable or_int : std_logic;
   begin
      or_int := '0';
      
      for k in 0 to CAM_ROW_COUNT-1 loop
         or_int := or_int or cmp_matched(k);
      end loop;

      sig_matched <= or_int;
   end process;


end architecture light;
