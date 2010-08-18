--
-- cam_reading_part.vhd: Controls reading from CAM
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IBUF_CAM_READING_PART is
   generic(
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer
   );
   port(
      -- Common signals
      CLK               : in std_logic;
      RESET             : in std_logic;
      -- Bus that holds what data has been found
      DATA_NEXT_BUS     : in std_logic_vector(CAM_ROW_WIDTH/4-1 downto 0);
      -- Resets all read counters (new search), active in '1'
      READ_CNTS_RST     : in std_logic;
      -- Data outgoing from CAM
      DATA_OUT          : out std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
      -- Data that should be driven to SRL16E
      DATA_SRL          : out std_logic_vector(CAM_ROW_WIDTH-1 downto 0)
   );
end entity IBUF_CAM_READING_PART;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IBUF_CAM_READING_ARCH of IBUF_CAM_READING_PART is

   -- Signal declaration
   signal cnt_data_ld         : std_logic_vector(CAM_ROW_WIDTH/4-1 downto 0);
   signal cnt_data            : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal reg_reg_cnt_we_en   : std_logic_vector(CAM_ROW_WIDTH/4-1 downto 0);
   signal reg_reg_cnt_we_en_in: std_logic_vector(CAM_ROW_WIDTH/4-1 downto 0);
   signal reg_cnt             : std_logic_vector(CAM_ROW_WIDTH-1 downto 0);
   signal reg_cnt_we          : std_logic_vector(CAM_ROW_WIDTH/4-1 downto 0);

begin

   -- Generate counters and related stuff -------------------------------------
   CNT_GEN: for i in 0 to (CAM_ROW_WIDTH/4 - 1) generate

      -- cnt_data counter
      cnt_data_ld(i) <= READ_CNTS_RST;
      cnt_datap: process(RESET, CLK)
      begin
         if (RESET = '1') then
            cnt_data((i+1)*4-1 downto i*4) <= (others => '1');
         elsif (CLK'event AND CLK = '1') then
            if (cnt_data_ld(i) = '1') then
               cnt_data((i+1)*4-1 downto i*4) <= (others => '1');
            else
               cnt_data((i+1)*4-1 downto i*4) <=
                                        cnt_data((i+1)*4-1 downto i*4) - 1;
            end if;
         end if;
      end process;

      -- logic
      reg_reg_cnt_we_en_in(i) <= reg_cnt_we(i) or READ_CNTS_RST;
      reg_cnt_we(i) <= reg_reg_cnt_we_en(i) and DATA_NEXT_BUS(i);

      -- register reg_reg_cnt_we_en
      reg_reg_cnt_we_enp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_reg_cnt_we_en(i) <= '0';
         elsif (CLK'event AND CLK = '1') then
            reg_reg_cnt_we_en(i) <= reg_reg_cnt_we_en_in(i);
         end if;
      end process;

      -- register reg_cnt
      reg_cntp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_cnt((i+1)*4-1 downto i*4) <= (others => '0');
         elsif (CLK'event AND CLK = '1') then
            if (reg_cnt_we(i) = '1') then
               reg_cnt((i+1)*4-1 downto i*4) <= cnt_data((i+1)*4-1 downto i*4);
            end if;
         end if;
      end process;

   end generate;

   -- Output data -------------------------------------------------------------
   DATA_OUT <= reg_cnt;
   DATA_SRL <= cnt_data;

end architecture IBUF_CAM_READING_ARCH;
