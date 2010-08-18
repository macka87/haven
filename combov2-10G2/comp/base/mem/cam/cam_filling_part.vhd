--
-- cam_filling_part.vhd: An important part of CAM responsible for filling
--                       memory rows
-- Copyright (C) 2005 CESNET
-- Author(s): Martin kosek <xkosek00@stud.fit.vutbr.cz>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_filling_part is
   generic(
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer;
      -- Width of address bus 
      -- should be greater or equal to log2(CAM_ROW_COUNT)
      CAM_ADDR_WIDTH    : integer
   );
   port(
      ADDR              : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      MASK_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_ENABLE      : in std_logic;
      RESET             : in std_logic;
      CLK               : in std_logic;
      WRITE_ENABLE_BUS  : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
      DATA_FILL_BUS     : out std_logic_vector(((CAM_ROW_WIDTH / 4) - 1) downto 0)
   );
end entity cam_filling_part;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_filling_part_arch of cam_filling_part is

-- ------------------ cam_fill_element Component Declaration ------------------
component cam_fill_element is
   port(
      CNT_IN            : in std_logic_vector(3 downto 0);
      MASK_IN           : in std_logic_vector(3 downto 0);
      DATA_IN           : in std_logic_vector(3 downto 0);
      DATA_FILL         : out std_logic
   );
end component cam_fill_element;

-- ---------------------- cam_dec1fn Component Declaration --------------------
component cam_dec1fn is
   generic(
      ITEMS       : integer
   );
   port(
      ADDR        : in std_logic_vector(log2(ITEMS)-1 downto 0);
      ENABLE      : in std_logic;
      DO          : out std_logic_vector(ITEMS-1 downto 0)
   );
end component cam_dec1fn;

-- ----------------- Constants declaration ------------------------------------
   -- Number of filling elements (cam_fill_element)
   constant ELEM_COUNT  : integer := (CAM_ROW_WIDTH / 4);

-- ------------------ Signals declaration -------------------------------------
   signal fill_result      : std_logic_vector((ELEM_COUNT - 1) downto 0);
   signal dec1fn_we        : std_logic;
   signal counter_16       : std_logic_vector(3 downto 0);
   signal counter_16_ce    : std_logic;
   signal cnt_busy         : std_logic;
   signal dec1fn_out       : std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
   signal dec1fn_reduced   : std_logic_vector((log2(CAM_ROW_COUNT) - 1) downto 0);

begin
   DATA_FILL_BUS     <= fill_result;
   counter_16_ce     <= WRITE_ENABLE;
   WRITE_ENABLE_BUS  <= dec1fn_out;

-- --------- Generating and maping cam_elements -------------------------------
   FILL_ROW: for i in 0 to (ELEM_COUNT - 1) generate
   -- generate all filling elements
      ELEMENT_INST: cam_fill_element
         port map (
            CNT_IN         => counter_16,
            MASK_IN        => MASK_IN((((i + 1) * 4) - 1) downto (i * 4)),
            DATA_IN        => DATA_IN((((i + 1) * 4) - 1) downto (i * 4)),
            DATA_FILL      => fill_result(i)
         );
   end generate;


-- counter_16 counter ---------------------------------------------------------
   counter_16p: process(RESET, CLK)
   begin
      if (RESET = '1') then
         counter_16 <= (others => '1');
      elsif (CLK'event AND CLK = '1') then
         if (counter_16_ce = '1' AND cnt_busy /= '1') then
            counter_16 <= (others => '1');
            cnt_busy <= '1';
            dec1fn_we <= '1';
         elsif (cnt_busy = '1') then
            if (counter_16 = "0000") then
               cnt_busy <= '0';
               dec1fn_we <= '0';
            else
               counter_16 <= counter_16 - 1;
            end if;
         end if;
      end if;
   end process;

-- --------- Generating and maping generic decoder cam_dec1fn -----------------
   DEC1FN : cam_dec1fn
      generic map (
         ITEMS       => CAM_ROW_COUNT
      )
      port map (
         ADDR        => dec1fn_reduced,
         ENABLE      => dec1fn_we,
         DO          => dec1fn_out
      );

-- -------- Maping cam_dec1fn input (have to adjust ADDR) ---------------------
   MAP_DEC1FN_OUT: for i in 0 to (log2(CAM_ROW_COUNT) - 1) generate
      dec1fn_reduced(i) <= ADDR(i);
   end generate;

end architecture cam_filling_part_arch;
