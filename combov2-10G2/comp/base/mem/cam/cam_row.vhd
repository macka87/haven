--
-- cam_row.vhd: One memory row of CAM.
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_row is
   generic(
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH  : integer
   );
   port(
      DATA_FILL      : in std_logic_vector(((CAM_ROW_WIDTH / 4)-1) downto 0);
      DATA_IN        : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_ENABLE   : in std_logic;
      MATCH_ENABLE   : in std_logic;
      MATCH_RST      : in std_logic;
      RESET          : in std_logic;
      CLK            : in std_logic;
      MATCH          : out std_logic
   );
end entity cam_row;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_row_arch of cam_row is

-- -------------------- cam_element Component Declaration ---------------------
   component cam_element is
      port(
         DATA_FILL      : in std_logic;
         DATA_IN        : in std_logic_vector(3 downto 0);
         WRITE_ENABLE   : in std_logic;
         MATCH_ENABLE   : in std_logic;
         RESET          : in std_logic; -- not used
         CLK            : in std_logic;
         MATCH          : out std_logic
      );
   end component cam_element;


-- ----------------- Constants declaration ------------------------------------
   -- Number of elements (cam_element)
   constant ELEM_COUNT  : integer := (CAM_ROW_WIDTH / 4);


-- ------------------ Signals declaration -------------------------------------
   signal reg_match_bus : std_logic_vector((ELEM_COUNT - 1) downto 0);
   signal reg_result : std_logic;
   signal match_result : std_logic;
   
begin
   match_result <= reg_match_bus(0) and not(MATCH_RST);
   MATCH <= reg_result;

-- --------- Generating and maping cam_elements -------------------------------
   DATA_ROW: for i in 0 to (ELEM_COUNT - 2) generate
   -- generate all row elements except the last one (it will be generated 
   -- later with special settings)
      ELEMENT_INST: cam_element
         port map (
            DATA_FILL      => DATA_FILL(i),
            DATA_IN        => DATA_IN( (((i + 1) * 4) - 1) downto (i * 4)),
            WRITE_ENABLE   => WRITE_ENABLE,
            MATCH_ENABLE   => reg_match_bus(i + 1),
            RESET          => RESET,
            CLK            => CLK,
            MATCH          => reg_match_bus(i)
         );
   end generate;

   -- generate the last element (it's connected to MATCH_ENABLE instead of
   -- reg_match_bus signal so it has to be generated separatedly)
      ELEMENT_LAST: cam_element
         port map (
            DATA_FILL      => DATA_FILL(ELEM_COUNT - 1),
            DATA_IN        => DATA_IN( ((ELEM_COUNT * 4) - 1)
                                     downto ((ELEM_COUNT - 1)*4)),
            WRITE_ENABLE   => WRITE_ENABLE,
            MATCH_ENABLE   => MATCH_ENABLE,
            RESET          => RESET,
            CLK            => CLK,
            MATCH          => reg_match_bus(ELEM_COUNT - 1)
         );
   
-- register reg_result ------------------------------------------------------
reg_resultp: process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_result <= '0';
   elsif (CLK'event AND CLK = '1') then
         reg_result <= match_result;
   end if;
end process;
   
end architecture cam_row_arch;
