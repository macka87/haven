--
-- cam_data_array.vhd: Array of memory elements + filling part
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
entity cam_data_array is
   generic (
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer;
      -- Width of address bus 
      -- should be greater or equal to log2(CAM_ROW_COUNT)
      CAM_ADDR_WIDTH    : integer
   );
   port (
      ADDR              : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      MASK_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_ENABLE      : in std_logic;
      MATCH_ENABLE      : in std_logic;
      MATCH_RST         : in std_logic;
      RESET             : in std_logic;
      CLK               : in std_logic;
      MATCH_BUS         : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0)
   );
end entity cam_data_array;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_data_array_arch of cam_data_array is

-- ----------------- cam_row Component Declaration ----------------------------
   component cam_row is
      generic(
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
   end component cam_row;

-- ----------------- cam_filling_part Component Declaration -------------------
   component cam_filling_part is
      generic(
         CAM_ROW_WIDTH     : integer;
         CAM_ROW_COUNT     : integer;
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
         DATA_FILL_BUS     : out std_logic_vector(((CAM_ROW_WIDTH / 4) - 1)
                                                                       downto 0)
      );
   end component cam_filling_part;

-- ------------------ Signals declaration -------------------------------------
   signal write_enable_bus : std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
   signal data_fill_bus : std_logic_vector(((CAM_ROW_WIDTH / 4) - 1) downto 0);
   signal match_out : std_logic_vector((CAM_ROW_COUNT - 1) downto 0);

begin
MATCH_BUS <= match_out;

-- -------- Generating and maping cam_filling_part ----------------------------
   FILLING_PART: cam_filling_part
      generic map (
         CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
         CAM_ROW_COUNT     => CAM_ROW_COUNT,
         CAM_ADDR_WIDTH    => CAM_ADDR_WIDTH
      )
      port map (
         ADDR              => ADDR,
         DATA_IN           => DATA_IN,
         MASK_IN           => MASK_IN,
         WRITE_ENABLE      => WRITE_ENABLE,
         RESET             => RESET,
         CLK               => CLK,
         WRITE_ENABLE_BUS  => write_enable_bus,
         DATA_FILL_BUS     => data_fill_bus
      );

-- -------- Generating and maping cam_rows ------------------------------------
   ROW_GEN: for i in 0 to (CAM_ROW_COUNT - 1) generate
   -- generate all memory rows
      ROW_INST: cam_row
         generic map (
            CAM_ROW_WIDTH  => CAM_ROW_WIDTH
         )
         port map (
            DATA_FILL      => data_fill_bus,
            DATA_IN        => DATA_IN,
            WRITE_ENABLE   => write_enable_bus(i),
            MATCH_ENABLE   => MATCH_ENABLE,
            MATCH_RST      => MATCH_RST,
            RESET          => RESET,
            CLK            => CLK,
            MATCH          => match_out(i)
         );
   end generate;

end architecture cam_data_array_arch;
