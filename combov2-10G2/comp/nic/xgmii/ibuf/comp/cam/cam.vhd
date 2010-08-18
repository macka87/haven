--
-- cam.vhd: Top level of CAM component
-- Copyright (C) 2006-2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
entity IBUF_CAM is
   generic (
      -- Data row width (bits, should be a multiple of 4)
      CAM_ROW_WIDTH     : integer := 64;
      -- Number of data rows (depth of the CAM)
      CAM_ROW_COUNT     : integer := 16
   );
   port (
      -- common interface
      CLK               : in std_logic;
      RESET             : in std_logic;
      
      -- insert/read interface
      ADDR              : in std_logic_vector((log2(CAM_ROW_COUNT) - 1) downto 0);
      CAM_BUSY          : out std_logic;

      -- insert interface
      DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      WRITE_EN          : in std_logic;

      -- read interface
      READ_EN           : in std_logic;
      DATA_OUT          : out std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
      DATA_OUT_VLD      : out std_logic;
      
      -- search interface
      MATCH_EN          : in std_logic;
      MATCH_RST         : in std_logic;
      MATCH_BUS         : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
      MATCH_BUS_VLD     : out std_logic
   );
end entity IBUF_CAM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ibuf_cam_arch of IBUF_CAM is

-- ------------------ Signals declaration -------------------------------------
   signal reg_addr         : std_logic_vector((log2(CAM_ROW_COUNT) - 1) downto 0);
   signal reg_addr_we      : std_logic;
   signal reg_data_in      : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal reg_data_in_we   : std_logic;
   signal reg_match_en     : std_logic;
   signal reg_match_bus_vld : std_logic;

begin
   MATCH_BUS_VLD <= reg_match_bus_vld;

   reg_addr_we <= WRITE_EN or READ_EN;
   reg_data_in_we <= WRITE_EN or MATCH_EN;

-- -------- Generating and maping cam_data_array ------------------------------
   DATA_ARRAY: entity work.ibuf_cam_data_array
      generic map (
         CAM_ROW_WIDTH     => CAM_ROW_WIDTH,
         CAM_ROW_COUNT     => CAM_ROW_COUNT
      )
      port map (
         ADDR              => reg_addr,
         DATA_IN           => reg_data_in,
         WRITE_ENABLE      => WRITE_EN,
         MATCH_ENABLE      => reg_match_en,
         MATCH_RST         => MATCH_RST,
         READ_ENABLE       => READ_EN,
         RESET             => RESET,
         CLK               => CLK,
         MATCH_BUS         => MATCH_BUS,
         DATA_OUT          => DATA_OUT,
         DATA_OUT_VLD      => DATA_OUT_VLD,
         CAM_BUSY          => CAM_BUSY
      );


-- register reg_addr ----------------------------------------------------------
reg_addrp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (reg_addr_we = '1') then
         reg_addr <= ADDR;
      end if;
   end if;
end process;

-- register reg_data_in -------------------------------------------------------
reg_data_inp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      if (reg_data_in_we = '1') then
         reg_data_in <= DATA_IN;
      end if;
   end if;
end process;

-- register reg_match_enable --------------------------------------------------
reg_match_enablep: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
         reg_match_en <= MATCH_EN;
   end if;
end process;

-- register reg_match_vld -----------------------------------------------------
reg_match_vldp: process(CLK)
begin
   if (CLK'event AND CLK = '1') then
      reg_match_bus_vld <= reg_match_en;
   end if;
end process;


end architecture ibuf_cam_arch;
