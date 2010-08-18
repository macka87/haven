--
-- epi2mi_converter.vhd: Endpoint Interface to MI Converter
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
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
--                             ENTITY DECLARATION                            --
-- ----------------------------------------------------------------------------

entity EPI2MI_CONVERTER is
   generic(
      -- Data Width
      DATA_WIDTH        : integer := 64;
      -- Address Width
      ADDR_WIDTH        : integer := 32
   );   
   port(
      -- Common interface -----------------------------------------------------
      CLK               : in std_logic;
      RESET             : in std_logic;
      
      -- MI interface ---------------------------------------------------------
      MI_DWR            : out std_logic_vector(DATA_WIDTH-1 downto 0);
      MI_ADDR           : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      MI_RD             : out std_logic;
      MI_WR             : out std_logic;
      MI_ARDY           : in  std_logic;
      MI_BE             : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
      MI_DRD            : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      MI_DRDY           : in  std_logic;
      
      -- IB WR interface ------------------------------------------------------
      WR_REQ            : in  std_logic;
      WR_RDY            : out std_logic;
      WR_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      WR_ADDR           : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      WR_BE             : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      WR_LENGTH         : in  std_logic_vector(11 downto 0);
      WR_SOF            : in  std_logic;
      WR_EOF            : in  std_logic;
      
      -- IB RD interface ------------------------------------------------------
      RD_REQ            : in  std_logic;
      RD_ARDY_ACCEPT    : out std_logic;
      RD_ADDR           : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
      RD_BE             : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      RD_LENGTH         : in  std_logic_vector(11 downto 0);
      RD_SOF            : in  std_logic;
      RD_EOF            : in  std_logic;
      
      RD_DATA           : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_SRC_RDY        : out std_logic;
      RD_DST_RDY        : in  std_logic
   );
end entity EPI2MI_CONVERTER;

