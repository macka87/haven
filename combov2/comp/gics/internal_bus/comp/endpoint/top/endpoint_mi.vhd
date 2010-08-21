--
-- endpoint_mi.vhd : IB Endpoint with converter to MI
-- Copyright (C) 2009 CESNET
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

use work.ib_ifc_pkg.all;
use work.ib_fmt_pkg.all;
use work.ib_endpoint_pkg.all;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION -- IB Endpoint with MI              --
-- ----------------------------------------------------------------------------

entity IB_ENDPOINT_MI is
   generic(
      -- Data Width (8-128)
      DATA_WIDTH         : integer := 64;
      -- Address Width (1-32)
      ADDR_WIDTH         : integer := 32;
      -- Bus Master Enable
      BUS_MASTER_ENABLE  : boolean := false;
      -- Endpoint Address Space 
      ENDPOINT_BASE      : std_logic_vector(31 downto 0) := X"11111111";
      ENDPOINT_LIMIT     : std_logic_vector(31 downto 0) := X"44444444";
      -- Endpoint is connected to
      CONNECTED_TO       : t_ib_comp := SWITCH_MASTER;
      -- Data alignment (to dst. address)
      DATA_REORDER       : boolean := false;
      -- The number of reads in-process
      READ_IN_PROCESS    : integer :=  1;
      -- Buffers Sizes
      INPUT_BUFFER_SIZE  : integer := 16;
      OUTPUT_BUFFER_SIZE : integer := 16
   ); 
   port (
      -- Common interface -----------------------------------------------------
      CLK                : in std_logic;
      RESET              : in std_logic;

      -- IB Interface ---------------------------------------------------------
      IB_DOWN_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in  std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;

      IB_UP_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;
      
      -- MI interface ---------------------------------------------------------
      MI_DWR            : out std_logic_vector(DATA_WIDTH-1 downto 0);
      MI_ADDR           : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      MI_RD             : out std_logic;
      MI_WR             : out std_logic;
      MI_ARDY           : in  std_logic;
      MI_BE             : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
      MI_DRD            : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      MI_DRDY           : in  std_logic;
      
      -- Bus Master Interface -------------------------------------------------
      BM_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      BM_SOF_N          : in  std_logic;
      BM_EOF_N          : in  std_logic;
      BM_SRC_RDY_N      : in  std_logic;
      BM_DST_RDY_N      : out std_logic;

      BM_TAG            : out std_logic_vector(7 downto 0);
      BM_TAG_VLD        : out std_logic
   ); 
end entity IB_ENDPOINT_MI;

-- ----------------------------------------------------------------------------
--              ARCHITECTURE DECLARATION -- IB Endpoint with MI              --
-- ----------------------------------------------------------------------------

architecture ib_endpoint_mi_arch of IB_ENDPOINT_MI is
  
  -- Write Interface ------------------------------------------------------
  signal wr_req          : std_logic;
  signal wr_rdy          : std_logic;
  signal wr_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal wr_addr         : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal wr_be           : std_logic_vector(DATA_WIDTH/8-1 downto 0);
  signal wr_length       : std_logic_vector(11 downto 0);
  signal wr_sof          : std_logic;
  signal wr_eof          : std_logic;

  -- Read Interface ------------------------------------------------------
  signal rd_req          : std_logic;
  signal rd_ardy_accept  : std_logic;
  signal rd_addr         : std_logic_vector(ADDR_WIDTH-1 downto 0);
  signal rd_be           : std_logic_vector(DATA_WIDTH/8-1 downto 0);
  signal rd_length       : std_logic_vector(11 downto 0);
  signal rd_sof          : std_logic;
  signal rd_eof          : std_logic;
  
  signal rd_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
  signal rd_src_rdy      : std_logic;
  signal rd_dst_rdy      : std_logic;
  
begin

   U_ib_endpoint: entity work.IB_ENDPOINT
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH         => DATA_WIDTH,
      -- Address Width (1-32)
      ADDR_WIDTH         => ADDR_WIDTH,
      -- Bus Master Enable
      BUS_MASTER_ENABLE  => BUS_MASTER_ENABLE,
      -- Endpoint Address Space 
      ENDPOINT_BASE      => ENDPOINT_BASE,
      ENDPOINT_LIMIT     => ENDPOINT_LIMIT,
      -- Endpoint is connected to
      CONNECTED_TO       => CONNECTED_TO,
      -- Strict Transaction Order
      STRICT_ORDER       => true,
      -- Data alignment (to dst. address)
      DATA_REORDER       => DATA_REORDER,
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE          => CONTINUAL,
      -- The number of reads in-process
      READ_IN_PROCESS    => READ_IN_PROCESS,
      -- Buffers Sizes
      INPUT_BUFFER_SIZE  => INPUT_BUFFER_SIZE,
      OUTPUT_BUFFER_SIZE => OUTPUT_BUFFER_SIZE
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK                => CLK,
      RESET              => RESET,

      -- IB Interface ---------------------------------------------------------
      IB_DOWN_DATA       => IB_DOWN_DATA,
      IB_DOWN_SOF_N      => IB_DOWN_SOF_N,
      IB_DOWN_EOF_N      => IB_DOWN_EOF_N,
      IB_DOWN_SRC_RDY_N  => IB_DOWN_SRC_RDY_N,
      IB_DOWN_DST_RDY_N  => IB_DOWN_DST_RDY_N,
      
      IB_UP_DATA         => IB_UP_DATA,
      IB_UP_SOF_N        => IB_UP_SOF_N,
      IB_UP_EOF_N        => IB_UP_EOF_N,
      IB_UP_SRC_RDY_N    => IB_UP_SRC_RDY_N,
      IB_UP_DST_RDY_N    => IB_UP_DST_RDY_N,
      
      -- Write Interface ------------------------------------------------------
      WR_REQ             => wr_req,
      WR_RDY             => wr_rdy,
      WR_DATA            => wr_data,
      WR_ADDR            => wr_addr,
      WR_BE              => wr_be,
      WR_LENGTH          => wr_length,
      WR_SOF             => wr_sof,
      WR_EOF             => wr_eof,
      
      -- Read Interface -------------------------------------------------------
      RD_REQ             => rd_req,
      RD_ARDY_ACCEPT     => rd_ardy_accept,
      RD_ADDR            => rd_addr,
      RD_BE              => rd_be,
      RD_LENGTH          => rd_length,
      RD_SOF             => rd_sof,
      RD_EOF             => rd_eof,
      
      RD_DATA            => rd_data,
      RD_SRC_RDY         => rd_src_rdy,
      RD_DST_RDY         => rd_dst_rdy,
      
      -- Bus Master Interface -------------------------------------------------
      BM_DATA            => BM_DATA,
      BM_SOF_N           => BM_SOF_N,
      BM_EOF_N           => BM_EOF_N,
      BM_SRC_RDY_N       => BM_SRC_RDY_N,
      BM_DST_RDY_N       => BM_DST_RDY_N,
      
      BM_TAG             => BM_TAG,
      BM_TAG_VLD         => BM_TAG_VLD
   );
   
   
   U_epi2mi: entity work.EPI2MI_CONVERTER
   generic map (
      -- Data Width (8-128)
      DATA_WIDTH         => DATA_WIDTH,
      -- Address Width (1-32)
      ADDR_WIDTH         => ADDR_WIDTH
   )
   port map (
      -- Common interface -----------------------------------------------------
      CLK               => CLK,
      RESET             => RESET,
      
      -- MI interface ---------------------------------------------------------
      MI_DWR            => MI_DWR,
      MI_ADDR           => MI_ADDR,
      MI_RD             => MI_RD,
      MI_WR             => MI_WR,
      MI_ARDY           => MI_ARDY,
      MI_BE             => MI_BE,
      MI_DRD            => MI_DRD,
      MI_DRDY           => MI_DRDY,
      
      -- IB WR interface ------------------------------------------------------
      WR_REQ            => wr_req,
      WR_RDY            => wr_rdy,
      WR_DATA           => wr_data,
      WR_ADDR           => wr_addr,
      WR_BE             => wr_be,
      WR_LENGTH         => wr_length,
      WR_SOF            => wr_sof,
      WR_EOF            => wr_eof,
      
      -- IB RD interface ------------------------------------------------------
      RD_REQ            => rd_req,
      RD_ARDY_ACCEPT    => rd_ardy_accept,
      RD_ADDR           => rd_addr,
      RD_BE             => rd_be,
      RD_LENGTH         => rd_length,
      RD_SOF            => rd_sof,
      RD_EOF            => rd_eof,
      
      RD_DATA           => rd_data,
      RD_SRC_RDY        => rd_src_rdy,
      RD_DST_RDY        => rd_dst_rdy
   );
   
end ib_endpoint_mi_arch;

