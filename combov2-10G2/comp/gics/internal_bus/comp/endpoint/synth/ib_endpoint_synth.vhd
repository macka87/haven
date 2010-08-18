-- ib_endpoint_synth.vhd: Internal Bus Endpoint Synth Wrapper
-- Copyright (C) 2010 CESNET
-- Author(s): Vaclav Bartos <washek@liberouter.org>
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
use work.ib_ifc_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity IB_ENDPOINT_SYNTH is
   generic(
      -- Data Width (8-128)
      DATA_WIDTH         : integer := 64;
      -- Address Width (1-32)
      ADDR_WIDTH         : integer := 32;
      -- Bus Master Enable
      BUS_MASTER_ENABLE  : boolean := false;
      -- Endpoint Address Space 
      ENDPOINT_BASE      : std_logic_vector(31 downto 0) := X"02300000";
      ENDPOINT_LIMIT     : std_logic_vector(31 downto 0) := X"01D00000";
      -- Endpoint is connected to
      CONNECTED_TO       : t_ib_comp := SWITCH_SLAVE;
      -- Strict Transaction Order
      STRICT_ORDER       : boolean := false;
      -- Data alignment (to dst. address)
      DATA_REORDER       : boolean := false;
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE          : t_ibrd_type := CONTINUAL;
      -- The number of reads in-process
      READ_IN_PROCESS    : integer :=  1;
      -- Buffers Sizes
      INPUT_BUFFER_SIZE  : integer := 1;
      OUTPUT_BUFFER_SIZE : integer := 1
   );
   port (
      -- Common interface -----------------------------------------------------
      CLK               : in std_logic;
      RESET             : in std_logic;

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

      -- Write Interface ------------------------------------------------------
      WR_REQ            : out std_logic;
      WR_RDY            : in  std_logic;
      WR_DATA           : out std_logic_vector(DATA_WIDTH-1 downto 0);
      WR_ADDR           : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      WR_BE             : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
      WR_LENGTH         : out std_logic_vector(11 downto 0);
      WR_SOF            : out std_logic;
      WR_EOF            : out std_logic;

      -- Read Interface -------------------------------------------------------
      RD_REQ            : out std_logic;
      RD_ARDY_ACCEPT    : in  std_logic;
      RD_ADDR           : out std_logic_vector(ADDR_WIDTH-1 downto 0);
      RD_BE             : out std_logic_vector(DATA_WIDTH/8-1 downto 0);
      RD_LENGTH         : out std_logic_vector(11 downto 0);
      RD_SOF            : out std_logic;
      RD_EOF            : out std_logic;

      RD_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_SRC_RDY        : in  std_logic;
      RD_DST_RDY        : out std_logic;

      -- Bus Master Interface -------------------------------------------------
      BM_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      BM_SOF_N          : in  std_logic;
      BM_EOF_N          : in  std_logic;
      BM_SRC_RDY_N      : in  std_logic;
      BM_DST_RDY_N      : out std_logic;

      BM_TAG            : out std_logic_vector(7 downto 0);
      BM_TAG_VLD        : out std_logic
   );
end entity IB_ENDPOINT_SYNTH;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of IB_ENDPOINT_SYNTH is

begin

   IB_ENDPOINT_I: entity work.IB_ENDPOINT
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
      STRICT_ORDER       => STRICT_ORDER,
      -- Data alignment (to dst. address)
      DATA_REORDER       => DATA_REORDER,
      -- Read type (CONTINUAL/PACKET)
      READ_TYPE          => READ_TYPE,
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
      WR_REQ             => WR_REQ,
      WR_RDY             => WR_RDY,
      WR_DATA            => WR_DATA,
      WR_ADDR            => WR_ADDR,
      WR_BE              => WR_BE,
      WR_LENGTH          => WR_LENGTH,
      WR_SOF             => WR_SOF,
      WR_EOF             => WR_EOF,
      
      -- Read Interface -------------------------------------------------------
      RD_REQ             => RD_REQ,
      RD_ARDY_ACCEPT     => RD_ARDY_ACCEPT,
      RD_ADDR            => RD_ADDR,
      RD_BE              => RD_BE,
      RD_LENGTH          => RD_LENGTH,
      RD_SOF             => RD_SOF,
      RD_EOF             => RD_EOF,
      
      RD_DATA            => RD_DATA,
      RD_SRC_RDY         => RD_SRC_RDY,
      RD_DST_RDY         => RD_DST_RDY,
      
      -- Bus Master Interface -------------------------------------------------
      BM_DATA            => BM_DATA,
      BM_SOF_N           => BM_SOF_N,
      BM_EOF_N           => BM_EOF_N,
      BM_SRC_RDY_N       => BM_SRC_RDY_N,
      BM_DST_RDY_N       => BM_DST_RDY_N,
      
      BM_TAG             => BM_TAG,
      BM_TAG_VLD         => BM_TAG_VLD
   );

end architecture full;
