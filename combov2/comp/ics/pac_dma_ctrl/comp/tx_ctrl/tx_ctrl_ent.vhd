-- tx_ctrl_ent.vhd: Packet TX DMA controller entity.
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- package with log2 function
use work.math_pack.all;
use work.pac_dma_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity tx_ctrl is
   generic(
      -- address of first tx buffer
      BUFFER_ADDR    : std_logic_vector(31 downto 0) := X"00000000";
      -- address gap between two tx buffers
      BUFFER_GAP     : std_logic_vector(31 downto 0) := X"00008000";
      -- size of tx buffer
      BUFFER_SIZE    : integer := 1024;
      -- tag for bus master operations
      DMA_ID         : std_logic_vector(1 downto 0) := "11";
      -- dma data width - output width of dma request
      DMA_DATA_WIDTH    : integer := 32;
      -- number of tx channels
      CHANNELS       : integer := 4;
      -- size of inner fifo
      BLOCK_SIZE     : integer := 4
   );
   port(
      -- Common interface
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      -- Control from desc. manager
      RUN         : in  std_logic_vector(CHANNELS-1 downto 0);
      IDLE        : out std_logic_vector(CHANNELS-1 downto 0);

      -- Receive buffer interface
      BUF_NEWLEN       : out std_logic_vector(CHANNELS*16-1 downto 0);
      BUF_NEWLEN_DV    : out std_logic_vector(CHANNELS-1 downto 0);
      BUF_NEWLEN_RDY   : in  std_logic_vector(CHANNELS-1 downto 0);
      BUF_RELLEN       : in  std_logic_vector(CHANNELS*16-1 downto 0);
      BUF_RELLEN_DV    : in  std_logic_vector(CHANNELS-1 downto 0);
      -- Descriptor FIFO interface
      DESC_READ   : out std_logic;
      DESC_ADDR   : out std_logic_vector(log2(CHANNELS)-1 downto 0);
      DESC_DO     : in  std_logic_vector(63 downto 0);
      DESC_DO_VLD : in  std_logic;
      DESC_EMPTY  : in  std_logic_vector(CHANNELS-1 downto 0);

      -- BM interface
      -- Memory interface
      DMA_ADDR        : in  std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT        : out std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ         : out std_logic;
      DMA_ACK         : in  std_logic;
      DMA_DONE        : in  std_logic;
      DMA_TAG         : in  std_logic_vector(15 downto 0);
 
      -- Status update
      SU_ADDR        : out std_logic_vector(abs(log2(CHANNELS)-1) downto 0);
      -- data width should change
      SU_DATA        : out std_logic_vector(NUM_FLAGS-1 downto 0);
      SU_DATA_VLD    : out std_logic;
      SU_HFULL       : in  std_logic_vector(CHANNELS-1 downto 0)
   );
end entity tx_ctrl;

