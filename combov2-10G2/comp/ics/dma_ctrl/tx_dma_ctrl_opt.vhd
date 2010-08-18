-- tx_dma_ctrl_opt.vhd: Optimized TX DMA controller entity.
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- package with log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity tx_dma_ctrl_opt is
   generic(
      BUFFER_ADDR    : std_logic_vector(31 downto 0) := X"00000000";
      BUFFER_SIZE    : integer := 1024;
      DMA_DATA_WIDTH : integer := 16;
      DMA_TAG_ID     : std_logic_vector(7 downto 0)
   );
   port(
      -- Common interface
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      INTERRUPT   : out std_logic_vector(1 downto 0);
      ENABLE      : out std_logic;
      -- Transmit buffer interface
      BUF_NEWLEN     : out std_logic_vector(15 downto 0);
      BUF_NEWLEN_DV  : out std_logic;
      BUF_NEWLEN_RDY : in  std_logic;
      BUF_RELLEN     : in  std_logic_vector(15 downto 0);
      BUF_RELLEN_DV  : in  std_logic;
      -- Descriptor FIFO interface
      DESC_READ   : out std_logic;
      DESC_DO     : in  std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DESC_EMPTY  : in  std_logic;
      -- Memory interface
      SW_DWR      : in  std_logic_vector(31 downto 0);
      SW_ADDR     : in  std_logic_vector(5 downto 0);
      SW_RD       : in  std_logic;
      SW_WR       : in  std_logic;
      SW_BE       : in  std_logic_vector(3  downto 0);
      SW_DRD      : out std_logic_vector(31 downto 0);
      SW_ARDY     : out std_logic;
      SW_DRDY     : out std_logic;
      -- DMA Interface
      DMA_ADDR    : in  std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT    : out std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ     : out std_logic;
      DMA_ACK     : in  std_logic;
      DMA_DONE    : in  std_logic;
      DMA_TAG     : in  std_logic_vector(15 downto 0)
   );
end entity tx_dma_ctrl_opt;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of tx_dma_ctrl_opt is

   signal empty_sig        : std_logic_vector(3 downto 0);
   signal sig_sw_addr      : std_logic_vector(31 downto 0);
begin

   empty_sig <= SW_BE;

   sig_sw_addr(5 downto 0) <= SW_ADDR;
   sig_sw_addr(31 downto 6) <= (others => '0');

   SW_ARDY <= '1';

-- 1-bit wide DMA
TX_DMA_CTRL_OPT_1b: if DMA_DATA_WIDTH = 1 generate
   TX_DMA_CTRL_OPT_ARCH_I: entity work.tx_dma_ctrl_opt_arch_1b
      port map(
         -- Propagation of generic parameters
         BUFFER_ADDR    => BUFFER_ADDR,
         BUFFER_SIZE    => conv_std_logic_vector(BUFFER_SIZE, 16),
         DMA_TAG_ID     => DMA_TAG_ID,
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         INTERRUPT      => INTERRUPT,
         ENABLE         => ENABLE,
         -- Transmit buffer interface
         BUF_NEWLEN     => BUF_NEWLEN,
         BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
         BUF_NEWLEN_RDY => BUF_NEWLEN_RDY,
         BUF_RELLEN     => BUF_RELLEN,
         BUF_RELLEN_DV  => BUF_RELLEN_DV,
         -- Descriptor FIFO interface
         DESC_READ      => DESC_READ,
         DESC_DO        => DESC_DO,
         DESC_EMPTY     => DESC_EMPTY,
         -- Memory interface
         SW_DWR         => SW_DWR,
         SW_ADDR        => sig_sw_addr,
         SW_RD          => SW_RD,
         SW_WR          => SW_WR,
         SW_DRD         => SW_DRD,
         SW_ARDY        => open,
         SW_DRDY        => SW_DRDY,
         -- DMA Interface
         DMA_ADDR       => DMA_ADDR,
         DMA_DOUT       => DMA_DOUT,
         DMA_REQ        => DMA_REQ,
         DMA_ACK        => DMA_ACK,
         DMA_DONE       => DMA_DONE,
         DMA_TAG        => DMA_TAG
      );
end generate;

-- 2-bit wide DMA
TX_DMA_CTRL_OPT_2b: if DMA_DATA_WIDTH = 2 generate
   TX_DMA_CTRL_OPT_ARCH_I: entity work.tx_dma_ctrl_opt_arch_2b
      port map(
         -- Propagation of generic parameters
         BUFFER_ADDR    => BUFFER_ADDR,
         BUFFER_SIZE    => conv_std_logic_vector(BUFFER_SIZE, 16),
         DMA_TAG_ID     => DMA_TAG_ID,
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         INTERRUPT      => INTERRUPT,
         ENABLE         => ENABLE,
         -- Transmit buffer interface
         BUF_NEWLEN     => BUF_NEWLEN,
         BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
         BUF_NEWLEN_RDY => BUF_NEWLEN_RDY,
         BUF_RELLEN     => BUF_RELLEN,
         BUF_RELLEN_DV  => BUF_RELLEN_DV,
         -- Descriptor FIFO interface
         DESC_READ      => DESC_READ,
         DESC_DO        => DESC_DO,
         DESC_EMPTY     => DESC_EMPTY,
         -- Memory interface
         SW_DWR         => SW_DWR,
         SW_ADDR        => sig_sw_addr,
         SW_RD          => SW_RD,
         SW_WR          => SW_WR,
         SW_DRD         => SW_DRD,
         SW_ARDY        => open,
         SW_DRDY        => SW_DRDY,
         -- DMA Interface
         DMA_ADDR       => DMA_ADDR,
         DMA_DOUT       => DMA_DOUT,
         DMA_REQ        => DMA_REQ,
         DMA_ACK        => DMA_ACK,
         DMA_DONE       => DMA_DONE,
         DMA_TAG        => DMA_TAG
      );
end generate;

-- 4-bit wide DMA
TX_DMA_CTRL_OPT_4b: if DMA_DATA_WIDTH = 4 generate
   TX_DMA_CTRL_OPT_ARCH_I: entity work.tx_dma_ctrl_opt_arch_4b
      port map(
         -- Propagation of generic parameters
         BUFFER_ADDR    => BUFFER_ADDR,
         BUFFER_SIZE    => conv_std_logic_vector(BUFFER_SIZE, 16),
         DMA_TAG_ID     => DMA_TAG_ID,
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         INTERRUPT      => INTERRUPT,
         ENABLE         => ENABLE,
         -- Transmit buffer interface
         BUF_NEWLEN     => BUF_NEWLEN,
         BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
         BUF_NEWLEN_RDY => BUF_NEWLEN_RDY,
         BUF_RELLEN     => BUF_RELLEN,
         BUF_RELLEN_DV  => BUF_RELLEN_DV,
         -- Descriptor FIFO interface
         DESC_READ      => DESC_READ,
         DESC_DO        => DESC_DO,
         DESC_EMPTY     => DESC_EMPTY,
         -- Memory interface
         SW_DWR         => SW_DWR,
         SW_ADDR        => sig_sw_addr,
         SW_RD          => SW_RD,
         SW_WR          => SW_WR,
         SW_DRD         => SW_DRD,
         SW_ARDY        => open,
         SW_DRDY        => SW_DRDY,
         -- DMA Interface
         DMA_ADDR       => DMA_ADDR,
         DMA_DOUT       => DMA_DOUT,
         DMA_REQ        => DMA_REQ,
         DMA_ACK        => DMA_ACK,
         DMA_DONE       => DMA_DONE,
         DMA_TAG        => DMA_TAG
      );
end generate;

-- 8-bit wide DMA
TX_DMA_CTRL_OPT_8b: if DMA_DATA_WIDTH = 8 generate
   TX_DMA_CTRL_OPT_ARCH_I: entity work.tx_dma_ctrl_opt_arch_8b
      port map(
         -- Propagation of generic parameters
         BUFFER_ADDR    => BUFFER_ADDR,
         BUFFER_SIZE    => conv_std_logic_vector(BUFFER_SIZE, 16),
         DMA_TAG_ID     => DMA_TAG_ID,
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         INTERRUPT      => INTERRUPT,
         ENABLE         => ENABLE,
         -- Transmit buffer interface
         BUF_NEWLEN     => BUF_NEWLEN,
         BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
         BUF_NEWLEN_RDY => BUF_NEWLEN_RDY,
         BUF_RELLEN     => BUF_RELLEN,
         BUF_RELLEN_DV  => BUF_RELLEN_DV,
         -- Descriptor FIFO interface
         DESC_READ      => DESC_READ,
         DESC_DO        => DESC_DO,
         DESC_EMPTY     => DESC_EMPTY,
         -- Memory interface
         SW_DWR         => SW_DWR,
         SW_ADDR        => sig_sw_addr,
         SW_RD          => SW_RD,
         SW_WR          => SW_WR,
         SW_DRD         => SW_DRD,
         SW_ARDY        => open,
         SW_DRDY        => SW_DRDY,
         -- DMA Interface
         DMA_ADDR       => DMA_ADDR,
         DMA_DOUT       => DMA_DOUT,
         DMA_REQ        => DMA_REQ,
         DMA_ACK        => DMA_ACK,
         DMA_DONE       => DMA_DONE,
         DMA_TAG        => DMA_TAG
      );
end generate;

-- 16-bit wide DMA
TX_DMA_CTRL_OPT_16b: if DMA_DATA_WIDTH = 16 generate
   TX_DMA_CTRL_OPT_ARCH_I: entity work.tx_dma_ctrl_opt_arch_16b
      port map(
         -- Propagation of generic parameters
         BUFFER_ADDR    => BUFFER_ADDR,
         BUFFER_SIZE    => conv_std_logic_vector(BUFFER_SIZE, 16),
         DMA_TAG_ID     => DMA_TAG_ID,
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         INTERRUPT      => INTERRUPT,
         ENABLE         => ENABLE,
         -- Transmit buffer interface
         BUF_NEWLEN     => BUF_NEWLEN,
         BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
         BUF_NEWLEN_RDY => BUF_NEWLEN_RDY,
         BUF_RELLEN     => BUF_RELLEN,
         BUF_RELLEN_DV  => BUF_RELLEN_DV,
         -- Descriptor FIFO interface
         DESC_READ      => DESC_READ,
         DESC_DO        => DESC_DO,
         DESC_EMPTY     => DESC_EMPTY,
         -- Memory interface
         SW_DWR         => SW_DWR,
         SW_ADDR        => sig_sw_addr,
         SW_RD          => SW_RD,
         SW_WR          => SW_WR,
         SW_DRD         => SW_DRD,
         SW_ARDY        => open,
         SW_DRDY        => SW_DRDY,
         -- DMA Interface
         DMA_ADDR       => DMA_ADDR,
         DMA_DOUT       => DMA_DOUT,
         DMA_REQ        => DMA_REQ,
         DMA_ACK        => DMA_ACK,
         DMA_DONE       => DMA_DONE,
         DMA_TAG        => DMA_TAG
      );
end generate;

-- 32-bit wide DMA
TX_DMA_CTRL_OPT_32b: if DMA_DATA_WIDTH = 32 generate
   TX_DMA_CTRL_OPT_ARCH_I: entity work.tx_dma_ctrl_opt_arch_32b
      port map(
         -- Propagation of generic parameters
         BUFFER_ADDR    => BUFFER_ADDR,
         BUFFER_SIZE    => conv_std_logic_vector(BUFFER_SIZE, 16),
         DMA_TAG_ID     => DMA_TAG_ID,
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         INTERRUPT      => INTERRUPT,
         ENABLE         => ENABLE,
         -- Transmit buffer interface
         BUF_NEWLEN     => BUF_NEWLEN,
         BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
         BUF_NEWLEN_RDY => BUF_NEWLEN_RDY,
         BUF_RELLEN     => BUF_RELLEN,
         BUF_RELLEN_DV  => BUF_RELLEN_DV,
         -- Descriptor FIFO interface
         DESC_READ      => DESC_READ,
         DESC_DO        => DESC_DO,
         DESC_EMPTY     => DESC_EMPTY,
         -- Memory interface
         SW_DWR         => SW_DWR,
         SW_ADDR        => sig_sw_addr,
         SW_RD          => SW_RD,
         SW_WR          => SW_WR,
         SW_DRD         => SW_DRD,
         SW_ARDY        => open,
         SW_DRDY        => SW_DRDY,
         -- DMA Interface
         DMA_ADDR       => DMA_ADDR,
         DMA_DOUT       => DMA_DOUT,
         DMA_REQ        => DMA_REQ,
         DMA_ACK        => DMA_ACK,
         DMA_DONE       => DMA_DONE,
         DMA_TAG        => DMA_TAG
      );
end generate;

-- 64-bit wide DMA
TX_DMA_CTRL_OPT_64b: if DMA_DATA_WIDTH = 64 generate
   TX_DMA_CTRL_OPT_ARCH_I: entity work.tx_dma_ctrl_opt_arch_64b
      port map(
         -- Propagation of generic parameters
         BUFFER_ADDR    => BUFFER_ADDR,
         BUFFER_SIZE    => conv_std_logic_vector(BUFFER_SIZE, 16),
         DMA_TAG_ID     => DMA_TAG_ID,
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         INTERRUPT      => INTERRUPT,
         ENABLE         => ENABLE,
         -- Transmit buffer interface
         BUF_NEWLEN     => BUF_NEWLEN,
         BUF_NEWLEN_DV  => BUF_NEWLEN_DV,
         BUF_NEWLEN_RDY => BUF_NEWLEN_RDY,
         BUF_RELLEN     => BUF_RELLEN,
         BUF_RELLEN_DV  => BUF_RELLEN_DV,
         -- Descriptor FIFO interface
         DESC_READ      => DESC_READ,
         DESC_DO        => DESC_DO,
         DESC_EMPTY     => DESC_EMPTY,
         -- Memory interface
         SW_DWR         => SW_DWR,
         SW_ADDR        => sig_sw_addr,
         SW_RD          => SW_RD,
         SW_WR          => SW_WR,
         SW_DRD         => SW_DRD,
         SW_ARDY        => open,
         SW_DRDY        => SW_DRDY,
         -- DMA Interface
         DMA_ADDR       => DMA_ADDR,
         DMA_DOUT       => DMA_DOUT,
         DMA_REQ        => DMA_REQ,
         DMA_ACK        => DMA_ACK,
         DMA_DONE       => DMA_DONE,
         DMA_TAG        => DMA_TAG
      );
end generate;

end architecture full;
