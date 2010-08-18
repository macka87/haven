-- sum_ent.vhd: status update manager entity
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
-- $Id$
--
-- TODO:
-- KEYWORDS : TODO, DEBUG
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;
use work.pac_dma_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sum is
   generic (
      -- local base address
      BASE_ADDR         : std_logic_vector(31 downto 0) := X"DEADBEEF";
      -- number of connected controlers (TX + RX)
      -- it is assumed that there are same number of rt and tx channels
      IFCS              : integer := 4;
      -- max number of descriptors in one transfer
      -- size of transfer is BLOCK_SIZE*16
      BLOCK_SIZE        : integer := 4;
      -- tag to identify DMA component
      DMA_ID            : std_logic_vector(1 downto 0) := "01";
      -- dma data width - output width of dma request
      DMA_DATA_WIDTH    : integer := 32;
      -- use lut memory type in nfifo
      NFIFO_LUT_MEMORY  : boolean := false
   );
   port(
      -- Common signals
      CLK      : in std_logic;  
      RESET    : in std_logic;

      INTERRUPT : out std_logic_vector(2*IFCS-1 downto 0);
      IDLE      : out std_logic_vector(2*IFCS-1 downto 0);
      FLUSH     : in  std_logic_vector(2*IFCS-1 downto 0);
      INIT      : in  std_logic_vector(2*IFCS-1 downto 0);

      -- Data interface
      -- Read interface
      IB_RD_ADDR     : in  std_logic_vector(31 downto 0);
      IB_RD_DATA     : out std_logic_vector(63 downto 0);
      IB_RD_BE       : in  std_logic_vector(7 downto 0);
      IB_RD_REQ      : in  std_logic;
      IB_RD_ARDY     : out std_logic;
      IB_RD_SRC_RDY  : out std_logic;
                 
      -- BM interface
      -- Memory interface
      DMA_ADDR        : in  std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT        : out std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ         : out std_logic;
      DMA_ACK         : in  std_logic;
      DMA_DONE        : in  std_logic;
      DMA_TAG         : in  std_logic_vector(15 downto 0);

      -- SW memory interface
      MI_SW_DWR      : in  std_logic_vector(31 downto 0);
      MI_SW_ADDR     : in  std_logic_vector(31 downto 0);
      MI_SW_RD       : in  std_logic;
      MI_SW_WR       : in  std_logic;
      MI_SW_BE       : in  std_logic_vector(3  downto 0);
      MI_SW_DRD      : out std_logic_vector(31 downto 0);
      MI_SW_ARDY     : out std_logic;
      MI_SW_DRDY     : out std_logic;

      -- RxReqFifo interface
      RX_RF_RADDR   : out std_logic_vector(abs(log2(IFCS)-1) downto 0);
      RX_RF_DOUT    : in  std_logic_vector(log2(BLOCK_SIZE) + 64 downto 0);
      RX_RF_DVLD    : in  std_logic;
      RX_RF_EMPTY   : in  std_logic_vector(IFCS-1 downto 0);
      RX_RF_READ    : out std_logic;
      RX_RF_STATUS  : in  std_logic_vector(log2(BLOCK_SIZE+1)*IFCS-1 downto 0);

      -- Rx status update
      RX_SU_ADDR     : in  std_logic_vector(abs(log2(IFCS)-1) downto 0);
      RX_SU_DATA     : in  std_logic_vector(NUM_FLAGS+16-1 downto 0);
      RX_SU_DVLD     : in  std_logic;
      RX_SU_HFULL    : out std_logic_vector(IFCS-1 downto 0);

      -- Tx status update
      TX_SU_ADDR     : in  std_logic_vector(abs(log2(IFCS)-1) downto 0);
      TX_SU_DATA     : in  std_logic_vector(NUM_FLAGS-1 downto 0);
      TX_SU_DVLD     : in  std_logic;
      TX_SU_HFULL    : out std_logic_vector(IFCS-1 downto 0)
   );
end entity sum;
