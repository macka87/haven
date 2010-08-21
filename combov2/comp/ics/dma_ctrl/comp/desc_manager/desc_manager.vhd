-- desc_manager.vhd: Top level descriptor manager.
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
-- Documentation: 
-- https://www.liberouter.org/trac/netcope/wiki/desc_manager_doc
-- 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity desc_manager is
   generic(
      -- local base address on Internal Bus
      BASE_ADDR         : std_logic_vector(31 downto 0) := X"DEADBEEF";
      -- number of connected DMA controlers (TX + RX), may be 1 as well
      FLOWS             : integer := 8;
      -- number of downloaded descriptors must be 2**N. In scheme DOWNLOADED_BLOCK_SIZE. 
      BLOCK_SIZE        : integer := 4;
      -- data width of DMA memory interface
      DMA_DATA_WIDTH    : integer := 64;
      -- address gap between two init descriptors
      DESC_INIT_GAP     : integer := 8
   );
   port(
      -- Common interface
      CLK               : in std_logic;         -- System clock
      RESET             : in std_logic;         -- System reset

      -- Memory interface
      -- Write interface
      WR_ADDR           : in std_logic_vector(31 downto 0);    -- IB Write address for addressing individual channels
      WR_DATA           : in std_logic_vector(63 downto 0);    -- IB Write data - descriptors input
      WR_BE             : in std_logic_vector(7 downto 0);     -- Byte enable for only 32 bit memory access
      WR_REQ            : in std_logic;                        -- Request to write from IB
      WR_RDY            : out std_logic;                       -- Descriptor manager component ready, always in '1'

      -- DMA Interface --
      -- P1 interface
      DMA_ADDR          : in  std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);   -- Address of 'DMA request' part
      DMA_DOUT          : out std_logic_vector(DMA_DATA_WIDTH-1 downto 0);             -- 'DMA request' part, divided to some DMA_DATA_WIDTH bit parts
      DMA_REQ           : out std_logic;                                               -- Request for DMA transfer
      DMA_ACK           : in  std_logic;                                               -- Ack for last DMA request
      DMA_DONE          : in  std_logic;                                               -- DMA transfer finnished
      DMA_TAG           : in  std_logic_vector(15 downto 0);                           -- DMA transfer identifier

      -- DMA ctrls interface
      DATA_OUT          : out std_logic_vector(63 downto 0);               -- descriptors for individual DMA controlers
      EMPTY             : out std_logic_vector(FLOWS-1 downto 0);          -- not DATA_VLD; valid for addressed DMA channel, one hot
      READ              : in  std_logic_vector(FLOWS-1 downto 0);          -- read request from DMA controler, one hot

      -- Per channel enable interface
      ENABLE            : in std_logic_vector(FLOWS-1 downto 0)            -- allow to download descriptors for selected channel, one hot
   );
end entity desc_manager;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of desc_manager is

   signal bm_global_addr_i    : std_logic_vector(63 downto 0);  -- BM blobal address
   signal bm_local_addr_i     : std_logic_vector(31 downto 0);  -- BM local address
   signal bm_length_i         : std_logic_vector(11 downto 0);  -- BM data length = BLOCK_SIZE * 8
   signal bm_tag_i            : std_logic_vector(15 downto 0);  -- BM tag
   signal bm_trans_type_i     : std_logic_vector(3 downto 0);   -- BM transaction type
   signal bm_req_i            : std_logic;                      -- BM request
   signal bm_ack_i            : std_logic;                      -- BM ackowledging
   signal bm_op_tag_i         : std_logic_vector(15 downto 0); -- NOT USED!
   signal bm_op_done_i        : std_logic;                     -- NOT USED!  

   -- DESC fifo interface
   signal df_data    : std_logic_vector(63 downto 0);
   signal df_addr    : std_logic_vector(abs(log2(FLOWS)-1) downto 0);
   signal df_write   : std_logic;
   signal df_full    : std_logic_vector(FLOWS-1 downto 0);
   signal df_status  : std_logic_vector(log2(2*BLOCK_SIZE+1)*FLOWS-1 downto 0);

   signal data_vld   : std_logic_vector(FLOWS-1 downto 0);

begin

   -- connect descriptor manager with BM
   DESC_MANAGER_BM_I : entity work.desc_manager_bm
      generic map(
         -- local base address
         BASE_ADDR         => BASE_ADDR,
         -- number of connected controlers (TX + RX)
         FLOWS             => FLOWS,
         -- number of descriptors. In scheme DOWNLOADED_BLOCK_SIZE. 
         BLOCK_SIZE        => BLOCK_SIZE,
         -- address gap between two init descriptors
         DESC_INIT_GAP     => DESC_INIT_GAP
      )
      port map(
         -- Common interface
         CLK               => CLK,
         RESET             => RESET,

         -- Memory interface
         -- Write interface
         WR_ADDR        => WR_ADDR,
         WR_DATA        => WR_DATA,
         WR_BE          => WR_BE,
         WR_REQ         => WR_REQ,
         WR_RDY         => WR_RDY,

         -- BM Interface 
         BM_GLOBAL_ADDR => bm_global_addr_i, 
         BM_LOCAL_ADDR  => bm_local_addr_i, 
         BM_LENGTH      => bm_length_i, 
         BM_TAG         => bm_tag_i,
         BM_TRANS_TYPE  => bm_trans_type_i,  
         BM_REQ         => bm_req_i,                     
         BM_ACK         => bm_ack_i,                     
         BM_OP_TAG      => bm_op_tag_i,   -- NOT USED!
         BM_OP_DONE     => bm_op_done_i,  -- NOT USED!  

         -- DESC fifo interface
         DF_DATA           => df_data,
         DF_ADDR           => df_addr,
         DF_WRITE          => df_write,
         DF_FULL           => df_full,
         DF_STATUS         => df_status,

         -- Per channel enable interface
         ENABLE         => ENABLE 
      );
   
   -- output BM to memory
   MEM_2_BM_I : entity work.bm2mem
   generic map(
      DMA_DATA_WIDTH => DMA_DATA_WIDTH
   )
   port map(
      -- global signals
      CLK   => CLK,
      RESET => RESET,
      -- BM interface
      BM_GLOBAL_ADDR => bm_global_addr_i,   -- descriptor
      BM_LOCAL_ADDR  => bm_local_addr_i,    -- BASE_ADDR + chanel_addr + reg_array(11 downto 0) 
      BM_LENGTH      => bm_length_i,        -- BLOCK_SIZE * 8
      BM_TAG         => bm_tag_i,           -- 0x0000
      BM_TRANS_TYPE  => bm_trans_type_i,    -- 00 (from RAM to FPGA) RAM2FPGA
      BM_REQ         => bm_req_i,           -- req

      BM_ACK         => bm_ack_i,           -- ack
      BM_OP_TAG      => bm_op_tag_i,        -- not used  
      BM_OP_DONE     => bm_op_done_i,       -- not used

      -- Memory interface
      DMA_ADDR    => DMA_ADDR,
      DMA_DOUT    => DMA_DOUT,
      DMA_REQ     => DMA_REQ,
      DMA_ACK     => DMA_ACK,
      DMA_DONE    => DMA_DONE,
      DMA_TAG     => DMA_TAG
   );

   -- multififo for whole descriptors storing
   DESCRIPTORS : entity work.fifo2nfifo
      generic map(
         DATA_WIDTH  => 64,
         FLOWS       => FLOWS,
         BLOCK_SIZE  => 2*BLOCK_SIZE,
         LUT_MEMORY  => false,
         GLOB_STATE  => false
      )
      port map(
         -- global signals
         CLK   => CLK,
         RESET => RESET,

         -- write interface
         DATA_IN     => df_data,
         BLOCK_ADDR  => df_addr,
         WRITE       => df_write,
         FULL        => df_full,

         -- read interface
         DATA_OUT => DATA_OUT,
         DATA_VLD => data_vld,
         READ     => READ,
         EMPTY    => open,
         STATUS   => df_status
      );

    -- DMA EMPTY signal from manager
    GEN_FIFO_EMPTY_SIG: for i in 0 to FLOWS-1 generate
      EMPTY(i) <= not data_vld(i);
    end generate;

end architecture;
