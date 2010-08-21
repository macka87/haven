-- desc_manager_gcc.vhd: Top level descriptor manager for generic
-- channel count version of dma controllers.
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
-- 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity desc_manager_gcc is
   generic(
      -- local base address
      BASE_ADDR         : std_logic_vector(31 downto 0) := X"DEADBEEF";
      -- number of connected controlers (TX + RX)
      FLOWS             : integer := 8;
      -- number of descriptors. In scheme DOWNLOADED_BLOCK_SIZE. 
      -- Must be 2**N
      BLOCK_SIZE        : integer := 4;
      -- data width of DMA memory interface
      DMA_DATA_WIDTH    : integer := 64;
      -- Number of unused flows with odd number.
      -- Starts unconnect from higher numbers. So if FLOWS=32 and UNUSED_ODD=5
      -- then flows with number 31,29,27,25,23 will be unconnected
      UNUSED_ODD : integer := 0;
      -- Number of unused flows with even number.
      -- Starts unconnect from higher numbers. So if FLOWS=32 and UNUSED_EVEN=5
      -- then flows with number 30,28,26,24,22 will be unconnected
      UNUSED_EVEN: integer := 0

   );
   port(
      -- Common interface
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Memory interface
      -- Write interface
      WR_ADDR           : in std_logic_vector(31 downto 0);
      WR_DATA           : in std_logic_vector(63 downto 0);
      WR_BE             : in std_logic_vector(7 downto 0);
      WR_REQ            : in std_logic;
      WR_RDY            : out std_logic;

      -- DMA Interface --
      -- P1 interface
      DMA_ADDR          : in  std_logic_vector(log2(128/DMA_DATA_WIDTH)-1 downto 0);
      DMA_DOUT          : out std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
      DMA_REQ           : out std_logic;
      DMA_ACK           : in  std_logic;
      DMA_DONE          : in  std_logic;
      DMA_TAG           : in  std_logic_vector(15 downto 0);

      -- dma ctrls interface
      DESC_DATA         : out std_logic_vector(63 downto 0);
      DESC_DVLD         : out std_logic;
      DESC_ADDR         : in  std_logic_vector(abs(log2(FLOWS)-1) downto 0);
      DESC_READ         : in  std_logic;
      DESC_PIPE_EN      : in  std_logic;
      DESC_EMPTY        : out std_logic_vector(FLOWS-1 downto 0);

      -- Per channel enable interface
      ENABLE            : in std_logic_vector(FLOWS-1 downto 0) 
   );
end entity desc_manager_gcc;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of desc_manager_gcc is

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
   signal DF_DATA    : std_logic_vector(63 downto 0);
   signal DF_ADDR    : std_logic_vector(abs(log2(FLOWS)-1) downto 0);
   signal DF_WRITE   : std_logic;
   signal DF_FULL    : std_logic_vector(FLOWS-1 downto 0);
   signal DF_STATUS  : std_logic_vector(log2(2*BLOCK_SIZE+1)*FLOWS-1 downto 0);

   signal nEnable    : std_logic_vector(FLOWS-1 downto 0);

begin

   -- connect descriptor manager with BM
   DESC_MANAGER_BM_I : entity work.desc_manager_bm
      generic map(
         -- local base address
         BASE_ADDR         => BASE_ADDR,
         -- number of connected controlers (TX + RX)
         FLOWS             => FLOWS,
         -- number of descriptors. In scheme DOWNLOADED_BLOCK_SIZE. 
         BLOCK_SIZE        => BLOCK_SIZE
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
   DESCRIPTORS : entity work.nfifo
   generic map(
      DATA_WIDTH  => 64,
      FLOWS       => FLOWS,
      BLOCK_SIZE  => 2*BLOCK_SIZE,
      LUT_MEMORY  => false,
      OUTPUT_REG  => false,
      UNUSED_ODD  => UNUSED_ODD,
      UNUSED_EVEN => UNUSED_EVEN
   )
   port map(
      -- global signals
      CLK         => CLK,
      RESET       => RESET,
      INIT        => nEnable, -- clear not enabled channels

      -- write interface
      DATA_IN     => df_data,
      WR_BLK_ADDR => df_addr,
      WRITE       => df_write,
      FULL        => df_full,

      -- read interface
      DATA_OUT    => DESC_DATA,
      DATA_VLD    => DESC_DVLD,
      RD_BLK_ADDR => DESC_ADDR,
      READ        => DESC_READ,
      PIPE_EN     => DESC_PIPE_EN,
      EMPTY       => DESC_EMPTY,

      STATUS      => df_status
   );

   nEnable <= not ENABLE;
end architecture;
