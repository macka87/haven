-- rx_dma_ctrl_opt.vhd: Optimized RX DMA controller entity.
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--            Petr Kastovsky <kastovsky@liberouter.org>
--            Tomas Dedek    <dedek@liberouter.org>
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
entity rx_dma_ctrl_opt is
   generic(
      BUFFER_ADDR    : std_logic_vector(31 downto 0) := X"00000000";
      BUFFER_SIZE    : integer := 1024;
      DMA_DATA_WIDTH : integer := 16;
      DMA_TAG_ID     : std_logic_vector(7 downto 0) := "00000000"
   );
   port(
      -- Common interface
      CLK         : in  std_logic;
      RESET       : in  std_logic;
      INTERRUPT   : out std_logic;
      ENABLE      : out std_logic;
      -- Receive buffer interface
      BUF_NEWLEN       : in  std_logic_vector(15 downto 0);
      BUF_NEWLEN_DV    : in  std_logic;
      BUF_NEWLEN_RDY   : out std_logic;
      BUF_RELLEN       : out std_logic_vector(15 downto 0);
      BUF_RELLEN_DV    : out std_logic;
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
end entity rx_dma_ctrl_opt;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of rx_dma_ctrl_opt is
   constant DMA_REQ_WIDTH  : integer := 128;
   
   constant DMA_DATA_TAG   : std_logic_vector (7 downto 0)  := X"01";
   constant DMA_TAG_CONST  : std_logic_vector (7 downto 0)  := DMA_DATA_TAG or DMA_TAG_ID;
   constant TYPE_FPGA2RAM  : std_logic_vector (3 downto 0)  := X"1";
   
--   Format of the DMA REQUEST word
--   127              64       32 28 16   4 0
--   #----------------|--------|-|---|---|-#
--   global_addr
--                    local_addr
--                             reserved bits
--                               tag
--                                   lenght
--                                       trans_type
--
-- local_addr - constant for 31:13, 12:0 - 8Kb offset in page
-- tag        - constant for each controller
-- trans_type - constant   

-- DAM REQUEST memory inicialization:   
   constant DMA_REQ_MEM_INIT : std_logic_vector(127 downto 0) :=
               X"0000_0000_0000_0000" -- global address 
               & BUFFER_ADDR          -- local address
               & X"00"                -- reserved
               & DMA_TAG_CONST        -- tag
               & X"000"                -- lenght
               & TYPE_FPGA2RAM;       -- trans_type
	
   signal sig_sw_addr      : std_logic_vector(31 downto 0);

   signal reg_drd          : std_logic_vector(31 downto 0);
   signal reg_drdy         : std_logic;

   signal sig_drd          : std_logic_vector(31 downto 0);
   signal sig_drdy         : std_logic;

   -- memory interface
   signal mem_wea          : std_logic;
   signal mem_addra        : std_logic_vector(log2(DMA_REQ_WIDTH/DMA_DATA_WIDTH) - 1 downto 0);
   signal mem_dia          : std_logic_vector(DMA_DATA_WIDTH - 1 downto 0);
   signal mem_addrb        : std_logic_vector(log2(DMA_REQ_WIDTH/DMA_DATA_WIDTH) - 1 downto 0);
   signal mem_doa          : std_logic_vector(DMA_DATA_WIDTH - 1 downto 0);
   signal mem_dob          : std_logic_vector(DMA_DATA_WIDTH - 1 downto 0);


begin
   sig_sw_addr(5 downto 0) <= SW_ADDR;
   sig_sw_addr(31 downto 6) <= (others => '0');
   
   SW_ARDY  <= '1';
   SW_DRD   <= reg_drd;
   SW_DRDY  <= reg_drdy;

   -- MI splitter error hack
   reg_drdp: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         reg_drd <= sig_drd;
      end if;
   end process;

   reg_drdyp: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_drdy <= '0';
         else
            reg_drdy <= sig_drdy;
         end if;
      end if;
   end process;

   RX_DMA_CTRL_OPT_ARCH_I: entity work.rx_dma_ctrl_opt_arch
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
      SW_BE          => SW_BE,
      SW_DRD         => sig_drd,
      SW_ARDY        => open,
      SW_DRDY        => sig_drdy,
      -- DMA Interface
      DMA_ADDR       => DMA_ADDR,
      DMA_DOUT       => DMA_DOUT,
      DMA_REQ        => DMA_REQ,
      DMA_ACK        => DMA_ACK,
      DMA_DONE       => DMA_DONE,
      DMA_TAG        => DMA_TAG,
      -- Memory interface
      MEM_WEA        => mem_wea,
      MEM_ADDRA      => mem_addra,
      MEM_DIA        => mem_dia,
      MEM_DOA        => mem_doa,
      MEM_ADDRB      => mem_addrb,
      MEM_DOB        => mem_dob
      );

   RX_DMA_CTRL_OPT_MEM_I : entity work.dp_mem_lut
   generic map (
      ITEMS        => DMA_REQ_WIDTH / DMA_DATA_WIDTH,
      DATA_WIDTH   => DMA_DATA_WIDTH,
      DATA         => DMA_REQ_MEM_INIT
      )
   port map(
      CLK          => CLK,
      -- writting port
      WEA          => mem_wea,
      ADDRA        => mem_addra,
      DIA          => mem_dia,
      DOA          => mem_doa,

      -- reading port
      ADDRB        => mem_addrb,
      DOB          => mem_dob
      );
end Architecture full;
