-- dma_ctrl_array_rx_opt.vhd: Array of optimalized DMA RX controllers 
--                            without descriptor manager
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
-- $Id$
--
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.all;
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity DMA_CTRL_ARRAY_RX_OPT is
   generic(
      -- number of network interfaces
      NET_IFC_COUNT     : integer := 2;
      -- DMA Controller generics
      BUFFER_ADDR       : std_logic_vector(31 downto 0) := X"00000000";
      BUFFER_SIZE       : integer := 1024;
      DMA_CTRL_INIT_GAP : integer := 16#40#
   );
   port(
      -- Common interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Interrupts
      RX_INTERRUPT   : out std_logic_vector(2*NET_IFC_COUNT-1 downto 0);
      
      -- Receive buffer interface
      RX_BUF_NEWLEN     : in  std_logic_vector(NET_IFC_COUNT*16-1 downto 0);
      RX_BUF_NEWLEN_DV  : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      RX_BUF_NEWLEN_RDY : out std_logic_vector(NET_IFC_COUNT-1 downto 0);  -- always set to '1'
      RX_BUF_RELLEN     : out std_logic_vector(NET_IFC_COUNT*16-1 downto 0);
      RX_BUF_RELLEN_DV  : out std_logic_vector(NET_IFC_COUNT-1 downto 0);

      -- LB memory interface
      SW_DWR         : in  std_logic_vector(31 downto 0);
      SW_ADDR        : in  std_logic_vector(31 downto 0);
      SW_RD          : in  std_logic;
      SW_WR          : in  std_logic;
      SW_BE          : in  std_logic_vector(3 downto 0);
      SW_DRD         : out std_logic_vector(31 downto 0);
      SW_ARDY        : out std_logic;
      SW_DRDY        : out std_logic;

      -- Busmaster interface
      BM_GLOBAL_ADDR : out std_logic_vector(63 downto 0);  
      BM_LOCAL_ADDR  : out std_logic_vector(31 downto 0);  
      BM_LENGTH      : out std_logic_vector(11 downto 0);  
      BM_TAG         : out std_logic_vector(15 downto 0);  
      BM_TRANS_TYPE  : out std_logic_vector(1 downto 0);   
      BM_REQ         : out std_logic;                      
      BM_ACK         : in  std_logic;                      
      BM_OP_TAG      : in  std_logic_vector(15 downto 0);   
      BM_OP_DONE     : in  std_logic;       

      -- Descriptor Manager Interface
      DESC_READ      : out std_logic_vector(NET_IFC_COUNT-1 downto 0);
      DESC_DO        : in  std_logic_vector(63 downto 0);
      DESC_EMPTY     : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      
      -- DMA Control Interface
      DESC_ENABLE    : out std_logic_vector(NET_IFC_COUNT-1 downto 0);

      -- Descriptor memory interface
      DESC_DMA_ADDR  : out std_logic_vector(log2(128/64)-1 downto 0);
      DESC_DMA_DOUT  : in  std_logic_vector(64-1 downto 0);
      DESC_DMA_REQ   : in  std_logic;
      DESC_DMA_ACK   : out std_logic;
      DESC_DMA_DONE  : out std_logic;
      DESC_DMA_TAG   : out std_logic_vector(15 downto 0)      
   );

end entity DMA_CTRL_ARRAY_RX_OPT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of DMA_CTRL_ARRAY_RX_OPT is
   -------------------------------------------------------------------
   --
   --  ICON core component declaration
   --
   -------------------------------------------------------------------
   component icon
     port
     (
       control0    : inout std_logic_vector(35 downto 0)
     );
   end component;

   -------------------------------------------------------------------
   --
   --  ILA core component declaration
   --
   -------------------------------------------------------------------
   component ila
     port
     (
       control     : inout std_logic_vector(35 downto 0);
       clk         : in    std_logic;
       data        : in    std_logic_vector(255 downto 0);
       trig0       : in    std_logic_vector(0 downto 0);
       trig1       : in    std_logic_vector(31 downto 0)
     );
   end component;

--    attribute noopt : boolean;
--    attribute noopt of icon : component is TRUE;
--    attribute noopt of ila : component is TRUE;


   -- Chipscope icon and ila signals
   signal ila_control : std_logic_vector(35 downto 0);
   signal ila_data    : std_logic_vector(255 downto 0);
   signal ila_trig0   : std_logic_vector(0 downto 0);
   signal ila_trig1   : std_logic_vector(31 downto 0);


   constant DMA_DATA_WIDTH    : integer := (64/(NET_IFC_COUNT));
   -- number of DMA interfaces (RX)
   constant DMA_COUNT      : integer := NET_IFC_COUNT;
   -- LB interface generics
   constant MI_ADDR_WIDTH  : integer := log2(DMA_CTRL_INIT_GAP); 
   constant DMA_CTRL_ADDR_WIDTH  : integer := 6; 
   constant DIFF_WIDTH     : integer := MI_ADDR_WIDTH - DMA_CTRL_ADDR_WIDTH;
   constant MI_DATA_WIDTH  : integer := 32;

   -- first multififo data out width
   constant FIFO_WIDTH     : integer := 64;

   -- MI_SPLITTER Output Interface
   signal mi_dwr     : std_logic_vector(DMA_COUNT*MI_DATA_WIDTH-1 downto 0);
   signal mi_addr    : std_logic_vector(DMA_COUNT*MI_ADDR_WIDTH-1 downto 0);
   signal mi_be      : std_logic_vector(DMA_COUNT*MI_DATA_WIDTH/8-1 downto 0);
   signal mi_rd      : std_logic_vector(DMA_COUNT-1 downto 0);
   signal mi_wr      : std_logic_vector(DMA_COUNT-1 downto 0);
   signal mi_ardy    : std_logic_vector(DMA_COUNT-1 downto 0);
   signal mi_drd     : std_logic_vector(DMA_COUNT*MI_DATA_WIDTH-1 downto 0);
   signal mi_drdy    : std_logic_vector(DMA_COUNT-1 downto 0);

   -- connect DMA Interface 
   signal dma_addr         : std_logic_vector(DMA_COUNT*log2(128/DMA_DATA_WIDTH)-1 downto 0);
   signal dma_dout         : std_logic_vector(DMA_COUNT*DMA_DATA_WIDTH-1 downto 0);
   signal dma_req          : std_logic_vector(DMA_COUNT-1 downto 0);
   signal dma_ack          : std_logic_vector(DMA_COUNT-1 downto 0);
   signal dma_done         : std_logic_vector(DMA_COUNT-1 downto 0);
   signal dma_tag          : std_logic_vector(DMA_COUNT*16-1 downto 0);

   -- Data inferface between DMA controllers and mfifo
   signal dma_tx_src_rdy_n : std_logic_vector(DMA_COUNT-1 downto 0);
   signal dma_tx_dst_rdy_n : std_logic_vector(DMA_COUNT-1 downto 0);
   signal dma_tx_src_rdy   : std_logic_vector(DMA_COUNT-1 downto 0);
   signal dma_tx_dst_rdy   : std_logic_vector(DMA_COUNT-1 downto 0);
   signal dma_tx_data      : std_logic_vector(DMA_COUNT*DMA_DATA_WIDTH-1 downto 0);

   signal data2bm_bm_global_addr : std_logic_vector(63 downto 0);
   signal data2bm_bm_req         : std_logic;
   signal data2bm_dma_done       : std_logic;
   signal data2bm_dma_tag        : std_logic_vector(15 downto 0);

   -- Output from dma2data connected to descriptor
   signal desc_tx_src_rdy_n   : std_logic;
   signal desc_tx_dst_rdy_n   : std_logic;
   signal desc_tx_data        : std_logic_vector(FIFO_WIDTH-1 downto 0);

   -- Multififo 1 data transmission logic
   signal cnt_block_addr_ce         : std_logic;
   signal mfifo1_word_transmission  : std_logic;
   signal cnt_mfifo1_words          : std_logic;
   signal cnt_mfifo1_words_ce       : std_logic;

   -- Multififo 1 output 
   signal mfifo1_data_out     : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal mfifo1_data_vld     : std_logic;
   signal mfifo1_block_addr   : std_logic_vector(abs(log2(DMA_COUNT)-1) downto 0) := (others => '0');
   signal mfifo1_read         : std_logic;
   signal mfifo1_empty        : std_logic_vector(DMA_COUNT-1 downto 0);

   signal mfifo2_write        : std_logic_vector(1 downto 0);  
   signal mfifo2_full         : std_logic_vector(1 downto 0);
   signal mfifo1_empty_part   : std_logic;

   -- Multififo 2 output 
   signal mfifo2_data_out     : std_logic_vector(2*FIFO_WIDTH-1 downto 0);
   signal mfifo2_data_vld     : std_logic;
   signal mfifo2_block_addr   : std_logic_vector(0 downto 0);
   signal mfifo2_block_addr_ce: std_logic;
   signal mfifo2_read         : std_logic;
   signal mfifo2_empty        : std_logic_vector(1 downto 0);
   
   signal data2bm_rx_src_rdy_n   : std_logic;
   signal data2bm_rx_dst_rdy_n   : std_logic;
   signal mfifo2_empty_part      : std_logic;
   signal mfifo2_data_in         : std_logic_vector(2*FIFO_WIDTH-1 downto 0); 

   -- Descriptor manager output interface
   signal rxdma_desc_read        : std_logic_vector(DMA_COUNT-1 downto 0);

begin

   one_flow: if DMA_COUNT = 1 generate
   
      mi_dwr   <= SW_DWR;
      mi_addr  <= SW_ADDR(MI_ADDR_WIDTH - 1 downto 0);
      mi_be    <= SW_BE;
      mi_rd(0) <= SW_RD;
      mi_wr(0) <= SW_WR;
      SW_ARDY  <= mi_ardy(0);
      SW_DRD   <= mi_drd;
      SW_DRDY  <= mi_drdy(0);
   
   end generate;

   more_flows: if DMA_COUNT > 1 generate

      -- mi_splitter
      MI_SPLITTER_I : entity work.mi_splitter
         generic map(
            ITEMS       => DMA_COUNT,
            ADDR_WIDTH  => MI_ADDR_WIDTH,
            DATA_WIDTH  => MI_DATA_WIDTH,
            PIPE        => false
         )
         port map(
            CLK      => CLK,
            RESET    => RESET,

            -- input interface
            IN_DWR   => SW_DWR,   
            IN_ADDR  => SW_ADDR(MI_ADDR_WIDTH+log2(DMA_COUNT)-1 downto 0),  
            IN_BE    => SW_BE,    
            IN_RD    => SW_RD,
            IN_WR    => SW_WR,
            IN_ARDY  => SW_ARDY,
            IN_DRD   => SW_DRD, 
            IN_DRDY  => SW_DRDY,

            -- output interface
            OUT_DWR  => mi_dwr, 
            OUT_ADDR => mi_addr,
            OUT_BE   => mi_be,  
            OUT_RD   => mi_rd,  
            OUT_WR   => mi_wr,  
            OUT_ARDY => mi_ardy,
            OUT_DRD  => mi_drd,
            OUT_DRDY => mi_drdy
         );

   end generate;

   -- generating DMA Controllers ----------------------------------------------
   GEN_DMA_CTRL : for i in 0 to NET_IFC_COUNT-1 generate
      rx_dma_ctrl_i : entity work.rx_dma_ctrl_opt
         generic map(
            BUFFER_ADDR       => BUFFER_ADDR + conv_std_logic_vector(i * 16#4000#, 32),
            BUFFER_SIZE       => BUFFER_SIZE,
            DMA_DATA_WIDTH    => DMA_DATA_WIDTH,
            DMA_TAG_ID        => conv_std_logic_vector(2*i, 8)
         )
         port map(
            CLK         => CLK,
            RESET       => RESET,
            INTERRUPT   => RX_INTERRUPT(2*(i+1) - 1 downto 2*i),
            ENABLE      => DESC_ENABLE(i),
   
            -- Receive buffer interface
            BUF_NEWLEN     => RX_BUF_NEWLEN((i+1)*16-1 downto i*16),
            BUF_NEWLEN_DV  => RX_BUF_NEWLEN_DV(i),
            BUF_NEWLEN_RDY => RX_BUF_NEWLEN_RDY(i),
            BUF_RELLEN     => RX_BUF_RELLEN((i+1)*16-1 downto i*16),
            BUF_RELLEN_DV  => RX_BUF_RELLEN_DV(i),
            
            -- Descriptor FIFO interface
            DESC_READ   => rxdma_desc_read(i),
            DESC_DO     => DESC_DO((i+1)*DMA_DATA_WIDTH-1 downto i*DMA_DATA_WIDTH),
            DESC_EMPTY  => DESC_EMPTY(i),

            -- Memory interface
            SW_DWR      => mi_dwr((i+1)*MI_DATA_WIDTH-1 downto i*MI_DATA_WIDTH),
            SW_ADDR     => mi_addr((i+1)*MI_ADDR_WIDTH-(1+DIFF_WIDTH) downto i*MI_ADDR_WIDTH),
            SW_RD       => mi_rd(i),
            SW_WR       => mi_wr(i),
            SW_BE       => mi_be((i+1)*MI_DATA_WIDTH/8-1 downto i*MI_DATA_WIDTH/8),
            SW_DRD      => mi_drd((i+1)*MI_DATA_WIDTH-1 downto i*MI_DATA_WIDTH),
            SW_ARDY     => mi_ardy(i),
            SW_DRDY     => mi_drdy(i),

            -- DMA Interface
            DMA_ADDR   => dma_addr((i+1)*log2(128/DMA_DATA_WIDTH)-1 downto i*log2(128/DMA_DATA_WIDTH)),
            DMA_DOUT   => dma_dout((i+1)*DMA_DATA_WIDTH-1 downto i*DMA_DATA_WIDTH),
            DMA_REQ    => dma_req(i),
            DMA_ACK    => dma_ack(i),
            DMA_DONE   => dma_done(i),
            DMA_TAG    => dma_tag((i+1)*16-1 downto i*16)
         );
      
      DESC_READ(i) <= rxdma_desc_read(i);
      
   end generate;

   -- generating DMA2DATA units -------------------------------------------------
   GEN_DMA2DATA : for i in 0 to DMA_COUNT-1 generate
      -- convert DMA Controller DMA interface to simple data
      DMA2DATA_I : entity work.DMA2DATA
         generic map(
            -- frame data width in bits
            DMA_DATA_WIDTH => DMA_DATA_WIDTH
--             DMA_COUNT      => DMA_COUNT
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,

            -- input interface
            DMA_ADDR       => dma_addr((i+1)*log2(128/DMA_DATA_WIDTH)-1 downto i*log2(128/DMA_DATA_WIDTH)),
            DMA_DOUT       => dma_dout((i+1)*DMA_DATA_WIDTH-1 downto i*DMA_DATA_WIDTH),
            DMA_REQ        => dma_req(i),
            DMA_ACK        => dma_ack(i),
            DMA_DONE       => dma_done(i),
            DMA_TAG        => dma_tag((i+1)*16-1 downto i*16),

            -- output interface
            TX_SRC_RDY_N   => dma_tx_src_rdy_n(i),
            TX_DST_RDY_N   => dma_tx_dst_rdy_n(i),
            TX_DATA        => dma_tx_data((i+1)*DMA_DATA_WIDTH-1 downto i*DMA_DATA_WIDTH),
            
            -- output tag interface
            TX_DMA_DONE    => data2bm_dma_done,
            TX_DMA_TAG     => data2bm_dma_tag
         );
   end generate;


   -- dma2data component for descriptor manager
   DMA2DATA_II : entity work.DMA2DATA
      generic map(
         -- frame data width in bits
         DMA_DATA_WIDTH => FIFO_WIDTH
--          DMA_COUNT      => DMA_COUNT
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         -- input interface
         DMA_ADDR       => DESC_DMA_ADDR,
         DMA_DOUT       => DESC_DMA_DOUT,
         DMA_REQ        => DESC_DMA_REQ,
         DMA_ACK        => DESC_DMA_ACK,
         DMA_DONE       => DESC_DMA_DONE,
         DMA_TAG        => DESC_DMA_TAG,

         -- output interface
         TX_SRC_RDY_N   => desc_tx_src_rdy_n,
         TX_DST_RDY_N   => desc_tx_dst_rdy_n,
         TX_DATA        => desc_tx_data,
            
         -- output tag interface
         TX_DMA_DONE    => data2bm_dma_done,
         TX_DMA_TAG     => data2bm_dma_tag
      );

      
   -- 3 situations possible:
   --  1. We are sending the first DMA word and the data from the current block
   --     is valid - read the word and wait for the next word (do not skip to
   --     the next block)
   --  2. We are sending the first DMA word (see cnt_mfifo1_words) and the data
   --     from the current block is not valid - skip to the next block
   --  3. We are sending the second DMA word - so must wait for it. In the word
   --     transfer cycle, proceed to the next block.
   --
   -- FIFO2NFIFO_I must be in LUT mode

   -- Word transmission from mfifo1 to mfifo2
   mfifo1_word_transmission <= mfifo1_data_vld and mfifo1_read;

   -- cnt_mfifo_block_addr counter
   cnt_block_addr_ce <= (mfifo1_word_transmission and cnt_mfifo1_words)
                          or
                        (not cnt_mfifo1_words and not mfifo1_data_vld);
   cnt_block_addr_i: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if(RESET = '1') then
            mfifo1_block_addr <= (others => '0');
         elsif (cnt_block_addr_ce = '1') then
            mfifo1_block_addr <= mfifo1_block_addr + 1;
         end if;
      end if;
   end process;

   -- cnt_mfifo1_words counter
   -- counter == 0 - sending the first (64b) DMA word
   -- counter == 1 - sending the second DMA word
   cnt_mfifo1_words_ce <= mfifo1_word_transmission;
   cnt_mfifo1_words_i: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if(RESET = '1') then
            cnt_mfifo1_words <= '0';
         elsif (cnt_mfifo1_words_ce = '1') then
            cnt_mfifo1_words <= not cnt_mfifo1_words;
         end if;
      end if;
   end process;

   
   dma_tx_src_rdy    <= not (dma_tx_src_rdy_n);  

   ONE_FLOW_FIFO: if DMA_COUNT = 1 generate 

      dma_tx_dst_rdy_n(0)  <= mfifo2_full(0);
      mfifo1_data_vld      <= dma_tx_src_rdy(0);
      mfifo1_data_out      <= dma_tx_data;

   end generate;

   MORE_FLOWS_FIFO: if DMA_COUNT > 1 generate 

      dma_tx_dst_rdy_n  <= (dma_tx_dst_rdy);  

      -- multififo for data from DMAs
      NFIFO2FIFO_I : entity work.NFIFO2FIFO
         generic map(
            DATA_WIDTH  => FIFO_WIDTH,
            FLOWS       => DMA_COUNT,
            BLOCK_SIZE  => 2,
            LUT_MEMORY  => true,
            GLOB_STATE  => false
         )
         port map(
            CLK      => CLK,
            RESET    => RESET,

            -- write interface
            DATA_IN     => dma_tx_data,
            WRITE       => dma_tx_src_rdy,
            FULL        => dma_tx_dst_rdy,

            -- read innterface
            DATA_OUT    => mfifo1_data_out,
            DATA_VLD    => mfifo1_data_vld,
            BLOCK_ADDR  => mfifo1_block_addr,
            READ        => mfifo1_read,
            PIPE_EN     => mfifo1_read,
            EMPTY       => mfifo1_empty
         );

   end generate;

   -- cnt_mfifo2_block_addr counter
   cnt_block_addr_ii: process(RESET, CLK)
   begin
         if (CLK'event AND CLK = '1') then
            if(RESET = '1') then
               mfifo2_block_addr <= (others => '0');
            else
               if mfifo2_block_addr_ce = '1' then
                  mfifo2_block_addr <= mfifo2_block_addr + 1;
               end if;
            end if;
         end if;
   end process;

   -- Step if current channel is being read, or if current channel is empty
   mfifo2_block_addr_ce <= mfifo2_data_vld or 
                           (((not mfifo2_block_addr(0)) and mfifo2_empty(0)) or
                            (mfifo2_block_addr(0) and mfifo2_empty(1)));

   -- connect write signals to fifo
   mfifo2_write      <= (not desc_tx_src_rdy_n) & (mfifo1_data_vld);
   -- descriptor manager side
   desc_tx_dst_rdy_n <= mfifo2_full(1);
   -- read to first DMA fifo
   mfifo1_read       <= not mfifo2_full(0);
   -- data to second fifo
   mfifo2_data_in    <= (desc_tx_data & mfifo1_data_out); 

   
   -- multififo for data from descriptor and DMAs
   NFIFO2FIFO_II : entity work.NFIFO2FIFO
      generic map(
         DATA_WIDTH  => 2*FIFO_WIDTH,
         FLOWS       => 2,
         BLOCK_SIZE  => 2,
         LUT_MEMORY  => true,
         GLOB_STATE  => false
      )
      port map(
         CLK      => CLK,
         RESET    => RESET,
         
         -- write interface
         DATA_IN     => mfifo2_data_in,
         WRITE       => mfifo2_write,
         FULL        => mfifo2_full,

         -- read innterface
         DATA_OUT    => mfifo2_data_out,
         DATA_VLD    => mfifo2_data_vld,
         BLOCK_ADDR  => mfifo2_block_addr,
         READ        => mfifo2_read,
         PIPE_EN     => mfifo2_read,
         EMPTY       => mfifo2_empty
      );


  
   data2bm_rx_src_rdy_n <= not (mfifo2_data_vld);
   -- fifo read signal
   mfifo2_read <= not data2bm_rx_dst_rdy_n;

   -- convert dma request in simple format to BM
   DATA2BM_I : entity work.DATA2BM
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         RX_SRC_RDY_N   => data2bm_rx_src_rdy_n,
         RX_DST_RDY_N   => data2bm_rx_dst_rdy_n,
         RX_DATA        => mfifo2_data_out,
         -- input TAG interface
         RX_DMA_TAG     => data2bm_dma_tag,
         RX_DMA_DONE    => data2bm_dma_done,
   
         -- Bus master interface
         BM_GLOBAL_ADDR => data2bm_bm_global_addr,
         BM_LOCAL_ADDR  => BM_LOCAL_ADDR,
         BM_LENGTH      => BM_LENGTH,
         BM_TAG         => BM_TAG,
         BM_TRANS_TYPE  => BM_TRANS_TYPE,
         BM_REQ         => data2bm_bm_req,
         BM_ACK         => BM_ACK,
         -- Output
         BM_OP_TAG      => BM_OP_TAG,
         BM_OP_DONE     => BM_OP_DONE
      );

  BM_GLOBAL_ADDR <= data2bm_bm_global_addr;
  BM_REQ         <= data2bm_bm_req;


  -------------------------------------------------------------------
  --  DEBUGGING - CHIPSCOPE stuff
  -------------------------------------------------------------------

--    i_icon : icon
--      port map
--      (
--        control0    => ila_control
--      );
-- 
--    i_ila : ila
--      port map
--      (
--        control   => ila_control,
--        clk       => CLK,
--        data      => ila_data,
--        trig0     => ila_trig0,
--        trig1     => ila_trig1
--      );
-- 
--    ila_trig0(0) <= data2bm_bm_req;
--    ila_trig1 <= data2bm_bm_global_addr(31 downto 0);
--    ila_data  <= 
--       X"000000" & "00" &
--       mfifo2_write & mfifo2_full & mfifo2_data_in(127 downto 64) &
--       mfifo1_empty & mfifo1_read & mfifo1_block_addr & mfifo1_data_vld & mfifo1_data_out &
--       dma_tx_dst_rdy(0) & dma_tx_src_rdy(0) & dma_tx_data(15 downto 0) &
--       dma_addr(1 downto 0) & dma_dout(15 downto 0) & dma_req(0) & dma_ack(0) & dma_done(0) &
--       DESC_EMPTY(0) & rxdma_desc_read(0) & DESC_DO(15 downto 0) &
--       ila_trig0 & ila_trig1;
    

end architecture;
-- ----------------------------------------------------------------------------
