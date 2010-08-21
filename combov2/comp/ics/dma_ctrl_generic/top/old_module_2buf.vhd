-- dma_module.vhd: DMA package with Generic DMA controller entity
-- Copyright (C) 2009 CESNET
-- Author(s): Martin Spinler <xspinl00@stud.fit.vutbr.cz>
--            Tomas Martinek <martinek@liberouter.org>
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
--merchantability and fitness for a particular purpose are disclaimed.
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
use work.ib_pkg.all;
use work.lb_pkg.all;
-- SW TX buffer definitions
use work.sw_txbuf_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity dma_module_2buf is
   generic(
      -- Number of network interfaces
      DMA_IFC_COUNT              : integer := 2;

      -- RX/TX Buffer generics
      DATA_WIDTH                 : integer := 64;
      BUFFER_ADDR                : std_logic_vector(31 DOWNTO 0) := X"02000000";
      BUFFER_SIZE                : integer := 4096;
      TX_SIZE_LENGTH             : integer := 16;
      RXTXBUF_IFC_TOTAL_SIZE     : integer := 16384;
      BLOCK_SIZE                 : integer := 512;
      
      -- Descriptor manager generics
      DESC_BASE_ADDR             : std_logic_vector(31 downto 0) :=  X"02200000";
      DESC_BLOCK_SIZE            : integer := 4;
      
      -- Internal Bus endpoint generics
      IB_EP_LIMIT                : std_logic_vector(31 downto 0) := X"01000000";
      IB_EP_INPUT_BUFFER_SIZE    : integer := 0;
      IB_EP_OUTPUT_BUFFER_SIZE   : integer := 0;
      IB_EP_READ_REORDER_BUFFER  : boolean := true;
      IB_EP_STRICT_EN            : boolean := false;

      -- Local Bus endpoint generics
      LB_EP_BASE_ADDR            : std_logic_vector(31 downto 0) := X"00000000";
      LB_EP_LIMIT                : std_logic_vector(31 downto 0) := X"00000800";
      LB_EP_FREQUENCY            : integer := 100;
      LB_EP_BUFFER_EN            : boolean := false
   );
   port(
      -- Common interface
      CLK                        : in  std_logic;
      RESET                      : in  std_logic;

      RX_INTERRUPT               : out std_logic;
      TX_INTERRUPT               : out std_logic;

      -- network interfaces interface
      -- input FrameLink interface
      RX_SOF_N                   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_SOP_N                   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_EOP_N                   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_EOF_N                   : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_SRC_RDY_N               : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_DST_RDY_N               : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      RX_DATA                    : in  std_logic_vector(DMA_IFC_COUNT*DATA_WIDTH-1 downto 0);
      RX_REM                     : in  std_logic_vector(DMA_IFC_COUNT*log2(DATA_WIDTH/8)-1 downto 0);
      -- output FrameLink interface
      TX_SOF_N                   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_SOP_N                   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_EOP_N                   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_EOF_N                   : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_SRC_RDY_N               : out std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_DST_RDY_N               : in  std_logic_vector(DMA_IFC_COUNT-1 downto 0);
      TX_DATA                    : out std_logic_vector(DMA_IFC_COUNT*DATA_WIDTH-1 downto 0);
      TX_REM                     : out std_logic_vector(DMA_IFC_COUNT*log2(DATA_WIDTH/8)-1 downto 0);
 
       -- Upstream InternalBus
      UP_DATA                    : out std_logic_vector(63 downto 0);
      UP_SOP_N                   : out std_logic;
      UP_EOP_N                   : out std_logic;
      UP_SRC_RDY_N               : out std_logic;
      UP_DST_RDY_N               : in  std_logic;
  
      -- Downstream InternalBus
      DOWN_DATA                  : in  std_logic_vector(63 downto 0);
      DOWN_SOP_N                 : in  std_logic;
      DOWN_EOP_N                 : in  std_logic;
      DOWN_SRC_RDY_N             : in  std_logic;
      DOWN_DST_RDY_N             : out std_logic;

      -- LocalBus
      LB_DWR                     : in std_logic_vector(15 downto 0);
      LB_BE                      : in std_logic_vector(1 downto 0);
      LB_ADS_N                   : in std_logic;
      LB_RD_N                    : in std_logic;
      LB_WR_N                    : in std_logic;
      LB_DRD                     : out std_logic_vector(15 downto 0);
      LB_RDY_N                   : out std_logic;
      LB_ERR_N                   : out std_logic;
      LB_ABORT_N                 : in std_logic
   );
end entity dma_module_2buf;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behaviour of dma_module_2buf is

   function minzero(n : integer) return integer is
   begin
      if(n > 0) then return n;
      else return 0;
      end if;
   end minzero;

   constant DMA_COUNT            : integer := 2*DMA_IFC_COUNT;

   ----------------------------------------------------------------------------
   --                            RX controller signals                         
   signal RX_BUF_NEWLEN          : std_logic_vector(15 DOWNTO 0);
   signal RX_BUF_NEWLEN_DV       : std_logic;
   signal RX_BUF_NEWLEN_IFC      : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal RX_BUF_NEWLEN_IFC2     : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0);

   signal RX_BUF_RELLEN          : std_logic_vector(15 DOWNTO 0);
   signal RX_BUF_RELLEN_DV       : std_logic;
   signal RX_BUF_RELLEN_IFC      : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal RX_BUF_RELLEN_IFC2     : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0);

   signal RX_DESC_EMPTY          : std_logic;
   signal RX_DESC_ADDR           : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal RX_DESC_ADDR2          : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0); 
   signal RX_DESC_READ           : std_logic;
   signal RX_DESC_DV             : std_logic;

   signal RX_DMA_ADDR            : std_logic_vector(log2(128/32)-1 DOWNTO 0);
   signal RX_DMA_DONE            : std_logic;
   signal RX_DMA_ACK             : std_logic;
   signal RX_DMA_DOUT            : std_logic_vector(31 DOWNTO 0);
   signal RX_DMA_REQ             : std_logic;

   signal RX_ENABLE              : std_logic_vector(DMA_IFC_COUNT-1 DOWNTO 0);
   signal RX_INTERRUPT_SIG       : std_logic_vector(1 DOWNTO 0);
   signal RX_INTERRUPT_IFC       : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal RX_INTERRUPT_IFC2      : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0);

   signal RX_SW_ARDY             : std_logic;
   signal RX_SW_DRD              : std_logic_vector(31 DOWNTO 0);
   signal RX_SW_DRDY             : std_logic;
   signal RX_SW_RD               : std_logic;
   signal RX_SW_WR               : std_logic;

   ----------------------------------------------------------------------------
   --                            TX controller signals                         
   signal TX_BUF_NEWLEN          : std_logic_vector(15 DOWNTO 0);
   signal TX_BUF_NEWLEN_DV       : std_logic;
   signal TX_BUF_NEWLEN_IFC      : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal TX_BUF_NEWLEN_IFC2     : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0);

   signal TX_BUF_RELLEN          : std_logic_vector(15 DOWNTO 0);
   signal TX_BUF_RELLEN_DV       : std_logic;
   signal TX_BUF_RELLEN_IFC      : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal TX_BUF_RELLEN_IFC2     : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0);

   signal TX_DESC_EMPTY          : std_logic;
   signal TX_DESC_ADDR           : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal TX_DESC_ADDR2          : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0); 
   signal TX_DESC_READ           : std_logic;
   signal TX_DESC_DV             : std_logic;

   signal TX_DMA_ADDR            : std_logic_vector(log2(128/32)-1 DOWNTO 0);
   signal TX_DMA_DONE            : std_logic;
   signal TX_DMA_ACK             : std_logic;
   signal TX_DMA_DOUT            : std_logic_vector(31 DOWNTO 0);
   signal TX_DMA_REQ             : std_logic;
 
   signal TX_ENABLE              : std_logic_vector(DMA_IFC_COUNT-1 DOWNTO 0);
   signal TX_INTERRUPT_SIG       : std_logic_vector(1 DOWNTO 0);
   signal TX_INTERRUPT_IFC       : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal TX_INTERRUPT_IFC2      : std_logic_vector(minzero(log2(DMA_IFC_COUNT)-1) DOWNTO 0);

   signal TX_SW_ARDY             : std_logic;
   signal TX_SW_DRD              : std_logic_vector(31 DOWNTO 0);
   signal TX_SW_DRDY             : std_logic;
   signal TX_SW_RD               : std_logic;
   signal TX_SW_WR               : std_logic;

   -----------------------------------------------------------------------------
   --                         Descriptor Manager signals                        
   signal DESC_DMA_ADDR          : std_logic_vector(0 DOWNTO 0);
   signal DESC_DMA_DONE          : std_logic;
   signal DESC_DMA_DOUT          : std_logic_vector(63 DOWNTO 0);
   signal DESC_DMA_ACK           : std_logic;
   signal DESC_DMA_TAG           : std_logic_vector(15 DOWNTO 0);
   signal DESC_DMA_REQ           : std_logic;

   signal DESC_DATA              : std_logic_vector(63 DOWNTO 0);
   signal DESC_READ              : std_logic;
   signal DESC_EMPTY             : std_logic_vector(2*DMA_IFC_COUNT-1 DOWNTO 0);
   signal DESC_DVLD              : std_logic;
   signal DESC_ADDR              : std_logic_vector(log2(2*DMA_IFC_COUNT)-1 DOWNTO 0);
   signal DESC_PIPE_EN           : std_logic;

   signal DESC_ENABLE            : std_logic_vector(2*DMA_IFC_COUNT-1 DOWNTO 0);

   -----------------------------------------------------------------------------
   --                           Receive buffer signals                          
   signal RXBUF_NEWLEN           : std_logic_vector(DMA_IFC_COUNT*16-1 downto 0);
   signal RXBUF_NEWLEN_DV        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RXBUF_NEWLEN_RDY       : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal RXBUF_RELLEN           : std_logic_vector(DMA_IFC_COUNT*16-1 downto 0);
   signal RXBUF_RELLEN_DV        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);

   -----------------------------------------------------------------------------
   --                           Transmit buffer signals                         
   signal TXBUF_NEWLEN           : std_logic_vector(DMA_IFC_COUNT*16-1 downto 0);
   signal TXBUF_NEWLEN_DV        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TXBUF_NEWLEN_RDY       : std_logic_vector(DMA_IFC_COUNT-1 downto 0);
   signal TXBUF_RELLEN           : std_logic_vector(DMA_IFC_COUNT*16-1 downto 0);
   signal TXBUF_RELLEN_DV        : std_logic_vector(DMA_IFC_COUNT-1 downto 0);

   -----------------------------------------------------------------------------
   --                           Status registers signal                         
   signal RX_INTERRUPT_SET       : std_logic_vector(63 downto 0);    -- TODO: What is this?
   signal TX_INTERRUPT_SET       : std_logic_vector(63 downto 0);

   -----------------------------------------------------------------------------
   --                         Local bus memory interface                        
   signal mi32_dwr               : std_logic_vector(31 downto 0);
   signal mi32_be                : std_logic_vector(3 downto 0);
   signal mi32_addr              : std_logic_vector(31 downto 0);
   signal mi32_drd               : std_logic_vector(31 downto 0);
   signal mi32_ardy              : std_logic;
   signal mi32_drdy              : std_logic;
   signal mi32_rd                : std_logic;
   signal mi32_wr                : std_logic;

   -----------------------------------------------------------------------------
   --                            Internal Bus signals                           
   -- read (input)
   signal ib_rd_addr             : std_logic_vector(31 downto 0);
   signal ib_rd_be               : std_logic_vector(7 downto 0);
   signal ib_rd_req              : std_logic;
   signal ib_rd_ardy             : std_logic;
   signal ib_rd_sof_in           : std_logic;
   signal ib_rd_eof_in           : std_logic;
   -- read (output)
   signal ib_rd_data             : std_logic_vector(63 downto 0);
   signal ib_rd_src_rdy          : std_logic;
   signal ib_rd_dst_rdy          : std_logic;
   -- write
   signal ib_wr_addr             : std_logic_vector(31 downto 0);
   signal ib_wr_data             : std_logic_vector(63 downto 0);
   signal ib_wr_be               : std_logic_vector(7 downto 0);
   signal ib_wr_req              : std_logic;
   signal ib_wr_rdy              : std_logic;
   signal ib_wr_length           : std_logic_vector(11 downto 0);
   signal ib_wr_sof              : std_logic;
   signal ib_wr_eof              : std_logic;
   -- busmaster interface (input)
   signal ib_bm_global_addr      : std_logic_vector(63 downto 0);
   signal ib_bm_local_addr       : std_logic_vector(31 downto 0);
   signal ib_bm_length           : std_logic_vector(11 downto 0);
   signal ib_bm_tag              : std_logic_vector(15 downto 0);
   signal ib_bm_trans_type       : std_logic_vector(1 downto 0);
   signal ib_bm_req              : std_logic;
   signal ib_bm_ack              : std_logic;
   -- busmaster interface (output)
   signal ib_bm_op_tag           : std_logic_vector(15 downto 0);
   signal ib_bm_op_done          : std_logic;

   signal bm_tag           : std_logic_vector(15 downto 0);   -- Operation TAG 
   signal bm_trans_type    : std_logic_vector(1 downto 0);    -- Transaction Type 
   signal bm_req           : std_logic; -- Request 
   signal bm_ack           : std_logic; -- Ack 
   -- outp 
   signal bm_op_tag        : std_logic_vector(15 downto 0);   -- Operation TAG 
   signal bm_op_done       : std_logic; -- Acknowledge 

   -----------------------------------------------------------------------------
   --                        Internal bus control signals                       
   -- read selectors
   signal ib_rxbuf_rd_sel        : std_logic;
   signal ib_rxbuf2_rd_sel       : std_logic;
   signal ib_txbuf_rd_sel        : std_logic;
   signal ib_txbuf2_rd_sel       : std_logic;
   signal ib_rxcontrol_rd_sel    : std_logic;
   signal ib_txcontrol_rd_sel    : std_logic;
   signal ib_desc_rd_sel         : std_logic;
   -- write selectors
   signal ib_rxbuf_wr_sel        : std_logic;
   signal ib_rxbuf2_wr_sel        : std_logic;
   signal ib_txbuf_wr_sel        : std_logic;
   signal ib_txbuf2_wr_sel        : std_logic;
   signal ib_rxcontrol_wr_sel    : std_logic;
   signal ib_txcontrol_wr_sel    : std_logic;
   signal ib_desc_wr_sel         : std_logic;
   -- read request
   signal ib_rxbuf_rd_req        : std_logic;
   signal ib_rxbuf2_rd_req        : std_logic;
   signal ib_txbuf_rd_req        : std_logic;
   signal ib_txbuf2_rd_req        : std_logic;
   signal ib_rxcontrol_rd_req    : std_logic;
   signal ib_txcontrol_rd_req    : std_logic;
   signal ib_desc_rd_req         : std_logic;
   -- read data
   signal ib_rxbuf_rd_data       : std_logic_vector(63 downto 0);
   signal ib_rxbuf2_rd_data       : std_logic_vector(63 downto 0);
   signal ib_txbuf_rd_data       : std_logic_vector(63 downto 0);
   signal ib_txbuf2_rd_data       : std_logic_vector(63 downto 0);
   signal ib_rxcontrol_rd_data   : std_logic_vector(63 downto 0);
   signal ib_txcontrol_rd_data   : std_logic_vector(63 downto 0);
   signal ib_desc_rd_data        : std_logic_vector(63 downto 0);
   -- read ardy
   signal ib_rxbuf_rd_ardy       : std_logic;
   signal ib_rxbuf2_rd_ardy       : std_logic;
   signal ib_txbuf_rd_ardy       : std_logic;
   signal ib_txbuf2_rd_ardy       : std_logic;
   signal ib_rxcontrol_rd_ardy   : std_logic;
   signal ib_txcontrol_rd_ardy   : std_logic;
   signal ib_desc_rd_ardy        : std_logic;
   -- read src_rdy
   signal ib_rxbuf_rd_src_rdy    : std_logic;
   signal ib_rxbuf2_rd_src_rdy    : std_logic;
   signal ib_txbuf_rd_src_rdy    : std_logic;
   signal ib_txbuf2_rd_src_rdy    : std_logic;
   signal ib_rxcontrol_rd_src_rdy: std_logic;
   signal ib_txcontrol_rd_src_rdy: std_logic;
   signal ib_desc_rd_src_rdy     : std_logic;
   -- write ready
   signal ib_rxbuf_wr_rdy        : std_logic;
   signal ib_rxbuf2_wr_rdy        : std_logic;
   signal ib_txbuf_wr_rdy        : std_logic;
   signal ib_txbuf2_wr_rdy        : std_logic;
   signal ib_dma_wr_rdy          : std_logic;
   signal ib_desc_wr_rdy         : std_logic;
   -- write request
   signal ib_rxbuf_wr_req        : std_logic;
   signal ib_rxbuf2_wr_req        : std_logic;
   signal ib_txbuf_wr_req        : std_logic;
   signal ib_txbuf2_wr_req        : std_logic;
   signal ib_rxcontrol_wr_req    : std_logic;
   signal ib_txcontrol_wr_req    : std_logic;
   signal ib_desc_wr_req         : std_logic;
   -- addresses for buffers
   signal ib_wr_addr_buf         : std_logic_vector(31 downto 0);
   signal ib_rd_addr_buf         : std_logic_vector(31 downto 0);
   signal ib_rd_ardy_buf         : std_logic;
   -- registers
   signal reg_rd_addr            : std_logic_vector(31 downto 0);
   signal reg_rd_addr_we         : std_logic;
   signal reg_ib_rd_req          : std_logic;
   signal reg_ib_rd_req_we       : std_logic;
   signal reg_ib_rxc_rd_src_rdy  : std_logic;
   signal reg_ib_rxc_rd_src_rdy_we : std_logic;
   signal reg_ib_txc_rd_src_rdy  : std_logic;
   signal reg_ib_txc_rd_src_rdy_we : std_logic;
   -- interrupt registers mx output - registered
   signal mx_dma_stat            : std_logic_vector(63 downto 0);
   signal reg_dma_stat           : std_logic_vector(63 downto 0);
   signal mfifo2_block_addr_ce   : std_logic;

   -----------------------------------------------------------------------------
   --              Data interface between DMA controllers and mfifo             
   signal dma_tx_src_rdy_n       : std_logic_vector(1 downto 0);
   signal dma_tx_dst_rdy_n       : std_logic_vector(1 downto 0);
   signal dma_tx_src_rdy         : std_logic_vector(1 downto 0);
   signal dma_tx_dst_rdy         : std_logic_vector(1 downto 0);
   signal dma_tx_data            : std_logic_vector(2*32-1 downto 0);
   -- Data2BM signals
   signal data2bm_dma_done       : std_logic;
   signal data2bm_dma_tag        : std_logic_vector(15 downto 0);
   signal data2bm_rx_src_rdy_n   : std_logic;
   signal data2bm_rx_dst_rdy_n   : std_logic;
   -- Output from dma2data connected to descriptor
   signal desc_tx_src_rdy_n      : std_logic;
   signal desc_tx_dst_rdy_n      : std_logic;
   signal desc_tx_data           : std_logic_vector(63 downto 0);
   -- Multififo 1 data transmission logic
   signal cnt_block_addr_ce      : std_logic;
   signal cnt_mfifo1_words       : std_logic;
   signal cnt_mfifo1_words_ce    : std_logic;
   signal mfifo1_word_transmission : std_logic;
   -- Multififo 1 output 
   signal mfifo1_data_out        : std_logic_vector(63 downto 0);
   signal mfifo1_data_vld        : std_logic;
   signal mfifo1_block_addr      : std_logic_vector(0 downto 0) := (others => '0');
   signal mfifo1_read            : std_logic;
   signal mfifo1_empty           : std_logic_vector(1 downto 0);
   signal mfifo2_write           : std_logic_vector(1 downto 0);
   signal mfifo2_full            : std_logic_vector(1 downto 0);
   signal mfifo1_empty_part      : std_logic;
   -- Multififo 2 output 
   signal mfifo2_data_out        : std_logic_vector(2*64-1 downto 0);
   signal mfifo2_data_vld        : std_logic;
   signal mfifo2_block_addr      : std_logic_vector(0 downto 0);
   signal mfifo2_read            : std_logic;
   signal mfifo2_empty           : std_logic_vector(1 downto 0);
   signal mfifo2_empty_part      : std_logic;
   signal mfifo2_data_in         : std_logic_vector(127 downto 0);

   -----------------------------------------------------------------------------
   --                 Aggregators between controllers and buffers               
   signal rxbuf_newlen_reg       : std_logic_vector(DMA_IFC_COUNT*16-1 downto 0);
   signal rx_newlen_ifc          : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal newlen_reg             : std_logic_vector(DMA_IFC_COUNT*16 - 1 downto 0);
   signal newlen_wr              : std_logic_vector(DMA_IFC_COUNT*16 - 1 downto 0);
   signal newlen_read            : std_logic_vector(DMA_IFC_COUNT - 1 downto 0);

   signal txbuf_rellen_reg       : std_logic_vector(DMA_IFC_COUNT*16-1 downto 0);
   signal tx_rellen_ifc          : std_logic_vector(log2(DMA_IFC_COUNT)-1 DOWNTO 0);
   signal rellen_reg             : std_logic_vector(DMA_IFC_COUNT*16 - 1 downto 0);
   signal rellen_wr              : std_logic_vector(DMA_IFC_COUNT*16 - 1 downto 0);
   signal rellen_read            : std_logic_vector(DMA_IFC_COUNT - 1 downto 0);

   -----------------------------------------------------------------------------
   --                         Descriptor manager sharing                        
   signal rx_tx_desc             : std_logic_vector(0 downto 0);
   signal rs_desc_read           : std_logic_vector(1 downto 0);
   signal rs_desc_read_set       : std_logic_vector(1 downto 0);
   signal rs_desc_read_reset     : std_logic_vector(1 downto 0);

   -----------------------------------------------------------------------------
   --                          Generic decoder function                         
   function decode(v : std_logic_vector) return std_logic_vector is
      variable res : std_logic_vector((2**v'length)-1 downto 0);
      variable i : integer;
   begin
      if v'length = -1 then
        return "1";
      else
         res := (others => '0'); i := 0;
         i := conv_integer(unsigned(v));
         res(i) := '1';
         return(res);
      end if;
   end;

   -----------------------------------------------------------------------------
   --                        Generic multiplexor function                       
   function genmux(s,v : std_logic_vector) return std_logic is
      variable res : std_logic_vector(v'length-1 downto 0);
      variable i : integer;
   begin
     res := v; i := 0;
     i := conv_integer(unsigned(s));
     return(res(i));
   end;

begin

   gen: if DMA_IFC_COUNT > 1 generate
      RX_BUF_NEWLEN_IFC2 <= RX_BUF_NEWLEN_IFC;
      TX_BUF_RELLEN_IFC2 <= TX_BUF_RELLEN_IFC;
      
      RX_BUF_RELLEN_IFC <= RX_BUF_RELLEN_IFC2;
      TX_BUF_NEWLEN_IFC <= TX_BUF_NEWLEN_IFC2;
      
      RX_INTERRUPT_IFC  <= RX_INTERRUPT_IFC2; 
      TX_INTERRUPT_IFC  <= TX_INTERRUPT_IFC2; 

      RX_DESC_ADDR      <= RX_DESC_ADDR2;
      TX_DESC_ADDR      <= TX_DESC_ADDR2;
   end generate;
   
   gen2: if DMA_IFC_COUNT = 1 generate
      RX_BUF_NEWLEN_IFC2 <= "0";
      TX_BUF_RELLEN_IFC2 <= "0";
   end generate;
  
   -----------------------------------------------------------------------------
   --                         RX DMA Controller instance                        
   RX_DMA_CTRL_I: entity work.rx_dma_ctrl_arch
      port map(
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         
   --      BUFFER_ADDR    => BUFFER_ADDR,

         BUF_NEWLEN     => RX_BUF_NEWLEN,
         BUF_NEWLEN_DV  => RX_BUF_NEWLEN_DV,
         BUF_NEWLEN_IFC => RX_BUF_NEWLEN_IFC2,

         BUF_RELLEN     => RX_BUF_RELLEN,
         BUF_RELLEN_IFC => RX_BUF_RELLEN_IFC2,
         BUF_RELLEN_DV  => RX_BUF_RELLEN_DV,

         DESC_DATA      => DESC_DATA,
         DESC_EMPTY     => RX_DESC_EMPTY,
         DESC_IFC       => RX_DESC_ADDR2,
         DESC_READ      => RX_DESC_READ,
         DESC_DV        => RX_DESC_DV,

         DMA_ADDR       => RX_DMA_ADDR,
         DMA_DOUT       => RX_DMA_DOUT,
         DMA_REQ        => RX_DMA_REQ,
         DMA_ACK        => RX_DMA_ACK,
         DMA_DONE       => RX_DMA_DONE,

         ENABLE         => RX_ENABLE,
         INTERRUPT      => RX_INTERRUPT_SIG,
         INTERRUPT_IFC  => RX_INTERRUPT_IFC2,

         SW_ADDR        => mi32_ADDR,
         SW_ARDY        => RX_SW_ARDY,
         SW_BE          => mi32_be,
         SW_DRD         => RX_SW_DRD,
         SW_DRDY        => RX_SW_DRDY,
         SW_DWR         => mi32_dwr,
         SW_RD          => RX_SW_RD,
         SW_WR          => RX_SW_WR
      );


   -----------------------------------------------------------------------------
   --                         TX DMA Controller instance                        
   TX_DMA_CTRL_I: entity work.tx_dma_ctrl_arch
      port map(
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         
--         BUFFER_ADDR    => BUFFER_ADDR,

         BUF_NEWLEN     => TX_BUF_NEWLEN,
         BUF_NEWLEN_DV  => TX_BUF_NEWLEN_DV,
         BUF_NEWLEN_IFC => TX_BUF_NEWLEN_IFC2,

         BUF_RELLEN     => TX_BUF_RELLEN,
         BUF_RELLEN_IFC => TX_BUF_RELLEN_IFC2,
         BUF_RELLEN_DV  => TX_BUF_RELLEN_DV,

         DESC_DATA      => DESC_DATA,
         DESC_EMPTY     => TX_DESC_EMPTY,
         DESC_IFC       => TX_DESC_ADDR2,
         DESC_READ      => TX_DESC_READ,
         DESC_DV        => TX_DESC_DV,

         DMA_ADDR       => TX_DMA_ADDR,
         DMA_DOUT       => TX_DMA_DOUT,
         DMA_REQ        => TX_DMA_REQ,
         DMA_ACK        => TX_DMA_ACK,
         DMA_DONE       => TX_DMA_DONE,

         ENABLE         => TX_ENABLE,
         INTERRUPT      => TX_INTERRUPT_SIG,
         INTERRUPT_IFC  => TX_INTERRUPT_IFC2,

         SW_ADDR        => mi32_ADDR,
         SW_ARDY        => TX_SW_ARDY,
         SW_BE          => mi32_be,
         SW_DRD         => TX_SW_DRD,
         SW_DRDY        => TX_SW_DRDY,
         SW_DWR         => mi32_dwr,
         SW_RD          => TX_SW_RD,
         SW_WR          => TX_SW_WR
      );
   -----------------------------------------------------------------------------
   --                               Receive buffer                              
   RXBUF_I : entity work.SW_RXBUF_TOP
      generic map(
         DATA_WIDTH     => 64, --DMA_IFC_COUNT / 2 * DATA_WIDTH,
         BLOCK_SIZE     => BLOCK_SIZE,
         FLOWS          => DMA_IFC_COUNT / 2,
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input FrameLink interface
         RX_SOF_N       => RX_SOF_N(DMA_IFC_COUNT/2-1 downto 0),
         RX_SOP_N       => RX_SOP_N(DMA_IFC_COUNT/2-1 downto 0),
         RX_EOP_N       => RX_EOP_N(DMA_IFC_COUNT/2-1 downto 0),
         RX_EOF_N       => RX_EOF_N(DMA_IFC_COUNT/2-1 downto 0),
         RX_SRC_RDY_N   => RX_SRC_RDY_N(DMA_IFC_COUNT/2-1 downto 0),
         RX_DST_RDY_N   => RX_DST_RDY_N(DMA_IFC_COUNT/2-1 downto 0),
         RX_DATA        => RX_DATA((DATA_WIDTH*DMA_IFC_COUNT/2)-1 downto 0),
         RX_REM         => RX_REM((log2(DATA_WIDTH/8)*DMA_IFC_COUNT/2)-1 downto 0),
         -- Memory Read Interface
         RD_ADDR        => ib_rd_addr_buf,
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxbuf_rd_req,
         RD_ARDY        => ib_rxbuf_rd_ardy,
         RD_DATA        => ib_rxbuf_rd_data,
         RD_SRC_RDY     => ib_rxbuf_rd_src_rdy,
         RD_DST_RDY     => ib_rd_dst_rdy,
         -- Receive Buffer Interface
         RX_NEWLEN      => rxbuf_newlen(16*DMA_IFC_COUNT/2-1 downto 0),
         RX_NEWLEN_DV   => rxbuf_newlen_dv(DMA_IFC_COUNT/2-1 downto 0),
         RX_NEWLEN_RDY  => rxbuf_newlen_rdy(DMA_IFC_COUNT/2-1 downto 0),
         RX_RELLEN      => rxbuf_rellen(16*DMA_IFC_COUNT/2-1 downto 0),
         RX_RELLEN_DV   => rxbuf_rellen_dv(DMA_IFC_COUNT/2-1 downto 0)
      );

   RXBUF_I2 : entity work.SW_RXBUF_TOP
      generic map(
         DATA_WIDTH     => 64, --DMA_IFC_COUNT/2 * DATA_WIDTH,
         BLOCK_SIZE     => BLOCK_SIZE,
         FLOWS          => DMA_IFC_COUNT/2,
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input FrameLink interface
         RX_SOF_N       => RX_SOF_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_SOP_N       => RX_SOP_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_EOP_N       => RX_EOP_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_EOF_N       => RX_EOF_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_SRC_RDY_N   => RX_SRC_RDY_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_DST_RDY_N   => RX_DST_RDY_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_DATA        => RX_DATA(DATA_WIDTH*DMA_IFC_COUNT-1 downto DATA_WIDTH*DMA_IFC_COUNT/2),
         RX_REM         => RX_REM(log2(DATA_WIDTH/8)*DMA_IFC_COUNT-1 downto log2(DATA_WIDTH/8)*DMA_IFC_COUNT/2),
         -- Memory Read Interface
         RD_ADDR        => ib_rd_addr_buf,
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxbuf2_rd_req,
         RD_ARDY        => ib_rxbuf2_rd_ardy,
         RD_DATA        => ib_rxbuf2_rd_data,
         RD_SRC_RDY     => ib_rxbuf2_rd_src_rdy,
         RD_DST_RDY     => ib_rd_dst_rdy,
         -- Receive Buffer Interface
         RX_NEWLEN      => rxbuf_newlen(16*DMA_IFC_COUNT-1 downto 16*DMA_IFC_COUNT/2),
         RX_NEWLEN_DV   => rxbuf_newlen_dv(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_NEWLEN_RDY  => rxbuf_newlen_rdy(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         RX_RELLEN      => rxbuf_rellen(16*DMA_IFC_COUNT-1 downto 16*DMA_IFC_COUNT/2),
         RX_RELLEN_DV   => rxbuf_rellen_dv(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2)
      );


   -----------------------------------------------------------------------------
   --                               Transmit buffer                              
   TXBUF_I : entity work.SW_TXBUF_TOP
      generic map(
         DATA_WIDTH     => DMA_IFC_COUNT/2 * DATA_WIDTH,
         BLOCK_SIZE     => BLOCK_SIZE,
         FLOWS          => DMA_IFC_COUNT/2,
         SIZE_LENGTH    => TX_SIZE_LENGTH,
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- output FrameLink interface
         TX_SOF_N       => TX_SOF_N(DMA_IFC_COUNT/2-1 downto 0),
         TX_SOP_N       => TX_SOP_N(DMA_IFC_COUNT/2-1 downto 0),
         TX_EOP_N       => TX_EOP_N(DMA_IFC_COUNT/2-1 downto 0),
         TX_EOF_N       => TX_EOF_N(DMA_IFC_COUNT/2-1 downto 0),
         TX_SRC_RDY_N   => TX_SRC_RDY_N(DMA_IFC_COUNT/2-1 downto 0),
         TX_DST_RDY_N   => TX_DST_RDY_N(DMA_IFC_COUNT/2-1 downto 0),
         TX_DATA        => TX_DATA(DATA_WIDTH*DMA_IFC_COUNT/2-1 downto 0),
         TX_REM         => TX_REM(log2(DATA_WIDTH/8)*DMA_IFC_COUNT/2-1 downto 0),

         -- Memory write Interface
         WR_ADDR        => ib_wr_addr_buf,
         WR_DATA        => ib_wr_data,
         WR_BE          => ib_wr_be,
         WR_REQ         => ib_txbuf_wr_req,
         WR_RDY         => ib_txbuf_wr_rdy,
         -- Transmit Buffer Interface
         TX_NEWLEN      => txbuf_newlen(16*DMA_IFC_COUNT/2-1 downto 0),
         TX_NEWLEN_DV   => txbuf_newlen_dv(DMA_IFC_COUNT/2-1 downto 0),
         TX_NEWLEN_RDY  => txbuf_newlen_rdy(DMA_IFC_COUNT/2-1 downto 0),
         TX_RELLEN      => txbuf_rellen(16*DMA_IFC_COUNT/2-1 downto 0),
         TX_RELLEN_DV   => txbuf_rellen_dv(DMA_IFC_COUNT/2-1 downto 0)
      );

   TXBUF_I2 : entity work.SW_TXBUF_TOP
      generic map(
         DATA_WIDTH     => DMA_IFC_COUNT/2 * DATA_WIDTH,
         BLOCK_SIZE     => BLOCK_SIZE,
         FLOWS          => DMA_IFC_COUNT/2,
         SIZE_LENGTH    => TX_SIZE_LENGTH,
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- output FrameLink interface
         TX_SOF_N       => TX_SOF_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_SOP_N       => TX_SOP_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_EOP_N       => TX_EOP_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_EOF_N       => TX_EOF_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_SRC_RDY_N   => TX_SRC_RDY_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_DST_RDY_N   => TX_DST_RDY_N(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_DATA        => TX_DATA(DATA_WIDTH*DMA_IFC_COUNT-1 downto DATA_WIDTH*DMA_IFC_COUNT/2),
         TX_REM         => TX_REM(log2(DATA_WIDTH/8)*DMA_IFC_COUNT-1 downto log2(DATA_WIDTH/8)*DMA_IFC_COUNT/2),
         -- Memory write Interface
         WR_ADDR        => ib_wr_addr_buf,
         WR_DATA        => ib_wr_data,
         WR_BE          => ib_wr_be,
         WR_REQ         => ib_txbuf2_wr_req,
         WR_RDY         => ib_txbuf2_wr_rdy,
         -- Transmit Buffer Interface
         TX_NEWLEN      => txbuf_newlen(16*DMA_IFC_COUNT-1 downto 16*DMA_IFC_COUNT/2),
         TX_NEWLEN_DV   => txbuf_newlen_dv(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_NEWLEN_RDY  => txbuf_newlen_rdy(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2),
         TX_RELLEN      => txbuf_rellen(16*DMA_IFC_COUNT-1 downto 16*DMA_IFC_COUNT/2),
         TX_RELLEN_DV   => txbuf_rellen_dv(DMA_IFC_COUNT-1 downto DMA_IFC_COUNT/2)
      );


   -----------------------------------------------------------------------------
   --                         Descriptor manager instance                       
   DESC_MANAGER_I: entity work.desc_manager_gcc
      generic map(
         BASE_ADDR      => DESC_BASE_ADDR,
         FLOWS          => 2*DMA_IFC_COUNT,
         -- e.g DOWNLOADED_BLOCK_SIZE:
         BLOCK_SIZE     => DESC_BLOCK_SIZE,
         DMA_DATA_WIDTH => 64
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Memory write interface
         WR_ADDR        => ib_wr_addr,
         WR_DATA        => ib_wr_data,
         WR_BE          => ib_wr_be,
         WR_REQ         => ib_desc_wr_req,
         WR_RDY         => ib_desc_wr_rdy,
         -- DMA Interface --
         DMA_ADDR       => desc_dma_addr,
         DMA_DOUT       => desc_dma_dout,
         DMA_REQ        => desc_dma_req,
         DMA_ACK        => desc_dma_ack,
         DMA_DONE       => desc_dma_done,
         DMA_TAG        => desc_dma_tag,
         -- DMA ctrls interface
         DESC_READ      => desc_read,
         DESC_DATA      => desc_data,
         DESC_ADDR      => desc_addr,
         DESC_EMPTY     => desc_empty,
         DESC_DVLD      => desc_dvld,
         DESC_PIPE_EN   => desc_pipe_en,
         -- Per channel enable interface
         ENABLE         => desc_enable
      );

     IB_ENDPOINT_I: entity work.IB_ENDPOINT_MASTER_NOREC
      generic map(
         LIMIT             => IB_EP_LIMIT,
         INPUT_BUFFER_SIZE => IB_EP_INPUT_BUFFER_SIZE,
         OUTPUT_BUFFER_SIZE  => IB_EP_OUTPUT_BUFFER_SIZE,
         READ_REORDER_BUFFER => IB_EP_READ_REORDER_BUFFER,
         STRICT_EN         => IB_EP_STRICT_EN
      )
      port map(
         IB_CLK            => CLK,
         IB_RESET          => RESET,
            -- Internal Bus Interface
            -- DOWNSTREAM
         IB_DOWN_DATA      => DOWN_DATA,
         IB_DOWN_SOP_N     => DOWN_SOP_N,
         IB_DOWN_EOP_N     => DOWN_EOP_N,
         IB_DOWN_SRC_RDY_N => DOWN_SRC_RDY_N,
         IB_DOWN_DST_RDY_N => DOWN_DST_RDY_N,
           -- UPSTREAM
         IB_UP_DATA        => UP_DATA,
         IB_UP_SOP_N       => UP_SOP_N,
         IB_UP_EOP_N       => UP_EOP_N,
         IB_UP_SRC_RDY_N   => UP_SRC_RDY_N,
         IB_UP_DST_RDY_N   => UP_DST_RDY_N,
         -- Write Interface
         WR_ADDR           => ib_wr_addr,
         WR_DATA           => ib_wr_data,
         WR_BE             => ib_wr_be,
         WR_REQ            => ib_wr_req,
         WR_RDY            => ib_wr_rdy,
         WR_LENGTH         => ib_wr_length,
         WR_SOF            => ib_wr_sof,
         WR_EOF            => ib_wr_eof,
         -- Read Interface
         -- Input Interface
         RD_ADDR           => ib_rd_addr,
         RD_BE             => ib_rd_be,
         RD_REQ            => ib_rd_req,
         RD_ARDY           => ib_rd_ardy,
         RD_SOF_IN         => ib_rd_sof_in,
         RD_EOF_IN         => ib_rd_eof_in,
         -- Output Interface
         RD_DATA           => ib_rd_data,
         RD_SRC_RDY        => ib_rd_src_rdy,
         RD_DST_RDY        => ib_rd_dst_rdy,
         -- Master Interface Input
         BM_GLOBAL_ADDR    => ib_bm_global_addr,
         BM_LOCAL_ADDR     => ib_bm_local_addr,
         BM_LENGTH         => ib_bm_length,
         BM_TAG            => ib_bm_tag,
         BM_TRANS_TYPE     => ib_bm_trans_type,
         BM_REQ            => ib_bm_req,
         BM_ACK            => ib_bm_ack,
         -- Master Output interface
         BM_OP_TAG         => ib_bm_op_tag,
         BM_OP_DONE        => ib_bm_op_done
      ); 

       ib_bm_tag(15 downto 8) <= X"00";
 
       tag_seq_i : entity work.TAG_SEQUENCER_TOP
       generic map(
          EP_TAG_WIDTH   => 8,
          USR_TAG_WIDTH  => 16
       )
       port map(
          CLK         => CLK,
          RESET       => RESET,
 
          USR_TAG        => bm_tag,
          USR_REQ        => bm_req,
          USR_ACK        => bm_ack,
          USR_TRANS_TYPE => bm_trans_type,
          EP_TAG         => ib_bm_tag(7 downto 0),
          EP_REQ         => ib_bm_req,
          EP_ACK         => ib_bm_ack,
          EP_TRANS_TYPE  => ib_bm_trans_type,
 
          EP_OP_TAG      => ib_bm_op_tag(7 downto 0),
          EP_OP_DONE     => ib_bm_op_done,
          USR_OP_TAG     => bm_op_tag,
          USR_OP_DONE    => bm_op_done,
 
          WR_FULL           => open,
          WR_EMPTY          => open,
          RD_FULL           => open,
          RD_EMPTY          => open
       );
 
   -----------------------------------------------------------------------------
   --                         Local bus endpoint instance                       
   LB_ENDPOINT_I: entity work.LB_ENDPOINT_NOREC
   generic map(
      BASE_ADDR         => LB_EP_BASE_ADDR,
      LIMIT             => LB_EP_LIMIT,
      FREQUENCY         => LB_EP_FREQUENCY,
      BUFFER_EN         => LB_EP_BUFFER_EN
   )
   port map(
      RESET             => RESET,
      LB_CLK            => CLK,

      LB_DWR            => LB_DWR,
      LB_BE             => LB_BE,
      LB_ADS_N          => LB_ADS_N,
      LB_RD_N           => LB_RD_N,
      LB_WR_N           => LB_WR_N,
      LB_DRD            => LB_DRD,
      LB_RDY_N          => LB_RDY_N,
      LB_ERR_N          => LB_ERR_N,
      LB_ABORT_N        => LB_ABORT_N,

      -- User Component Interface
      CLK               => CLK,
      MI32_DWR          => mi32_dwr,
      MI32_ADDR         => mi32_addr,
      MI32_RD           => mi32_rd,
      MI32_WR           => mi32_wr,
      MI32_BE           => mi32_be,
      MI32_DRD          => mi32_drd,
      MI32_ARDY         => mi32_ardy,
      MI32_DRDY         => mi32_drdy
   );

   ---------------------------------------------------------------------------
   --                          Status register instance                         
   RX_DMA_STATUS_REG_I: entity work.DMA_STATUS_REG
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Internal Bus interface
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxcontrol_rd_req,
         RD_DATA        => ib_rxcontrol_rd_data,
         -- DMA Controller interface
         SET_INTERRUPT  => rx_interrupt_set
      );

   TX_DMA_STATUS_REG_I: entity work.DMA_STATUS_REG
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Internal Bus interface
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_txcontrol_rd_req,
         RD_DATA        => ib_txcontrol_rd_data,
         -- DMA Controller interface
         SET_INTERRUPT  => tx_interrupt_set
      );

   -----------------------------------------------------------------------------
   --                         DMA2DATA for RX Controller                        
   DMA2DATA_RX_I : entity work.DMA2DATA
      generic map(
         -- frame data width in bits
         DMA_DATA_WIDTH => 32
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         DMA_ADDR       => RX_DMA_ADDR,
         DMA_DOUT       => RX_DMA_DOUT,
         DMA_REQ        => RX_DMA_REQ,
         DMA_ACK        => RX_DMA_ACK,
         DMA_DONE       => open,
         DMA_TAG        => open,
         -- output interface
         TX_SRC_RDY_N   => dma_tx_src_rdy_n(0),
         TX_DST_RDY_N   => dma_tx_dst_rdy_n(0),
         TX_DATA        => dma_tx_data(31 downto 0),
         -- output tag interface
         TX_DMA_DONE    => data2bm_dma_done,
         TX_DMA_TAG     => data2bm_dma_tag
      );

   -----------------------------------------------------------------------------
   --                         DMA2DATA for TX Controller                        
   DMA2DATA_TX_I : entity work.DMA2DATA
      generic map(
         DMA_DATA_WIDTH => 32
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         DMA_ADDR       => TX_DMA_ADDR,
         DMA_DOUT       => TX_DMA_DOUT,
         DMA_REQ        => TX_DMA_REQ,
         DMA_ACK        => TX_DMA_ACK,
         DMA_DONE       => open,
         DMA_TAG        => open,
         -- output interface
         TX_SRC_RDY_N   => dma_tx_src_rdy_n(1),
         TX_DST_RDY_N   => dma_tx_dst_rdy_n(1),
         TX_DATA        => dma_tx_data(63 downto 32),
         -- output tag interface
         TX_DMA_DONE    => data2bm_dma_done,
         TX_DMA_TAG     => data2bm_dma_tag
      );

   -----------------------------------------------------------------------------
   --                       DMA2DATA for Descriptor Manager                     
   DMA2DATA_DESCMAN_I : entity work.DMA2DATA
      generic map(
         -- frame data width in bits
         DMA_DATA_WIDTH => 64
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

   -----------------------------------------------------------------------------
   --                   MultiFifo for data from DMA Controllers                 
   NFIFO2FIFO_I : entity work.NFIFO2FIFO
      generic map(
         DATA_WIDTH     => 64,
         FLOWS          => 2,
         BLOCK_SIZE     => 2,
         LUT_MEMORY     => true,
         GLOB_STATE     => false
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         DATA_IN        => dma_tx_data,
         WRITE          => dma_tx_src_rdy,
         FULL           => dma_tx_dst_rdy,
         -- read interface
         DATA_OUT       => mfifo1_data_out,
         DATA_VLD       => mfifo1_data_vld,
         BLOCK_ADDR     => mfifo1_block_addr,
         READ           => mfifo1_read,
         PIPE_EN        => mfifo1_read, -- TODO: Check
         EMPTY          => mfifo1_empty
      );

   -----------------------------------------------------------------------------
   --       MultiFifo for data from Descriptor Manager and DMA Controllers      
   NFIFO2FIFO_II : entity work.NFIFO2FIFO
      generic map(
         DATA_WIDTH     => 2*64,
         FLOWS          => 2,
         BLOCK_SIZE     => 2,
         LUT_MEMORY     => true,
         GLOB_STATE     => false
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- write interface
         DATA_IN        => mfifo2_data_in,
         WRITE          => mfifo2_write,
         FULL           => mfifo2_full,
         -- read interface
         DATA_OUT       => mfifo2_data_out,
         DATA_VLD       => mfifo2_data_vld,
         BLOCK_ADDR     => mfifo2_block_addr,
         READ           => mfifo2_read,
         PIPE_EN        => mfifo2_read,    -- TODO: Check
         EMPTY          => mfifo2_empty
      );

   -----------------------------------------------------------------------------
   --                         Data to BusMaster instance                        
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
         BM_GLOBAL_ADDR => ib_BM_GLOBAL_ADDR,
         BM_LOCAL_ADDR  => ib_BM_LOCAL_ADDR,
         BM_LENGTH      => ib_BM_LENGTH,
         BM_TAG         => BM_TAG,
         BM_TRANS_TYPE  => BM_TRANS_TYPE,
         BM_REQ         => BM_REQ,
         BM_ACK         => BM_ACK,
         -- Output
         BM_OP_TAG      => BM_OP_TAG,
         BM_OP_DONE     => BM_OP_DONE
      );

   -----------------------------------------------------------------------------
   --                               MI32 connection                             
   mi32_drd             <= RX_SW_DRD or TX_SW_DRD;
   mi32_ardy            <= RX_SW_ARDY or TX_SW_ARDY;
   mi32_drdy            <= RX_SW_DRDY or TX_SW_DRDY;

   RX_SW_RD             <= mi32_rd and not mi32_addr(6);
   RX_SW_WR             <= mi32_wr and not mi32_addr(6);
   TX_SW_RD             <= mi32_rd and mi32_addr(6);
   TX_SW_WR             <= mi32_wr and mi32_addr(6);

   -----------------------------------------------------------------------------
   --                  Control (interrupt) registers connection                 
   tx_interrupt         <= tx_interrupt_sig(0);
   rx_interrupt         <= rx_interrupt_sig(0) or rx_interrupt_sig(1);

   interruptp : process(rx_interrupt_sig, tx_interrupt_sig, reset, rx_interrupt_ifc, tx_interrupt_ifc)

   begin
      if(reset = '1') then
         rx_interrupt_set(63 downto 0) <= (others => '0');
         tx_interrupt_set(63 downto 0) <= (others => '0');
      else -- if(CLK'event and CLK = '1') then
         if(rx_interrupt_sig(0) = '1') then
            rx_interrupt_set(2*DMA_IFC_COUNT-1 downto 0) <= (decode(rx_interrupt_ifc & '0'));
         elsif(rx_interrupt_sig(1) = '1') then
            rx_interrupt_set(2*DMA_IFC_COUNT-1 downto 0) <= (decode(rx_interrupt_ifc & '1'));
         else
            rx_interrupt_set(63 downto 0) <= (others => '0');
         end if;

         if(tx_interrupt_sig(0) = '1') then
            tx_interrupt_set(2*DMA_IFC_COUNT-1 downto 0) <= (decode(tx_interrupt_ifc & '0'));
         else
            tx_interrupt_set(63 downto 0) <= (others => '0');
         end if;
      end if;
   end process;

   -----------------------------------------------------------------------------
   --                            MultiFifo connection                           
   mfifo1_word_transmission <= mfifo1_data_vld and mfifo1_read;
   cnt_mfifo1_words_ce  <= mfifo1_word_transmission;
   cnt_block_addr_ce    <= (mfifo1_word_transmission and cnt_mfifo1_words) or (not cnt_mfifo1_words and not mfifo1_data_vld);
   dma_tx_src_rdy       <= not dma_tx_src_rdy_n;
   dma_tx_dst_rdy_n     <= dma_tx_dst_rdy;

   data2bm_rx_src_rdy_n <= not mfifo2_data_vld;
   mfifo2_read          <= not data2bm_rx_dst_rdy_n;
   mfifo2_data_in       <= desc_tx_data & mfifo1_data_out;
   mfifo2_write         <= (not desc_tx_src_rdy_n) & mfifo1_data_vld;
   mfifo1_read          <= not mfifo2_full(0);
   desc_tx_dst_rdy_n    <= mfifo2_full(1);

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

   -----------------------------------------------------------------------------
   --                  RX & TX Buffer <---> DMA Controller connection                
   RXBUF_NEWLEN_RDY <= (others => '1'); -- It is ignored

   genlenmux: if DMA_IFC_COUNT > 1 generate
      newlen_mux: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => 16,
         MUX_WIDTH => DMA_IFC_COUNT
      )  port map(
         DATA_IN => rxbuf_newlen_reg,
         SEL => rx_newlen_ifc,
         DATA_OUT => rx_buf_newlen
      );
      rellen_mux: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => 16,
         MUX_WIDTH => DMA_IFC_COUNT
      )  port map(
         DATA_IN => txbuf_rellen_reg,
         SEL => tx_rellen_ifc,
         DATA_OUT => tx_buf_rellen
      );
   end generate;

   genlenmux2: if DMA_IFC_COUNT = 1 generate
      rx_buf_newlen <= rxbuf_newlen_reg;
      tx_buf_rellen <= txbuf_rellen_reg;
   end generate;

   pdv:  process(RX_BUF_NEWLEN, TX_BUF_RELLEN)
   begin
      if(RX_BUF_NEWLEN = X"0000") then
         rx_buf_newlen_dv <= '0';
      else
         rx_buf_newlen_dv <= '1';
      end if;

      if(TX_BUF_RELLEN = X"0000") then
         tx_buf_rellen_dv <= '0';
      else
         tx_buf_rellen_dv <= '1';
      end if;
   end process;

   newlen_ifcp : process(CLK, RESET, rx_newlen_ifc)
   begin
      if (RESET = '1') then
         rx_newlen_ifc     <= (others => '0');
         tx_rellen_ifc     <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         rx_newlen_ifc     <= rx_newlen_ifc + 1;
         tx_rellen_ifc     <= tx_rellen_ifc + 1;
      end if;

   end process;

   tx_buf_rellen_ifc <= tx_rellen_ifc;
   rx_buf_newlen_ifc <= rx_newlen_ifc;
   rellen_read       <= decode(tx_rellen_ifc);
   newlen_read       <= decode(rx_newlen_ifc);

   gen_rxbuf: for i in 0 to DMA_IFC_COUNT-1 generate
      RXBUF_RELLEN((i+1)*16-1 downto i*16) <= RX_BUF_RELLEN;
      DESC_ENABLE(i*2) <= RX_ENABLE(i);

      newlen_regp : process(CLK, RXBUF_NEWLEN, RXBUF_NEWLEN_DV, NEWLEN_READ)
      begin
         if (CLK'event AND CLK = '1') then
            if(RXBUF_NEWLEN_DV(i) = '1' and newlen_read(i) = '1') then
               rxbuf_newlen_reg((i+1)*16-1 downto i*16) <= RXBUF_NEWLEN((i+1)*16-1 downto i*16);
            elsif(RXBUF_NEWLEN_DV(i) = '1') then
               rxbuf_newlen_reg((i+1)*16-1 downto i*16) <= rxbuf_newlen_reg((i+1)*16-1 downto i*16) + RXBUF_NEWLEN((i+1)*16-1 downto i*16); 
            elsif(newlen_read(i) = '1') then
               rxbuf_newlen_reg((i+1)*16-1 downto i*16) <= (others => '0');
            end if;
         end if;
      end process;
   end generate;

   gen_txbuf: for i in 0 to DMA_IFC_COUNT-1 generate
      TXBUF_NEWLEN((i+1)*16-1 downto i*16) <= TX_BUF_NEWLEN;
      DESC_ENABLE(i*2+1) <= TX_ENABLE(i);
  
      rellen_regp : process(CLK, TXBUF_RELLEN, TXBUF_RELLEN_DV, rellen_read)
      begin
         if (CLK'event AND CLK = '1') then
            if(TXBUF_RELLEN_DV(i) = '1' and rellen_read(i) = '1') then
               txbuf_rellen_reg((i+1)*16-1 downto i*16) <= TXBUF_RELLEN((i+1)*16-1 downto i*16);
            elsif(TXBUF_RELLEN_DV(i) = '1') then
               txbuf_rellen_reg((i+1)*16-1 downto i*16) <= txbuf_rellen_reg((i+1)*16-1 downto i*16) + TXBUF_RELLEN((i+1)*16-1 downto i*16);
            elsif(rellen_read(i) = '1') then
               txbuf_rellen_reg((i+1)*16-1 downto i*16) <= (others => '0');
            end if;
         end if;
      end process;
   end generate;

   -----------------------------------------------------------------------------
   --                       Common RX/TX Buffer connection                      
   buf_dv: process (TX_BUF_NEWLEN_DV, RX_BUF_RELLEN_DV, TX_BUF_NEWLEN_IFC, RX_BUF_RELLEN_IFC2, TX_BUF_NEWLEN_IFC2,  RX_BUF_RELLEN_IFC)
   begin
      if(RX_BUF_RELLEN_DV = '1') then
         RXBUF_RELLEN_DV <= decode(RX_BUF_RELLEN_IFC);
      else
         RXBUF_RELLEN_DV <= (others => '0'); 
      end if;
      if(TX_BUF_NEWLEN_DV = '1') then
         TXBUF_NEWLEN_DV <= decode(TX_BUF_NEWLEN_IFC);
      else
         TXBUF_NEWLEN_DV <= (others => '0'); 
      end if;
   end process;

   desc_emptyp: process(rx_desc_addr, tx_desc_addr, desc_empty)
   begin
      rx_desc_empty <= genmux(rx_desc_addr & '0', desc_empty);
      tx_desc_empty <= genmux(tx_desc_addr & '1', desc_empty);
   end process;

   -----------------------------------------------------------------------------
   --                   Descriptor manager sharing - switching                  
   cnt_rx_tx_desc : process(CLK, RESET)
   begin
      if (RESET = '1') then
         rx_tx_desc <= "0";
      elsif (CLK'event AND CLK = '1')  then
         rx_tx_desc <= rx_tx_desc + 1;
      end if;
   end process;

   desc_switch : process(CLK,RESET, rx_tx_desc)
   begin
      if(RESET = '1') then
      else
         rs_desc_read_reset <= decode(rx_tx_desc);
         if(rx_tx_desc(0) = '0') then     -- RX is active
            DESC_READ <= rs_desc_read(0);
            rs_desc_read_reset(0) <= '1';
            DESC_ADDR <= RX_DESC_ADDR & '0';
            TX_DESC_DV <= DESC_DVLD;      -- Special timing...
            RX_DESC_DV <= '0';
         else                             -- TX is active
            DESC_READ <= rs_desc_read(1);
            rs_desc_read_reset(1) <= '1';
            DESC_ADDR <= TX_DESC_ADDR & '1';
            RX_DESC_DV <= DESC_DVLD;      -- The same here...
            TX_DESC_DV <= '0';
         end if;
      end if;
   end process;

   desc_rs: process(CLK, RESET, rs_desc_read_reset, rs_desc_read_set)
   begin
      if(RESET = '1') then
         rs_desc_read <= (others => '0');
      elsif(CLK'event and CLK = '1') then
         if(rs_desc_read_set(0) = '1') then
            rs_desc_read(0) <= '1';
         elsif(rs_desc_read_reset(0) = '1') then
          rs_desc_read(0) <= '0';
         end if;
         if(rs_desc_read_set(1) = '1') then
            rs_desc_read(1) <= '1';
         elsif(rs_desc_read_reset(1) = '1') then
          rs_desc_read(1) <= '0';
         end if;
      end if;
   end process;
   rs_desc_read_set(0) <= RX_DESC_READ;
   rs_desc_read_set(1) <= TX_DESC_READ;

   desc_pipe_en <= '1';

   rx_dma_done <= data2bm_dma_done and not data2bm_dma_tag(0) and not data2bm_dma_tag(7);
   tx_dma_done <= data2bm_dma_done and     data2bm_dma_tag(0) and not data2bm_dma_tag(7);

   -----------------------------------------------------------------------------
   --                   Internal Bus addressing and switchning                  
   -- register reg_rd_addr
   reg_rd_addrp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_rd_addr <= (others => '0');
         elsif (ib_rd_ardy_buf = '1') then
            reg_rd_addr <= ib_rd_addr;
         end if;
      end if;
   end process;

   -- read request signals
   ib_rxbuf_rd_req      <= ib_rd_req and ib_rxbuf_rd_sel;
   ib_rxbuf2_rd_req     <= ib_rd_req and ib_rxbuf2_rd_sel;
   ib_txbuf_rd_req      <= ib_rd_req and ib_txbuf_rd_sel;
   ib_txbuf2_rd_req     <= ib_rd_req and ib_txbuf2_rd_sel;
   ib_rxcontrol_rd_req  <= ib_rd_req and ib_rxcontrol_rd_sel and ib_rd_ardy_buf;
   ib_txcontrol_rd_req  <= ib_rd_req and ib_txcontrol_rd_sel and ib_rd_ardy_buf;
   ib_desc_rd_req       <= ib_rd_req and ib_desc_rd_sel;
   -- write request signals
   ib_rxbuf_wr_req      <= ib_wr_req and ib_rxbuf_wr_sel;
   ib_rxbuf2_wr_req     <= ib_wr_req and ib_rxbuf2_wr_sel;
   ib_txbuf_wr_req      <= ib_wr_req and ib_txbuf_wr_sel;
   ib_txbuf2_wr_req     <= ib_wr_req and ib_txbuf2_wr_sel;
   ib_rxcontrol_wr_req  <= ib_wr_req and ib_rxcontrol_wr_sel;
   ib_txcontrol_wr_req  <= ib_wr_req and ib_txcontrol_wr_sel;
   ib_desc_wr_req       <= ib_wr_req and ib_desc_wr_sel;

   -- read chip select
   rd_csp: process( ib_rd_addr )
   begin
      ib_rxbuf_rd_sel   <= '0';
      ib_rxbuf2_rd_sel   <= '0';
      ib_txbuf_rd_sel   <= '0';
      ib_txbuf2_rd_sel   <= '0';
      ib_rxcontrol_rd_sel <= '0';
      ib_txcontrol_rd_sel <= '0';
      ib_desc_rd_sel    <= '0';

      case ib_rd_addr (21) is
         -- buffers address space -----------------------------
         when '0' =>
            case ib_rd_addr(20) is
               when '0'    => -- RX buffer is selected
                  case ib_rd_addr(13) is
                     when '0'    => ib_rxbuf_rd_sel  <= '1';
                     when '1'    => ib_rxbuf2_rd_sel <= '1';
                     when others => null;
                  end case;
               when '1'    => -- TX buffer is selected
                  case ib_rd_addr(13) is
                     when '0'    => ib_txbuf_rd_sel  <= '1';
                     when '1'    => ib_txbuf2_rd_sel <= '1';
                     when others => null;
                  end case;
               when others => null;
            end case;
         -- ---------------------------------------------------
         -- descriptor manager address space ------------------
         when '1' =>
            case ib_rd_addr(19) is
               when '0'    => ib_desc_rd_sel       <= '1';
               -- interrupt control registers -----------------
               when '1'    =>    
                  case ib_rd_addr(3) is
                     when '0'    => ib_rxcontrol_rd_sel  <= '1';
                     when '1'    => ib_txcontrol_rd_sel  <= '1';
                     when others => null;
                  end case;
               when others => null;
            end case;
         when others => null;
      end case;
      -- ------------------------------------------------------
   end process;

   -- write chip select
   wr_csp: process( ib_wr_addr )
   begin
      ib_rxbuf_wr_sel      <= '0';
      ib_rxbuf2_wr_sel     <= '0';
      ib_txbuf_wr_sel      <= '0';
      ib_txbuf2_wr_sel     <= '0';
      ib_rxcontrol_wr_sel  <= '0';
      ib_txcontrol_wr_sel  <= '0';
      ib_desc_wr_sel       <= '0';

      case ib_wr_addr (21) is
         -- buffers address space -----------------------------
         when '0' =>         
            case ib_wr_addr(20) is
               when '0'    => -- RX buffer is selected
                  case ib_wr_addr(13) is
                     when '0'    => ib_rxbuf_wr_sel  <= '1';
                     when '1'    => ib_rxbuf2_wr_sel <= '1';
                     when others => null;
                  end case;
               when '1'    => -- TX buffer is selected
                  case ib_wr_addr(13) is
                     when '0'    => ib_txbuf_wr_sel  <= '1';
                     when '1'    => ib_txbuf2_wr_sel <= '1';
                     when others => null;
                  end case;
               when others => null;
            end case;
         -- ---------------------------------------------------
         -- descriptor manager address space ------------------
         when '1' =>
            case ib_wr_addr(19) is
               when '0'    => ib_desc_wr_sel       <= '1';
               -- interrupt control register -------------------
               when '1'    =>    
                  case ib_wr_addr(3) is
                     when '0'    => ib_rxcontrol_wr_sel  <= '1';
                     when '1'    => ib_txcontrol_wr_sel  <= '1';
                     when others => null;
                  end case;
                  -- -------------------------------------------
               when others => null;
            end case;
            -- ------------------------------------------------
         when others => null;
      end case;
      -- ------------------------------------------------------
   end process;

   -- Status registers output mx - registered
   reg_dma_statp: process (CLK)
   begin
      if (clk'event and clk = '1') then
         if (ib_rd_ardy_buf = '1') then
            reg_dma_stat <= mx_dma_stat;
         end if;
      end if;
   end process;


   mx_status_outp: process (ib_txcontrol_rd_sel, ib_rxcontrol_rd_data, ib_txcontrol_rd_data)
   begin
      case ib_txcontrol_rd_sel is
         when '0' =>    mx_dma_stat <= ib_rxcontrol_rd_data;
         when '1' =>    mx_dma_stat <= ib_txcontrol_rd_data;
         when others => mx_dma_stat <= (others => 'X');
      end case;
   end process;

   -- data out multiplexing
   rd_datap: process( reg_rd_addr, ib_rxbuf_rd_data, ib_rxcontrol_rd_data, ib_txcontrol_rd_data, ib_desc_rd_data )
   begin
      case reg_rd_addr (21) is
         when '0' =>          -- buffers
            case reg_rd_addr(20) is
               when '0'  => 
               case reg_rd_addr(13) is
                     when '0'    => ib_rd_data <= ib_rxbuf_rd_data;
                     when '1'    => ib_rd_data <= ib_rxbuf2_rd_data;
                     when others => ib_rd_data <= (others => '0');
                  end case;
               --when '1'  => ib_rd_data <= ib_txbuf_rd_data;      -- no read from tx buffers
               when others => ib_rd_data <= (others => '0');
            end case;
         when '1' =>          -- desc
            case reg_rd_addr(19) is
--                when '0' => ib_rd_data <= ib_desc_rd_data;    -- no read from descriptor manager
               when '1'    => ib_rd_data <= reg_dma_stat;   -- interrupt control registers
               when others => ib_rd_data <= (others => '0');
            end case;
         when others => null;
      end case;
   end process;

   ib_rxcontrol_rd_ardy <= ib_rxcontrol_rd_sel and ib_rd_dst_rdy;
   ib_txcontrol_rd_ardy <= ib_txcontrol_rd_sel and ib_rd_dst_rdy;

   -- ardy multiplexing
   rd_ardyp: process(clk, ib_rd_addr, ib_rxbuf_rd_ardy, ib_rxcontrol_rd_ardy, ib_txcontrol_rd_ardy, ib_desc_rd_ardy)
   begin
      case ib_rd_addr (21) is
         when '0' =>          -- buffers
            case ib_rd_addr(20) is
               when '0' =>
                  case ib_rd_addr(13) is
                     when '0'    => ib_rd_ardy_buf <= ib_rxbuf_rd_ardy;
                     when '1'    => ib_rd_ardy_buf <= ib_rxbuf2_rd_ardy;
                     when others => ib_rd_ardy_buf <= '0';
                  end case;
               --when '1' => ib_rd_ardy_buf <= ib_txbuf_rd_ardy;      -- no read from tx buffers
               when others => ib_rd_ardy_buf <= '0';
            end case;
         when '1' =>          -- desc
            case ib_rd_addr(19) is
--                when '0' => ib_rd_ardy_buf <= ib_desc_rd_ardy;    -- no read from descriptor manager
               when '1' =>    -- interrupt control register
                  case ib_rd_addr(3) is
                     when '0' => ib_rd_ardy_buf <= ib_rxcontrol_rd_ardy;
                     when '1' => ib_rd_ardy_buf <= ib_txcontrol_rd_ardy;
                     when others => ib_rd_ardy_buf <= '0';
                  end case;
               when others => ib_rd_ardy_buf <= '0';
            end case;
         when others => ib_rd_ardy_buf <= '0';
      end case;
   end process;

   ib_rd_ardy <= ib_rd_ardy_buf;

   -- register reg_ib_rxc_rd_src_rdy ------------------------------------------------------
   reg_ib_rxc_rd_src_rdyp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_ib_rxc_rd_src_rdy <= '0';
         elsif (ib_rd_dst_rdy = '1') then
            reg_ib_rxc_rd_src_rdy <= ib_rxcontrol_rd_req;
         end if;
      end if;
   end process;

   -- register reg_ib_txc_rd_src_rdy ------------------------------------------------------
   reg_ib_txc_rd_src_rdyp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_ib_txc_rd_src_rdy <= '0';
         elsif (ib_rd_dst_rdy = '1') then
            reg_ib_txc_rd_src_rdy <= ib_txcontrol_rd_req;
         end if;
      end if;
   end process;

--    ib_rxcontrol_rd_src_rdy <= ib_rxcontrol_rd_req and ib_rd_ardy_buf;
--    ib_txcontrol_rd_src_rdy <= ib_txcontrol_rd_req and ib_rd_ardy_buf;

   -- src_rdy multiplexing
   rd_src_rdyp: process(reg_rd_addr, ib_rxbuf_rd_src_rdy, ib_rxbuf2_rd_src_rdy, reg_ib_rxc_rd_src_rdy, reg_ib_txc_rd_src_rdy, ib_desc_rd_src_rdy )
   begin
      case reg_rd_addr (21) is
         when '0' =>          -- buffers
            case reg_rd_addr(20) is
               when '0'    => -- RX buffer is selected
                  case reg_rd_addr(13) is
                     when '0'    => ib_rd_src_rdy <= ib_rxbuf_rd_src_rdy;
                     when '1'    => ib_rd_src_rdy <= ib_rxbuf2_rd_src_rdy;
                     when others => ib_rd_src_rdy <= '0';
                  end case;
               --when '1' => ib_rd_src_rdy <= ib_txbuf_rd_src_rdy;      -- no read from tx buffers
               when others => ib_rd_src_rdy <= '0';
            end case;
         when '1' =>          -- desc
            case reg_rd_addr(19) is
               -- when '0' => ib_rd_src_rdy <= ib_desc_rd_src_rdy;    -- no read from descriptor manager
               when '1' =>    -- interrupt control register
                  case reg_rd_addr(3) is
                     when '0' => ib_rd_src_rdy <= reg_ib_rxc_rd_src_rdy;
                     when '1' => ib_rd_src_rdy <= reg_ib_txc_rd_src_rdy;
                     when others => ib_rd_src_rdy <= '0';
                  end case;
               when others => ib_rd_src_rdy <= '0';
            end case;
         when others => ib_rd_src_rdy <= '0';
      end case;
   end process;
   
   -- wr_rdy multiplexing
   wr_rdyp: process( ib_wr_addr, ib_txbuf_wr_rdy, ib_txbuf2_wr_rdy, ib_desc_wr_rdy )
   begin
      case ib_wr_addr (21) is
         when '0' =>          -- buffers
            case ib_wr_addr(20) is
               --when '0' => ib_wr_rdy <= ib_rxbuf_wr_rdy;     -- no write to rx buffers
               when '1'    => -- TX buffer is selected
                  case ib_wr_addr(13) is
                     when '0'    => ib_wr_rdy <= ib_txbuf_wr_rdy;
                     when '1'    => ib_wr_rdy <= ib_txbuf2_wr_rdy;
                     when others => ib_wr_rdy <= '0';
                  end case;
               when others => ib_wr_rdy <= '0';
            end case;
         when '1' =>          -- desc
            case ib_wr_addr(19) is
               when '0' => ib_wr_rdy <= ib_desc_wr_rdy;    
               when '1' =>    -- interrupt control register -- no write to control register
                  case ib_wr_addr(3) is
                     --when '0' => ib_wr_rdy <= ib_rxcontrol_wr_rdy;
                     --when '1' => ib_wr_rdy <= ib_txcontrol_wr_rdy;
                     when others => ib_wr_rdy <= '0';
                  end case;
               when others => ib_wr_rdy <= '0';
            end case;
         when others => ib_wr_rdy <= '0';
      end case;
   end process;

   -- create correct addresses for buffers
   ib_wr_addr_buf(19 downto 0)  <=  ib_wr_addr(19 downto 0);
   ib_wr_addr_buf(31 downto 20) <= (others => '0');

   ib_rd_addr_buf(19 downto 0)  <=  ib_rd_addr(19 downto 0);
   ib_rd_addr_buf(31 downto 20) <= (others => '0');

end architecture behaviour;

