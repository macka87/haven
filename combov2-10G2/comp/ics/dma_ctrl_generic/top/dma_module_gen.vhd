-- dma_module_gen.vhd: Generic RX/TX DMA Module
-- Copyright (C) 2010 CESNET
-- Author(s): Karel Koranda <xkoran01@stud.fit.vutbr.cz>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
-- log2 function
use work.math_pack.all;
-- Internal bus package
use work.ib_ifc_pkg.all;

-- -----------------------------------------------------------------------------
--                              Entity declaration
-- -----------------------------------------------------------------------------
entity DMA_MODULE_GEN is
   generic (
      -- Common RXTX BUFFERs and DMA Controller generics -------------------------
      --* Number of RX DMA channels
      RX_IFC_COUNT               : integer := 2;
      --* Size of each RX DMA buffer in Bytes
      RX_BUFFER_SIZE             : integer := 4096;
      --* Input FrameLink width (only 64 supported now)
      RX_FL_WIDTH                : integer := 64;

      --* Number of TX DMA channels
      TX_IFC_COUNT               : integer := 2;
      --* Size of each TX DMA buffer in Bytes
      TX_BUFFER_SIZE             : integer := 4096;
      --* Output FrameLink width (only 64 supported now)
      TX_FL_WIDTH                : integer := 64;

      -- Generic allowing generation of FL_DISCARD_STAT entity before RX Buffer
      RX_DISCARD_EN              : boolean := true;
      
      -- --------------- Internal Bus Endpoint -----------------------------------
      -- BASE and LIMIT used only if CONNECTED_TO = SWITCH_SLAVE 
      IB_EP_CONNECTED_TO         : t_ib_comp := SWITCH_SLAVE; 
      IB_EP_ENDPOINT_BASE        : std_logic_vector(31 downto 0) := X"02000000"; 
      IB_EP_ENDPOINT_LIMIT       : std_logic_vector(31 downto 0) := X"00300000"; 
      IB_EP_STRICT_ORDER         : boolean := false; 
      IB_EP_DATA_REORDER         : boolean := false; 
      IB_EP_READ_IN_PROCESS      : integer := 1; 
      IB_EP_INPUT_BUFFER_SIZE    : integer := 1; 
      IB_EP_OUTPUT_BUFFER_SIZE   : integer := 1; 

      -- Descriptor manager generics
      --* Base address
      DESC_BASE_ADDR             : std_logic_vector(31 downto 0) := X"02200000";
      --* Number of descriptors downloaded at once 
      --* (Size of descriptor memory for each channel is double than this)
      DESC_BLOCK_SIZE            : integer   := 4
   );
   port (
      -- Common interface
      CLK            : in std_logic;
      RESET          : in std_logic;
      -- RX/TX Interrupts
      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;
      
      -- RX Buffer status signals
      RX_BUFFER_STATUS : out std_logic_vector(RX_IFC_COUNT*log2((RX_BUFFER_SIZE/(RX_FL_WIDTH/8))+1)-1 downto 0);
      RX_BUFFER_FULL   : out std_logic_vector(RX_IFC_COUNT-1 downto 0);
      RX_BUFFER_EMPTY  : out std_logic_vector(RX_IFC_COUNT-1 downto 0);

      -- network interfaces interface
      -- input FrameLink interface
      RX_SOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic_vector(RX_IFC_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(RX_FL_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(RX_FL_WIDTH/8)-1 downto 0); -- TODO: Check
      RX_ADDR        : in  std_logic_vector(abs(log2(RX_IFC_COUNT)-1) downto 0);
      -- output FrameLinks
      TX_SOF_N       : out std_logic_vector(TX_IFC_COUNT-1 downto 0);
      TX_SOP_N       : out std_logic_vector(TX_IFC_COUNT-1 downto 0);
      TX_EOF_N       : out std_logic_vector(TX_IFC_COUNT-1 downto 0);
      TX_EOP_N       : out std_logic_vector(TX_IFC_COUNT-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(TX_IFC_COUNT-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(TX_IFC_COUNT-1 downto 0);
      TX_DATA        : out std_logic_vector((TX_IFC_COUNT*TX_FL_WIDTH)-1 downto 0);
      TX_REM         : out std_logic_vector(TX_IFC_COUNT*log2(TX_FL_WIDTH/8)-1 downto 0); -- TODO: Check
      
      -- Upstream Internal Bus interface
      UP_DATA        : out std_logic_vector(63 downto 0);
      UP_SOF_N       : out std_logic;
      UP_EOF_N       : out std_logic;
      UP_SRC_RDY_N   : out std_logic;
      UP_DST_RDY_N   : in  std_logic;
      
      -- Downstream Internal Bus interface
      DOWN_DATA      : in  std_logic_vector(63 downto 0);
      DOWN_SOF_N     : in  std_logic;
      DOWN_EOF_N     : in  std_logic;
      DOWN_SRC_RDY_N : in  std_logic;
      DOWN_DST_RDY_N : out std_logic;
      
      -- MI32 Interface
      MI32_DWR         : in  std_logic_vector(31 downto 0);
      MI32_ADDR        : in  std_logic_vector(31 downto 0);
      MI32_BE          : in  std_logic_vector(3 downto 0);
      MI32_RD          : in  std_logic;
      MI32_WR          : in  std_logic;
      MI32_DRDY        : out std_logic;
      MI32_ARDY        : out std_logic;
      MI32_DRD         : out std_logic_vector(31 downto 0)        
   );
end entity DMA_MODULE_GEN;

-- -----------------------------------------------------------------------------
--                           Architecture declaration
-- -----------------------------------------------------------------------------
architecture behavioral of DMA_MODULE_GEN is

   -- -----------------------------------------------------------------------
   --                              Functions
   -- -----------------------------------------------------------------------
   -- minzero function returns zero for negative numbers
   -- It's used mainly for ifc or addr signals - if one flow is somewhere set
   -- is possible that vector may have range -1 downto 0 and that is nonsence.
   function minzero(n : integer) return integer is
   begin
      if (n > 0) then 
         return n;
      else 
         return 0;
      end if;
   end minzero;
   
   -- Function max returns greater number from its params.
   function max(a : integer; b : integer) return integer is
   begin
      if (a > b) then
         return a;
      else
         return b;
      end if;
   end max;

   -- Generic decoder function
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

   -- -----------------------------------------------------------------------
   --                              Constants
   -- -----------------------------------------------------------------------
   -- Number of FLOWS for Descriptor Manager - it's found maximum of RX_IFC_COUNT
   -- and TX_IFC_COUNT and multiplied by 2. In desc_enable signal are RX and TX
   -- DMA Controller's enables switching (odds are TX and evens are RX).
   -- Because of non-equality of RX_IFC_COUNT and TX_IFC_COUNT is possible, that
   -- some of these channels are set to '0' by default -> the channel is not used.
   constant DESC_FLOWS        : integer   := 2*max(RX_IFC_COUNT, TX_IFC_COUNT);
	constant UNUSED_ODD			: integer	:= max(RX_IFC_COUNT, TX_IFC_COUNT) - TX_IFC_COUNT;
	constant UNUSED_EVEN			: integer	:= max(RX_IFC_COUNT, TX_IFC_COUNT) - RX_IFC_COUNT;

   constant RX_BLOCK_SIZE     : integer   := RX_BUFFER_SIZE/(RX_FL_WIDTH/8);
   constant TX_BLOCK_SIZE     : integer   := TX_BUFFER_SIZE/(TX_FL_WIDTH/8);
   
   -- DIS_STATUS_WIDTH counts status width generic for each flow for 
   -- FL_DISCARD_STAT component.
   constant DIS_STATUS_WIDTH  : integer   := log2(RX_BLOCK_SIZE+1);
   
   -- Total size of one block for one flow - former generic, now only constant
   constant TX_FLOW_SPACE     : integer   := 2*TX_BUFFER_SIZE;

   constant TX_LOW_ADDR       : integer   := 1+log2(TX_BUFFER_SIZE); 
   -- -----------------------------------------------------------------------
   --                            Types and Subtypes
   -- -----------------------------------------------------------------------
   -- Because of many TX buffers set with FLOWS = 1 is trouble with vectors.
   -- Each TX buffer expects some outputs to be vectors (0 downto 0) and 
   -- because of many TX buffers is needed this type.
   type t_vect_zero is array (0 to TX_IFC_COUNT-1) of std_logic_vector(0 downto 0);
   
   -- Address range which separates from ib_wr_addr appropriate part that
   -- is addressing conrete TX buffer
   subtype TX_BUF_ADDR_RANGE is natural range minzero(log2(TX_IFC_COUNT)-1)+TX_LOW_ADDR downto TX_LOW_ADDR;
   
   -- -----------------------------------------------------------------------
   --                        Signals declarations
   -- -----------------------------------------------------------------------
   -- Signals of connection between FL_DISCARD_STAT and SW_RXBUF_GEN
   signal rx_addr_buf               : std_logic_vector(abs(log2(RX_IFC_COUNT)-1) downto 0);
   signal rx_data_buf               : std_logic_vector(RX_FL_WIDTH-1 downto 0);
   signal rx_drem_buf               : std_logic_vector(log2(RX_FL_WIDTH/8)-1 downto 0); -- TODO: Check
   signal rx_sop_n_buf              : std_logic;
   signal rx_eop_n_buf              : std_logic;
   signal rx_sof_n_buf              : std_logic;
   signal rx_eof_n_buf              : std_logic;
   signal rx_src_rdy_n_buf          : std_logic;
   signal rx_dst_rdy_n_buf          : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   
   -- Status signals of RX buffer
   signal rx_buf_status             : std_logic_vector(RX_IFC_COUNT*log2(RX_BLOCK_SIZE+1)-1 downto 0);
   signal rx_buf_full               : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal rx_buf_empty              : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   
   signal rx_buf_init               : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   
   -- Newlen signals of RX buffer
   signal rx_buf_newlen             : std_logic_vector(15 downto 0);
   signal rx_buf_newlen_ifc         : std_logic_vector(abs(log2(RX_IFC_COUNT)-1) downto 0);
   signal rx_buf_newlen_ifc2        : std_logic_vector(minzero(log2(RX_IFC_COUNT)-1) downto 0);
   signal rx_buf_newlen_dv          : std_logic;
   -- Rellen signals of RX buffer
   signal rx_buf_rellen             : std_logic_vector(15 downto 0);
   signal rx_buf_rellen_ifc         : std_logic_vector(abs(log2(RX_IFC_COUNT)-1) downto 0);
   signal rx_buf_rellen_ifc2        : std_logic_vector(minzero(log2(RX_IFC_COUNT)-1) downto 0);
   signal rx_buf_rellen_dv          : std_logic;
   
   -- Interrupt signals of RX DMA Ctrl
   signal rx_enable                 : std_logic_vector(RX_IFC_COUNT-1 downto 0);
   signal rx_interrupt_sig          : std_logic_vector(1 downto 0);
   signal rx_interrupt_set          : std_logic_vector(63 downto 0);   
   signal rx_interrupt_ifc          : std_logic_vector(log2(RX_IFC_COUNT)-1 downto 0);
   signal rx_interrupt_ifc2         : std_logic_vector(minzero(log2(RX_IFC_COUNT)-1) downto 0);
   -- DMA signals of RX DMA Ctrl
   signal rx_dma_addr               : std_logic_vector(log2(128/32)-1 downto 0);
   signal rx_dma_dout               : std_logic_vector(31 downto 0);
   signal rx_dma_req                : std_logic;
   signal rx_dma_ack                : std_logic;
   signal rx_dma_done               : std_logic;
   -- RX descriptor manager signals
   signal rx_desc_addr              : std_logic_vector(log2(RX_IFC_COUNT)-1 downto 0);
   signal rx_desc_addr2             : std_logic_vector(minzero(log2(RX_IFC_COUNT)-1) downto 0);
   signal rx_desc_addr_mux          : std_logic_vector(minzero(log2(DESC_FLOWS)-1) downto 0);
   signal rx_desc_empty             : std_logic;
   signal rx_desc_empty_mux         : std_logic_vector(0 downto 0);  
   signal rx_desc_read              : std_logic;
   signal rx_desc_dv                : std_logic;
   
   -- TX Buffers and Controller signals
   -- FrameLink and other signals - with type t_vect_zero
   signal tx_sof_n_vect_z           : t_vect_zero;
   signal tx_sop_n_vect_z           : t_vect_zero;
   signal tx_eof_n_vect_z           : t_vect_zero;
   signal tx_eop_n_vect_z           : t_vect_zero;
   signal tx_src_rdy_n_vect_z       : t_vect_zero;
   signal tx_dst_rdy_n_vect_z       : t_vect_zero;
   signal txbuf_newlen_dv_vect_z    : t_vect_zero;
   signal txbuf_newlen_rdy_vect_z   : t_vect_zero;
   signal txbuf_rellen_dv_vect_z    : t_vect_zero;
   
   -- Newlen signals of TX buffers
   signal tx_buf_newlen             : std_logic_vector(15 downto 0);
   signal tx_buf_newlen_ifc         : std_logic_vector(abs(log2(TX_IFC_COUNT)-1) downto 0);
   signal tx_buf_newlen_ifc2        : std_logic_vector(minzero(log2(TX_IFC_COUNT)-1) downto 0);
   signal tx_buf_newlen_dv          : std_logic;

   signal txbuf_newlen_dv           : std_logic_vector(TX_IFC_COUNT-1 downto 0);
   signal txbuf_newlen_rdy          : std_logic_vector(TX_IFC_COUNT-1 downto 0);

   -- Rellen signals of TX buffers
   signal tx_buf_rellen             : std_logic_vector(15 downto 0);
   signal tx_buf_rellen_ifc         : std_logic_vector(abs(log2(TX_IFC_COUNT)-1) downto 0);
   signal tx_buf_rellen_ifc2        : std_logic_vector(minzero(log2(TX_IFC_COUNT)-1) downto 0);
   signal tx_buf_rellen_dv          : std_logic;
   
   signal txbuf_rellen              : std_logic_vector(TX_IFC_COUNT*16-1 downto 0);
   signal txbuf_rellen_dv           : std_logic_vector(TX_IFC_COUNT-1 downto 0);

   -- TX Rellen logic signals
   signal txbuf_rellen_reg          : std_logic_vector(TX_IFC_COUNT*16-1 downto 0);
   signal rellen_wr                 : std_logic_vector(TX_IFC_COUNT*16-1 downto 0);
   signal rellen_reg                : std_logic_vector(TX_IFC_COUNT*16-1 downto 0);
   signal tx_rellen_ifc             : std_logic_vector(abs(log2(TX_IFC_COUNT)-1) downto 0);
   signal rellen_read               : std_logic_vector(TX_IFC_COUNT-1 downto 0);
   signal rellen_read_dec           : std_logic_vector(TX_IFC_COUNT-1 downto 0);
   
   -- Interrupt signals of TX DMA Ctrl
   signal tx_enable                 : std_logic_vector(TX_IFC_COUNT-1 downto 0);
   signal tx_interrupt_sig          : std_logic_vector(1 downto 0);
   signal tx_interrupt_set          : std_logic_vector(63 downto 0);
   signal tx_interrupt_ifc          : std_logic_vector(log2(TX_IFC_COUNT)-1 downto 0);
   signal tx_interrupt_ifc2         : std_logic_vector(minzero(log2(TX_IFC_COUNT)-1) downto 0);

   -- TX Descriptor managers signals
   signal tx_desc_addr              : std_logic_vector(log2(TX_IFC_COUNT)-1 downto 0);
   signal tx_desc_addr2             : std_logic_vector(minzero(log2(TX_IFC_COUNT)-1) downto 0);
   signal tx_desc_addr_mux          : std_logic_vector(minzero(log2(DESC_FLOWS)-1) downto 0);
   signal tx_desc_empty             : std_logic;
   signal tx_desc_empty_mux         : std_logic_vector(0 downto 0);
   signal tx_desc_read              : std_logic;
   signal tx_desc_dv                : std_logic;
   
   -- Signals of TX DMA Ctrl
   signal tx_dma_addr               : std_logic_vector(log2(128/32)-1 downto 0);
   signal tx_dma_dout               : std_logic_vector(31 downto 0);
   signal tx_dma_req                : std_logic;
   signal tx_dma_ack                : std_logic;
   signal tx_dma_done               : std_logic;

   -- Descriptor Manager signals
   signal desc_dma_addr             : std_logic_vector(0 downto 0);
   signal desc_dma_done             : std_logic;
   signal desc_dma_dout             : std_logic_vector(63 downto 0);
   signal desc_dma_ack              : std_logic;
   signal desc_dma_tag              : std_logic_vector(15 downto 0);
   signal desc_dma_req              : std_logic;
   
   signal desc_enable               : std_logic_vector(DESC_FLOWS-1 downto 0);
   signal desc_data                 : std_logic_vector(63 downto 0);
   signal desc_read                 : std_logic;
   signal desc_empty                : std_logic_vector(DESC_FLOWS-1 downto 0);
   signal desc_dvld                 : std_logic;
   signal desc_addr                 : std_logic_vector(log2(DESC_FLOWS)-1 downto 0);
   signal desc_pipe_en              : std_logic;
   -- Descriptor manager sharing signals
   signal rx_tx_desc                : std_logic;
   signal rs_desc_read              : std_logic_vector(1 downto 0);
   signal rs_desc_read_set          : std_logic_vector(1 downto 0);
   signal rs_desc_read_reset        : std_logic_vector(1 downto 0);
      
   -- Internal Bus signals
   -- Write
   signal ib_wr_addr                : std_logic_vector(31 downto 0);
   signal ib_wr_data                : std_logic_vector(63 downto 0);
   signal ib_wr_be                  : std_logic_vector(7 downto 0);
   signal ib_wr_req                 : std_logic;
   signal ib_wr_rdy                 : std_logic;
   signal ib_wr_length              : std_logic_vector(11 downto 0);
   signal ib_wr_sof                 : std_logic;
   signal ib_wr_eof                 : std_logic;
   -- Registered Write
   signal reg_ib_wr_addr            : std_logic_vector(31 downto 0);
   signal reg_ib_wr_data            : std_logic_vector(63 downto 0);
   signal reg_ib_wr_be              : std_logic_vector(7 downto 0);
   signal reg_ib_wr_req             : std_logic;
   -- Read input
   signal ib_rd_addr                : std_logic_vector(31 downto 0);
   signal ib_rd_be                  : std_logic_vector(7 downto 0);
   signal ib_rd_req                 : std_logic;
   signal ib_rd_ardy                : std_logic;
   signal ib_rd_sof                 : std_logic;
   signal ib_rd_eof                 : std_logic;
   -- Read output
   signal ib_rd_data                : std_logic_vector(63 downto 0);
   signal ib_rd_src_rdy             : std_logic;
   signal ib_rd_dst_rdy             : std_logic;
   -- Busmaster interface input
   signal ib_bm_global_addr         : std_logic_vector(63 downto 0);
   signal ib_bm_local_addr          : std_logic_vector(31 downto 0);
   signal ib_bm_length              : std_logic_vector(11 downto 0);
   signal ib_bm_tag                 : std_logic_vector(7 downto 0);
   signal ib_bm_trans_type          : std_logic_vector(1 downto 0);
   signal ib_bm_req                 : std_logic;
   signal ib_bm_ack                 : std_logic;
   -- Busmaster interface output
   signal ib_bm_op_tag              : std_logic_vector(7 downto 0);
   signal ib_bm_op_done             : std_logic;

   -- Internal Bus busmaster interface (serial gics format, bm_converter <-> endpoint)
   signal ib_epbm_data      : std_logic_vector(63 downto 0);
   signal ib_epbm_sof_n     : std_logic;
   signal ib_epbm_eof_n     : std_logic;
   signal ib_epbm_src_rdy_n : std_logic;
   signal ib_epbm_dst_rdy_n : std_logic;
   
   signal ib_epbm_tag       : std_logic_vector(7 downto 0);
   signal ib_epbm_tag_vld   : std_logic;


   -- Internal Bus control signals
   signal ib_rxbuf_rd_sel           : std_logic;
   signal ib_rxbuf_rd_req           : std_logic;
   signal ib_rxbuf_rd_ardy          : std_logic;
   signal ib_rxbuf_rd_data          : std_logic_vector(63 downto 0);
   signal ib_rxbuf_rd_src_rdy       : std_logic;
   
   signal ib_txbuf_wr               : std_logic_vector(TX_IFC_COUNT-1 downto 0);
   signal ib_txbuf_wr_req           : std_logic_vector(TX_IFC_COUNT-1 downto 0);
   signal ib_txbuf_wr_rdy           : std_logic_vector(TX_IFC_COUNT-1 downto 0);
   signal ib_txbuf_wr_sel           : std_logic;

   signal ib_txbuf_wr_rdy_mx        : std_logic_vector(0 downto 0);
   signal ib_txbuf_wr_rdy_addr      : std_logic_vector(minzero(log2(TX_IFC_COUNT)-1) downto 0);
   
   signal ib_rxcontrol_rd_sel       : std_logic;
   signal ib_txcontrol_rd_sel       : std_logic;
   signal ib_rxcontrol_rd_req       : std_logic;
   signal ib_txcontrol_rd_req       : std_logic;
   signal ib_txcontrol_rd_data      : std_logic_vector(63 downto 0);
   signal ib_rxcontrol_rd_data      : std_logic_vector(63 downto 0);
   signal ib_rxcontrol_rd_ardy      : std_logic;
   signal ib_txcontrol_rd_ardy      : std_logic;
   
   signal ib_rd_addr_buf            : std_logic_vector(31 downto 0);
   signal ib_rd_ardy_buf            : std_logic;
   
   signal ib_wr_addr_buf            : std_logic_vector(31 downto 0);

   signal ib_desc_wr_req            : std_logic;
   signal ib_desc_wr_sel            : std_logic;
   signal ib_desc_wr_rdy            : std_logic;
   
   signal ib_desc_rd_sel            : std_logic;

   signal reg_rd_addr               : std_logic_vector(31 downto 0);

   signal reg_ib_rxc_rd_src_rdy     : std_logic;
   signal reg_ib_txc_rd_src_rdy     : std_logic;
   
   signal reg_mx_control            : std_logic_vector(63 downto 0);
   signal reg_control               : std_logic_vector(63 downto 0);

   -- Data interface between DMA controllers and mfifo
   signal dma_tx_src_rdy_n          : std_logic_vector(1 downto 0);
   signal dma_tx_dst_rdy_n          : std_logic_vector(1 downto 0);
   signal dma_tx_src_rdy            : std_logic_vector(1 downto 0);
   signal dma_tx_dst_rdy            : std_logic_vector(1 downto 0);
   signal dma_tx_data               : std_logic_vector(2*32-1 downto 0);
   
   -- Data2BM signals
   signal data2bm_dma_done          : std_logic;
   signal data2bm_dma_tag           : std_logic_vector(15 downto 0);
   signal data2bm_rx_src_rdy_n      : std_logic;
   signal data2bm_rx_dst_rdy_n      : std_logic;

   -- Output from dma2data connected to descriptor
   signal desc_tx_src_rdy_n         : std_logic;
   signal desc_tx_dst_rdy_n         : std_logic;
   signal desc_tx_data              : std_logic_vector(63 downto 0);

   -- Multififo 1 outputs
   signal mfifo1_data_out           : std_logic_vector(63 downto 0);
   signal mfifo1_read               : std_logic;
   signal mfifo1_empty              : std_logic_vector(1 downto 0);
   signal mfifo1_data_vld           : std_logic;
   signal mfifo1_block_addr         : std_logic_vector(0 downto 0);
   signal mfifo1_word_transmission  : std_logic;

   -- Multififo 2 outputs
   signal mfifo2_full               : std_logic_vector(1 downto 0);
   signal mfifo2_data_out           : std_logic_vector(2*64-1 downto 0);
   signal mfifo2_data_vld           : std_logic;
   signal mfifo2_read               : std_logic;
   signal mfifo2_data_in            : std_logic_vector(2*64-1 downto 0);
   signal mfifo2_write              : std_logic_vector(1 downto 0);
   signal mfifo2_empty              : std_logic_vector(1 downto 0);
   signal mfifo2_block_addr         : std_logic_vector(0 downto 0);
   signal mfifo2_block_addr_ce      : std_logic;

   -- Multififo 1 data transmission logic
   signal cnt_mfifo1_words_ce       : std_logic;
   signal cnt_block_addr_ce         : std_logic;
   signal cnt_mfifo1_words          : std_logic;
   
   -- MI32 discard signals
   signal dis_mi_dwr                : std_logic_vector(31 downto 0);
   signal dis_mi_be                 : std_logic_vector(3 downto 0);
   signal dis_mi_addr               : std_logic_vector(31 downto 0);
   signal dis_mi_drd                : std_logic_vector(31 downto 0);
   signal dis_mi_ardy               : std_logic;
   signal dis_mi_drdy               : std_logic;
   signal dis_mi_rd                 : std_logic;
   signal dis_mi_wr                 : std_logic;
   -- MI32 buffers signals - from first MI SPLITTER
   signal buf_mi_dwr                : std_logic_vector(31 downto 0);
   signal buf_mi_be                 : std_logic_vector(3 downto 0);
   signal buf_mi_addr               : std_logic_vector(31 downto 0);
   signal buf_mi_drd                : std_logic_vector(31 downto 0);
   signal buf_mi_ardy               : std_logic;
   signal buf_mi_drdy               : std_logic;
   signal buf_mi_rd                 : std_logic;
   signal buf_mi_wr                 : std_logic;
   -- MI32 RX DMA Ctrl signals
   signal rx_mi_dwr                : std_logic_vector(31 downto 0);
   signal rx_mi_be                 : std_logic_vector(3 downto 0);
   signal rx_mi_addr               : std_logic_vector(31 downto 0);
   signal rx_mi_drd                : std_logic_vector(31 downto 0);
   signal rx_mi_ardy               : std_logic;
   signal rx_mi_drdy               : std_logic;
   signal rx_mi_rd                 : std_logic;
   signal rx_mi_wr                 : std_logic;
   -- Pipelined
   signal rx_mi_dwr_pipe           : std_logic_vector(31 downto 0);
   signal rx_mi_be_pipe            : std_logic_vector(3 downto 0);
   signal rx_mi_addr_pipe          : std_logic_vector(31 downto 0);
   signal rx_mi_drd_pipe           : std_logic_vector(31 downto 0);
   signal rx_mi_ardy_pipe          : std_logic;
   signal rx_mi_drdy_pipe          : std_logic;
   signal rx_mi_rd_pipe            : std_logic;
   signal rx_mi_wr_pipe            : std_logic;
   -- MI32 TX DMA Ctrl signals
   signal tx_mi_dwr                : std_logic_vector(31 downto 0);
   signal tx_mi_be                 : std_logic_vector(3 downto 0);
   signal tx_mi_addr               : std_logic_vector(31 downto 0);
   signal tx_mi_drd                : std_logic_vector(31 downto 0);
   signal tx_mi_ardy               : std_logic;
   signal tx_mi_drdy               : std_logic;
   signal tx_mi_rd                 : std_logic;
   signal tx_mi_wr                 : std_logic;
   -- Signals between IB, DATA2BM and TAG_SEQUENCER
   signal bm_tag                    : std_logic_vector(15 downto 0);
   signal bm_trans_type             : std_logic_vector(1 downto 0);
   signal bm_req                    : std_logic;
   signal bm_ack                    : std_logic;
   
   signal bm_op_tag                 : std_logic_vector(15 downto 0);
   signal bm_op_done                : std_logic;

   -- Pipe signals between Tag sequencer and IB Endpoint
   signal data_out_tag_pipe         : std_logic_vector(117 downto 0); -- (8+2)+12+32+64 = 118
   signal data_in_tag_pipe          : std_logic_vector(117 downto 0);
   
   signal ib_bm_req_pipe            : std_logic;
   signal ib_bm_ack_pipe            : std_logic;
   signal ib_bm_ack_pipe2           : std_logic;
   signal ib_bm_trans_type_pipe     : std_logic_vector(1 downto 0);
   signal ib_bm_tag_pipe            : std_logic_vector(7 downto 0);

   signal ib_bm_global_addr_pipe    : std_logic_vector(63 downto 0);
   signal ib_bm_local_addr_pipe     : std_logic_vector(31 downto 0);
   signal ib_bm_length_pipe         : std_logic_vector(11 downto 0);

   signal zeros                     : std_logic_vector(log2(DESC_FLOWS)-1 downto 0);

begin

assert (not (RX_DISCARD_EN = true and RX_IFC_COUNT = 1))
report "Can't be enabled FL_DISCARD_STAT entity when RX_IFC_COUNT = 1!"
severity ERROR;

assert (2**(log2(RX_BUFFER_SIZE)) = RX_BUFFER_SIZE)
report "RX_BUFFER_SIZE must be power of 2!"
severity ERROR;

assert (2**(log2(TX_BUFFER_SIZE)) = TX_BUFFER_SIZE)
report "TX_BUFFER_SIZE must be power of 2!"
severity ERROR;

assert (RX_FL_WIDTH = 64)
report "Currently supported only 64bit FrameLink"
severity ERROR;

assert (TX_FL_WIDTH = 64)
report "Currently supported only 64bit FrameLink"
severity ERROR;

assert (2**(log2(RX_IFC_COUNT)) = RX_IFC_COUNT)
report "RX_IFC_COUNT must be power of 2!"
severity ERROR;

assert (2**(log2(TX_IFC_COUNT)) = TX_IFC_COUNT)
report "TX_IFC_COUNT must be power of 2!"
severity ERROR;

   -- IFC signals mapping for many flows - it's needed because of one flow and problem
   -- with log2 function (its possible to create -1 downto 0 vector)
   GEN_IFC_MORE_FLOWS_RX: if RX_IFC_COUNT > 1 generate
   
      rx_buf_newlen_ifc2   <= rx_buf_newlen_ifc;
      rx_buf_rellen_ifc    <= rx_buf_rellen_ifc2;
      
      rx_interrupt_ifc     <= rx_interrupt_ifc2;
      
      rx_desc_addr         <= rx_desc_addr2;
   
   end generate;
   
   GEN_IFC_MORE_FLOWS_TX: if TX_IFC_COUNT > 1 generate
   
      tx_buf_newlen_ifc    <= tx_buf_newlen_ifc2;
      tx_buf_rellen_ifc2   <= tx_buf_rellen_ifc;
 
      tx_interrupt_ifc     <= tx_interrupt_ifc2;

      tx_desc_addr         <= tx_desc_addr2;
   
   end generate;

   GEN_IFC_ONE_FLOW_RX: if RX_IFC_COUNT = 1 generate
   
      rx_buf_newlen_ifc2 <= "0";
      rx_buf_rellen_ifc <= (others => '0');
   
   end generate;

   GEN_IFC_ONE_FLOW_TX: if TX_IFC_COUNT = 1 generate
      tx_buf_rellen_ifc2 <= "0";
   end generate;

   -- -----------------------------------------------------------------------
   --                           MI32 Connections
   -- -----------------------------------------------------------------------
   -- Address space:
   -- To 0x2000 (excluding) is address space of RX/TX DMA Controllers
   -- For example:
   -- 0x0000 - RX Controller - buffer 0
   -- 0x0040 - TX Controller - buffer 0
   -- 0x0080 - RX Controller - buffer 1
   -- 0x00C0 - TX Controller - buffer 1
   -- ...
   -- From 0x2000 (including) is address space of others components - in this 
   -- case FL_DISCARD_STAT only
   
   -- first MI SPLITTER - switching MI32 according to bit no.13 of MI_ADDR -
   -- when '0' - MI for DMA Ctrls - signals are used as input of second MI 
   --            SPLITTER
   -- when '1' - MI for FL_DISCARD_STAT entity
   GEN_MI_FL_DISCARD: if RX_DISCARD_EN = true generate
   
      MI_SPLITTER_BUF_DIS_I : entity work.mi_splitter_addr32
         generic map (
            -- Number of output interfaces
            ITEMS       => 2,
            -- New address width - upper bits will be filled with zeros
            ADDR_WIDTH  => 13,
            -- MI Data width
            DATA_WIDTH  => 32,
            -- Pipe enable
            PIPE        => true
         )
         port map (
            -- Common interface
            CLK         => CLK,
            RESET       => RESET,
            -- Input MI32
            IN_DWR      => MI32_DWR,
            IN_ADDR     => MI32_ADDR(13 downto 0),
            IN_BE       => MI32_BE,
            IN_RD       => MI32_RD,
            IN_WR       => MI32_WR,
            IN_ARDY     => MI32_ARDY,
            IN_DRD      => MI32_DRD,
            IN_DRDY     => MI32_DRDY,
            -- Output MI32
            OUT_DWR(31 downto 0)    => buf_mi_dwr,         
            OUT_DWR(63 downto 32)   => dis_mi_dwr,
            OUT_ADDR(31 downto 0)   => buf_mi_addr,
            OUT_ADDR(63 downto 32)  => dis_mi_addr,
            OUT_RD(0)               => buf_mi_rd,
            OUT_RD(1)               => dis_mi_rd,
            OUT_WR(0)               => buf_mi_wr,
            OUT_WR(1)               => dis_mi_wr,
            OUT_ARDY(0)             => buf_mi_ardy,
            OUT_ARDY(1)             => dis_mi_ardy,
            OUT_BE(3 downto 0)      => buf_mi_be,
            OUT_BE(7 downto 4)      => dis_mi_be,
            OUT_DRD(31 downto 0)    => buf_mi_drd,
            OUT_DRD(63 downto 32)   => dis_mi_drd,
            OUT_DRDY(0)             => buf_mi_drdy,
            OUT_DRDY(1)             => dis_mi_drdy
         );
   
   end generate;
   
   GEN_NOT_MI_FL_DISCARD: if RX_DISCARD_EN = false generate
   
      buf_mi_addr <= MI32_ADDR;
      buf_mi_be   <= MI32_BE;
      buf_mi_dwr  <= MI32_DWR;
      buf_mi_rd   <= MI32_RD;
      buf_mi_wr   <= MI32_WR;
      MI32_ARDY     <= buf_mi_ardy;
      MI32_DRD      <= buf_mi_drd;
      MI32_DRDY     <= buf_mi_drdy;
   
   end generate;
   
   -- second MI SPLITTER - switching MI32 according to bit no.6 of buf_mi_addr
   -- when '0' - MI for RX DMA Ctrl
   -- when '1' - MI for TX DMA Ctrl
   -- ATTENTION, please! This MI SPLITTER can NOT have latency, 'cause DMA Ctrls
   -- need whole non-cut address. 
   MI_SPLITTER_RX_TX_I : entity work.mi_splitter_addr32
      generic map (
         -- Number of output interfaces
         ITEMS       => 2,
         -- new Address width - bits up to 32 are filled with zeros
         ADDR_WIDTH  => 6,
         -- MI Data width
         DATA_WIDTH  => 32,
         -- Pipe enable - here MUST be false!! rx_ and tx_mi_addr is not used -
         -- buf_mi_addr is used instead.
         PIPE        => false -- DO NOT CHANGE!!!
      )
      port map (
         -- Common interface
         CLK      => CLK,
         RESET    => RESET,
         -- Input MI32
         IN_DWR   => buf_mi_dwr,
         IN_ADDR  => buf_mi_addr(6 downto 0),
         IN_BE    => buf_mi_be,
         IN_RD    => buf_mi_rd,
         IN_WR    => buf_mi_wr,
         IN_ARDY  => buf_mi_ardy,
         IN_DRD   => buf_mi_drd,
         IN_DRDY  => buf_mi_drdy,
         -- Output MI32
         OUT_DWR(31 downto 0)    => rx_mi_dwr,         
         OUT_DWR(63 downto 32)   => tx_mi_dwr,
         OUT_ADDR(31 downto 0)   => rx_mi_addr,
         OUT_ADDR(63 downto 32)  => tx_mi_addr,
         OUT_RD(0)               => rx_mi_rd,
         OUT_RD(1)               => tx_mi_rd,
         OUT_WR(0)               => rx_mi_wr,
         OUT_WR(1)               => tx_mi_wr,
         OUT_ARDY(0)             => rx_mi_ardy,
         OUT_ARDY(1)             => tx_mi_ardy,
         OUT_BE(3 downto 0)      => rx_mi_be,
         OUT_BE(7 downto 4)      => tx_mi_be,
         OUT_DRD(31 downto 0)    => rx_mi_drd,
         OUT_DRD(63 downto 32)   => tx_mi_drd,
         OUT_DRDY(0)             => rx_mi_drdy,
         OUT_DRDY(1)             => tx_mi_drdy
      );

   rx_mi_pipe_i : entity work.MI_PIPE
   generic map(
      DATA_WIDTH  => 32,
      ADDR_WIDTH  => 32,
      USE_OUTREG  => true,
      FAKE_PIPE   => false
   )
   port map(
      -- Common interface
      CLK         => CLK,
      RESET       => RESET,
      
      -- Input MI interface
      IN_DWR      => rx_mi_dwr,
      IN_ADDR     => buf_mi_addr,
      IN_BE       => rx_mi_be,
      IN_RD       => rx_mi_rd,
      IN_WR       => rx_mi_wr,
      IN_ARDY     => rx_mi_ardy,
      IN_DRD      => rx_mi_drd,
      IN_DRDY     => rx_mi_drdy,
      
      -- Output MI interface
      OUT_DWR     => rx_mi_dwr_pipe,
      OUT_ADDR    => rx_mi_addr_pipe,
      OUT_BE      => rx_mi_be_pipe,
      OUT_RD      => rx_mi_rd_pipe,
      OUT_WR      => rx_mi_wr_pipe,
      OUT_ARDY    => rx_mi_ardy_pipe,
      OUT_DRD     => rx_mi_drd_pipe,
      OUT_DRDY    => rx_mi_drdy_pipe
   );

   -- -----------------------------------------------------------------------
   --                                    RX
   -- -----------------------------------------------------------------------
   -- ------------------------------------------
   --         RX DMA Controller instance
   -- ------------------------------------------
   RX_DMA_CTRL_I : entity work.rx_dma_ctrl_arch
      port map (
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         -- Newlen output interface
         BUF_NEWLEN     => rx_buf_newlen,
         BUF_NEWLEN_DV  => rx_buf_newlen_dv,
         BUF_NEWLEN_IFC => rx_buf_newlen_ifc2,
         -- Rellen input interface
         BUF_RELLEN     => rx_buf_rellen,
         BUF_RELLEN_DV  => rx_buf_rellen_dv,
         BUF_RELLEN_IFC => rx_buf_rellen_ifc2,
         -- Descriptor manager interface
         DESC_DATA      => desc_data,
         DESC_EMPTY     => rx_desc_empty,
         DESC_IFC       => rx_desc_addr2,
         DESC_READ      => rx_desc_read,
         DESC_DV        => rx_desc_dv,
         -- DMA interface
         DMA_ADDR       => rx_dma_addr,
         DMA_DOUT       => rx_dma_dout,
         DMA_REQ        => rx_dma_req,
         DMA_ACK        => rx_dma_ack,
         DMA_DONE       => rx_dma_done,
         -- Interrupts
         ENABLE         => rx_enable,
         INTERRUPT      => rx_interrupt_sig,
         INTERRUPT_IFC  => rx_interrupt_ifc2,
         -- MI interface
         SW_ADDR        => rx_mi_addr_pipe,
         SW_ARDY        => rx_mi_ardy_pipe,
         SW_BE          => rx_mi_be_pipe,
         SW_DRD         => rx_mi_drd_pipe,
         SW_DRDY        => rx_mi_drdy_pipe,
         SW_DWR         => rx_mi_dwr_pipe,
         SW_RD          => rx_mi_rd_pipe,
         SW_WR          => rx_mi_wr_pipe
      );

   -- -----------------------------------------------
   --                   FL_DISCARD
   -- -----------------------------------------------
   -- FL_DISCARD_STAT is needed when flows > 1 and on input is not
   -- FL_MULTIPLEXER entity.
   -- It prevents stopping sending on all channels when only one buffer is full
   -- - it drops packets.
   GEN_FL_DISCARD: if RX_DISCARD_EN = true generate
   
      FL_DISCARD_STAT_I : entity work.FL_DISCARD_STAT
         generic map (
            -- Input data width
            DATA_WIDTH     => 64,
            -- Number of flows
            CHANNELS       => RX_IFC_COUNT,
            -- Width of status signal for one flow
            STATUS_WIDTH   => DIS_STATUS_WIDTH,
            -- Width of statistic counters
            CNT_WIDTH      => 64,
            -- counting number of droped/passed packets 
            COUNT_DROP     => true,
            COUNT_PASS     => false,
            -- counting total length of droped/passed packets
            COUNT_DROP_LEN => true,
            COUNT_PASS_LEN => false,
            -- Generate output register on FrameLink
            -- (It's possible because on output framelink is not used dst_rdy_n
            -- signal)
            OUTPUT_REG     => true
         )
         port map (
            -- Common interface
            CLK            => CLK,
            RESET          => RESET,
            -- Input FrameLink interface
            RX_DATA        => RX_DATA,
            RX_DREM        => RX_REM,
            RX_SRC_RDY_N   => RX_SRC_RDY_N,
            RX_DST_RDY_N   => RX_DST_RDY_N,
            RX_SOP_N       => RX_SOP_N,
            RX_EOP_N       => RX_EOP_N,
            RX_SOF_N       => RX_SOF_N,
            RX_EOF_N       => RX_EOF_N,
            RX_CHAN        => RX_ADDR,
            -- Output FrameLink interface - to RX buffer
            TX_DATA        => rx_data_buf,
            TX_DREM        => rx_drem_buf,
            TX_SRC_RDY_N   => rx_src_rdy_n_buf,
            TX_SOP_N       => rx_sop_n_buf,
            TX_EOP_N       => rx_eop_n_buf,
            TX_SOF_N       => rx_sof_n_buf, 
            TX_EOF_N       => rx_eof_n_buf,
            TX_CHAN        => rx_addr_buf,
            -- Status signal of RX buffer
            STATUS         => rx_buf_status,
            -- MI32 interface
            MI_DWR         => dis_mi_dwr,
            MI_ADDR        => dis_mi_addr,
            MI_BE          => dis_mi_be,
            MI_RD          => dis_mi_rd,
            MI_WR          => dis_mi_wr,
            MI_DRDY        => dis_mi_drdy,
            MI_ARDY        => dis_mi_ardy,
            MI_DRD         => dis_mi_drd
         );
   
   end generate;

   -- FL_DISCARD_STAT is not instantiated
   GEN_NOT_FL_DISCARD: if RX_DISCARD_EN = false generate
   
      rx_data_buf       <= RX_DATA;
      rx_drem_buf       <= RX_REM;
      rx_src_rdy_n_buf  <= RX_SRC_RDY_N;
      RX_DST_RDY_N      <= rx_dst_rdy_n_buf;
      rx_sop_n_buf      <= RX_SOP_N;
      rx_sof_n_buf      <= RX_SOF_N;
      rx_eop_n_buf      <= RX_EOP_N;
      rx_eof_n_buf      <= RX_EOF_N;
      rx_addr_buf       <= RX_ADDR;
      
      dis_mi_drd  <= (others => 'X');
      dis_mi_drdy <= '0';
      dis_mi_ardy <= '0';
   
   end generate;

   -- --------------------------------------------
   --                  RX Buffer
   -- --------------------------------------------
   rx_buf_init <= (others => '0'); -- init signal of rx buffer
   
   RXBUF_I : entity work.SW_RXBUF_GEN
      generic map (
         -- Input data width
         DATA_WIDTH  => RX_FL_WIDTH,
         -- Block size
         BLOCK_SIZE  => RX_BLOCK_SIZE,
         -- Number of flows
         FLOWS       => RX_IFC_COUNT
      )
      port map (
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         INIT           => rx_buf_init,
         -- Status signals
         STATUS         => rx_buf_status,
         FULL           => rx_buf_full,
         EMPTY          => rx_buf_empty,
         -- Input "multiplexed" FrameLink
         RX_ADDR        => rx_addr_buf,
         RX_DATA        => rx_data_buf,
         RX_SOP_N       => rx_sop_n_buf,
         RX_EOP_N       => rx_eop_n_buf,
         RX_SOF_N       => rx_sof_n_buf,
         RX_EOF_N       => rx_eof_n_buf,
         RX_REM         => rx_drem_buf,
         RX_SRC_RDY_N   => rx_src_rdy_n_buf,
         RX_DST_RDY_N   => rx_dst_rdy_n_buf,
         -- Receive Buffer Interface
         BUF_NEWLEN     => rx_buf_newlen,
         BUF_NEWLEN_DV  => rx_buf_newlen_dv,
         BUF_NEWLEN_IFC => rx_buf_newlen_ifc,
         BUF_RELLEN     => rx_buf_rellen,
         BUF_RELLEN_DV  => rx_buf_rellen_dv,
         BUF_RELLEN_IFC => rx_buf_rellen_ifc,
         -- Memory read interface
         RD_ADDR        => ib_rd_addr_buf,
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxbuf_rd_req,
         RD_ARDY        => ib_rxbuf_rd_ardy,      
         RD_DATA        => ib_rxbuf_rd_data,
         RD_SRC_RDY     => ib_rxbuf_rd_src_rdy,
         RD_DST_RDY     => ib_rd_dst_rdy
      );

   -- mapping output interface - STATUS signals
   -- this is needed, when on input are not HFE like things
   -- User maybe needed to know status signals of RX Buffer
   -- when FL_DISCARD_STAT entity is not instantiated
   RX_BUFFER_STATUS  <= rx_buf_status;
   RX_BUFFER_FULL    <= rx_buf_full;
   RX_BUFFER_EMPTY   <= rx_buf_empty;

   -- -----------------------------------------------
   --           RX DMA Status register
   -- -----------------------------------------------
   RX_DMA_STATUS_REG_I : entity work.DMA_STATUS_REG
      port map (
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- Internal Bus interface
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxcontrol_rd_req,
         RD_DATA        => ib_rxcontrol_rd_data,
         -- DMA Controller interface
         SET_INTERRUPT  => rx_interrupt_set
      );
      
   -- ------------------------------------------------
   --   RX connections
   -- ------------------------------------------------
   -- sending rx_enable signal to appropriate possitions in desc_enable signal
   GEN_RX_DESC_EN: for i in 0 to (DESC_FLOWS/2)-1 generate
   
      GEN_RX_DESC_IF: if (i < RX_IFC_COUNT) generate
         desc_enable(i*2) <= rx_enable(i);
      end generate;
      
      -- this situation shall appear when TX_IFC_COUNT is greater than
      -- RX_IFC_COUNT
      GEN_RX_DESC_ELSE: if (i >= RX_IFC_COUNT) generate
         desc_enable(i*2) <= '0';
      end generate;
   
   end generate; 

   -- rx_desc_empty MUX
   rx_desc_addr_mux  <= zeros(log2(DESC_FLOWS)-1 downto log2(2*RX_IFC_COUNT)) & rx_desc_addr & '0';
   rx_desc_empty     <= rx_desc_empty_mux(0);

   RX_DESC_EMPTY_MUX_I : entity work.GEN_MUX
      generic map (
         -- Data width of input interface
         DATA_WIDTH  => 1,
         -- Number of outputs
         MUX_WIDTH   => DESC_FLOWS
      )
      port map (
         DATA_IN     => desc_empty,
         SEL         => rx_desc_addr_mux,
         DATA_OUT    => rx_desc_empty_mux
      );
   
   -- RX Interrupts
   RX_INTERRUPT <= rx_interrupt_sig(0) or rx_interrupt_sig(1);
   
   -- RX Interrupt set vector
   -- It's stored in RX DMA status register
   rx_interrupt_p : process(rx_interrupt_sig, rx_interrupt_ifc)
   begin
   
      rx_interrupt_set <= (others => '0');

      if (rx_interrupt_sig(0) = '1') then
         rx_interrupt_set(2*RX_IFC_COUNT-1 downto 0) <= (decode(rx_interrupt_ifc & '0'));
      elsif (rx_interrupt_sig(1) = '1') then
         rx_interrupt_set(2*RX_IFC_COUNT-1 downto 0) <= (decode(rx_interrupt_ifc & '1'));
      else
         rx_interrupt_set <= (others => '0');
      end if;
   end process;

   -- --------------------------------------------------------------------------
   --                                    TX
   -- --------------------------------------------------------------------------
   -- -----------------------------------------------
   --           TX DMA Controller instance
   -- -----------------------------------------------
   TX_DMA_CTRL_I : entity work.tx_dma_ctrl_arch
      port map (
         -- Common interface
         PIN_CLK        => CLK,
         PIN_RESET      => RESET,
         -- Newlen input interface
         BUF_NEWLEN     => tx_buf_newlen,
         BUF_NEWLEN_DV  => tx_buf_newlen_dv,
         BUF_NEWLEN_IFC => tx_buf_newlen_ifc2,
         -- Rellen output interface
         BUF_RELLEN     => tx_buf_rellen,
         BUF_RELLEN_DV  => tx_buf_rellen_dv,
         BUF_RELLEN_IFC => tx_buf_rellen_ifc2,
         -- Descriptor manager interface
         DESC_DATA      => desc_data,
         DESC_EMPTY     => tx_desc_empty,
         DESC_IFC       => tx_desc_addr2,
         DESC_READ      => tx_desc_read,
         DESC_DV        => tx_desc_dv,
         -- DMA interface
         DMA_ADDR       => tx_dma_addr,
         DMA_DOUT       => tx_dma_dout,
         DMA_REQ        => tx_dma_req,
         DMA_ACK        => tx_dma_ack,
         DMA_DONE       => tx_dma_done,
         -- Interrupts interface
         ENABLE         => tx_enable,
         INTERRUPT      => tx_interrupt_sig,
         INTERRUPT_IFC  => tx_interrupt_ifc2,
         -- MI interface
         SW_ADDR        => buf_mi_addr,
         SW_ARDY        => tx_mi_ardy,
         SW_BE          => tx_mi_be,
         SW_DRD         => tx_mi_drd,
         SW_DRDY        => tx_mi_drdy,
         SW_DWR         => tx_mi_dwr,
         SW_RD          => tx_mi_rd,
         SW_WR          => tx_mi_wr
      );

   -- -----------------------------------------------
   --                  TX Buffers
   -- -----------------------------------------------
   -- Note: If it's everything alright, TX_NEWLEN_RDY signal is always in '1',
   -- but this signal is not used in this module.
   TXBUF_BLOCK_GEN: for j in 0 to TX_IFC_COUNT-1 generate
      
      -- TX Buffers - for each flow one buffer
      TXBUF_I : entity work.SW_TXBUF_TOP
         generic map (
            -- Data width
            DATA_WIDTH        => TX_FL_WIDTH,
            -- Size of block for one flow
            BLOCK_SIZE        => TX_BLOCK_SIZE,
            -- Number of flows
            FLOWS             => 1,
            -- Total Flow size generic
            TOTAL_FLOW_SIZE   => TX_FLOW_SPACE
         )
         port map (
            -- Common interface
            CLK               => CLK,
            RESET             => RESET,
            -- Output interface - FrameLink
            TX_SOF_N          => tx_sof_n_vect_z(j),
            TX_SOP_N          => tx_sop_n_vect_z(j),
            TX_EOP_N          => tx_eop_n_vect_z(j),
            TX_EOF_N          => tx_eof_n_vect_z(j),
            TX_SRC_RDY_N      => tx_src_rdy_n_vect_z(j),
            TX_DST_RDY_N      => tx_dst_rdy_n_vect_z(j),
            TX_DATA           => TX_DATA((j+1)*64-1 downto j*64),
            TX_REM            => TX_REM((j+1)*log2(64/8)-1 downto j*log2(64/8)),
            -- Input write memory interface
            WR_ADDR           => ib_wr_addr_buf,
            WR_DATA           => reg_ib_wr_data,
            WR_BE             => reg_ib_wr_be,
            WR_REQ            => ib_txbuf_wr_req(j),
            WR_RDY            => ib_txbuf_wr_rdy(j),
            -- DMA NEWLEN and RELLEN interface
            TX_NEWLEN         => tx_buf_newlen,
            TX_NEWLEN_DV      => txbuf_newlen_dv_vect_z(j),
            TX_NEWLEN_RDY     => txbuf_newlen_rdy_vect_z(j),
            TX_RELLEN         => txbuf_rellen((j+1)*16-1 downto j*16),
            TX_RELLEN_DV      => txbuf_rellen_dv_vect_z(j)
         );

      -- Output TX interface mapping
      TX_SOF_N(j) <= tx_sof_n_vect_z(j)(0);
      TX_SOP_N(j) <= tx_sop_n_vect_z(j)(0);
      TX_EOF_N(j) <= tx_eof_n_vect_z(j)(0);
      TX_EOP_N(j) <= tx_eop_n_vect_z(j)(0);
      TX_SRC_RDY_N(j) <= tx_src_rdy_n_vect_z(j)(0);
      tx_dst_rdy_n_vect_z(j)(0) <= TX_DST_RDY_N(j); 

      txbuf_rellen_dv(j)   <= txbuf_rellen_dv_vect_z(j)(0);
      txbuf_newlen_rdy(j)  <= txbuf_newlen_rdy_vect_z(j)(0);
      txbuf_newlen_dv_vect_z(j)(0) <= txbuf_newlen_dv(j);
   
   end generate;
   
   -- -------------------------------------------------
   --             TX DMA Status register
   -- -------------------------------------------------
   TX_DMA_STATUS_REG_I : entity work.DMA_STATUS_REG
      port map (
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- Internal Bus interface
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_txcontrol_rd_req,
         RD_DATA        => ib_txcontrol_rd_data,
         -- DMA Controller interface
         SET_INTERRUPT  => tx_interrupt_set
      );
      
   -- -------------------------------------------------
   -- connections of rellen and newlen signals between
   -- TX buffers and TX DMA controller
   -- -------------------------------------------------
   GEN_TX_NEWLEN_DEMUX_MORE_FLOWS: if TX_IFC_COUNT > 1 generate 
      
      -- Sending newlen dv signal from TX DMA Controller to appropriate
      -- SW_TXBUF_TOP entity according to newlen ifc signal
      TX_NEWLEN_DV_DEMUX : entity work.DEC1FN_ENABLE
         generic map (
            -- Number of input interface
            ITEMS    => TX_IFC_COUNT
         )
         port map (
            ADDR     => tx_buf_newlen_ifc,
            ENABLE   => tx_buf_newlen_dv,
            DO       => txbuf_newlen_dv
         );
         
   end generate;

   GEN_TX_NEWLEN_DEMUX_ONE_FLOW: if TX_IFC_COUNT = 1 generate
      txbuf_newlen_dv(0) <= tx_buf_newlen_dv;
   end generate;

   -- --------------------------------------------------
   -- TX RELLEN Switching logic
   -- --------------------------------------------------
   -- sending tx_enable signal to appropriate possitions in desc_enable signal
   GEN_TX_DESC_EN: for i in 0 to (DESC_FLOWS/2)-1 generate
   
      GEN_TX_DESC_IF: if (i < TX_IFC_COUNT) generate
         desc_enable(i*2+1) <= tx_enable(i);
      end generate;
      
      GEN_TX_DESC_ELSE: if (i >= TX_IFC_COUNT) generate
         desc_enable(i*2+1) <= '0';
      end generate;
   
   end generate;
   
   GEN_TXBUF_RELLEN: for i in 0 to TX_IFC_COUNT-1 generate

      rellen_reg_p : process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               txbuf_rellen_reg((i+1)*16-1 downto i*16) <= (others => '0');
            else
               if (txbuf_rellen_dv(i) = '1' and rellen_read(i) = '1') then
                  txbuf_rellen_reg((i+1)*16-1 downto i*16) <= txbuf_rellen((i+1)*16-1 downto i*16);
               elsif (txbuf_rellen_dv(i) = '1') then
                  txbuf_rellen_reg((i+1)*16-1 downto i*16) <= txbuf_rellen_reg((i+1)*16-1 downto i*16) + txbuf_rellen((i+1)*16-1 downto i*16);
               elsif (rellen_read(i) = '1') then
                  txbuf_rellen_reg((i+1)*16-1 downto i*16) <= (others => '0');
               end if;
            end if;
         end if;
      end process;
   
   end generate;

   tx_buf_rellen_ifc <= tx_rellen_ifc;
   
   rellen_ifc_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            rellen_reg     <= (others => '0');
            tx_rellen_ifc  <= (others => '0');
         else
            rellen_reg     <= txbuf_rellen_reg;
            tx_rellen_ifc  <= tx_rellen_ifc + 1;
         end if;
      end if;
   end process;

   rellen_read <= rellen_read_dec;

   GEN_RELLEN_MUX_MORE_FLOWS: if TX_IFC_COUNT > 1 generate
   
      RELLEN_MUX_I : entity work.GEN_MUX
         generic map (
            -- Data width of input interface
            DATA_WIDTH  => 16,
            -- Number of outputs
            MUX_WIDTH   => TX_IFC_COUNT
         )
         port map (
            DATA_IN     => txbuf_rellen_reg,
            SEL         => tx_rellen_ifc,
            DATA_OUT    => tx_buf_rellen
         );
   
   end generate;
   
   rellen_dv_p : process(tx_buf_rellen)
   begin
      if (tx_buf_rellen = conv_std_logic_vector(0, tx_buf_rellen'length)) then
         tx_buf_rellen_dv <= '0';
      else
         tx_buf_rellen_dv <= '1';
      end if;
   end process;
   
   GEN_RELLEN_MUX_ONE_FLOW: if TX_IFC_COUNT = 1 generate
      tx_buf_rellen <= txbuf_rellen_reg;
   end generate;

   GEN_RELLEN_READ_DEC_MORE_FLOWS: if TX_IFC_COUNT > 1 generate

      RELLEN_READ_DEC_I : entity work.DEC1FN
         generic map (
            -- Number of outputs
            ITEMS => TX_IFC_COUNT
         )
         port map (
            ADDR  => tx_rellen_ifc,
            DO    => rellen_read_dec
         );
         
   end generate;
   
   GEN_RELLEN_READ_DEC_ONE_FLOW: if TX_IFC_COUNT = 1 generate
      rellen_read_dec(0) <= '1';
   end generate;

   -- -----------------------------------------------
   -- TX Connections
   -- -----------------------------------------------

   -- tx_desc_empty MUX
   tx_desc_addr_mux <= zeros(log2(DESC_FLOWS)-1 downto log2(2*TX_IFC_COUNT)) & tx_desc_addr & '1';
   tx_desc_empty <= tx_desc_empty_mux(0);

   TX_DESC_EMPTY_MUX_I : entity work.GEN_MUX
      generic map (
         -- Data width of input
         DATA_WIDTH  => 1,
         -- Number of outputs
         MUX_WIDTH   => DESC_FLOWS
      )
      port map (
         DATA_IN     => desc_empty,
         SEL         => tx_desc_addr_mux,
         DATA_OUT    => tx_desc_empty_mux
      );

   -- TX Interrupts
   TX_INTERRUPT <= tx_interrupt_sig(0);
   
   -- this is done in dma_module_2buf differently
   tx_interrupt_p : process(tx_interrupt_ifc, tx_interrupt_sig)
   begin   
   
      tx_interrupt_set <= (others => '0');

      if (tx_interrupt_sig(0) = '1') then
         tx_interrupt_set(2*TX_IFC_COUNT-1 downto 0) <= (decode(tx_interrupt_ifc & '0'));
      else
         tx_interrupt_set <= (others => '0');
      end if;
   end process;

   -- -----------------------------------------------
   --               Descriptor manager
   -- -----------------------------------------------
   DESC_MANAGER_I : entity work.DESC_MANAGER_GCC
      generic map (
         -- Base address
         BASE_ADDR      => DESC_BASE_ADDR,
         -- Number of flows (RX+TX)
         FLOWS          => DESC_FLOWS,
         -- Size of memory block
         BLOCK_SIZE     => DESC_BLOCK_SIZE,
         -- Data width
         DMA_DATA_WIDTH => 64,
			-- Number of unused flows with odd number.
 	      -- Starts unconnect from higher numbers. So if FLOWS=32 and UNUSED_ODD=5
 	      -- then flows with number 31,29,27,25,23 will be unconnected
			UNUSED_ODD => UNUSED_ODD,
			-- Number of unused flows with odd number.
 	      -- Starts unconnect from higher numbers. So if FLOWS=32 and UNUSED_ODD=5
 	      -- then flows with number 31,29,27,25,23 will be unconnected
			UNUSED_EVEN => UNUSED_EVEN
      )
      port map (
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- Memory write interface
         WR_ADDR        => reg_ib_wr_addr,
         WR_DATA        => reg_ib_wr_data,
         WR_BE          => reg_ib_wr_be,
         WR_REQ         => ib_desc_wr_req,
         WR_RDY         => ib_desc_wr_rdy,
         -- DMA Interface
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

   -- -----------------------------------------------
   -- Descriptor Manager sharing - switching
   -- -----------------------------------------------
   -- rx_tx_desc signal is for switching between RX and TX demands to Descriptor
   -- manager this signal set to '0' means RX, '1' means TX
   cnt_rx_tx_desc : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            rx_tx_desc <= '0';
         else
            rx_tx_desc <= not rx_tx_desc;
         end if;
      end if;
   end process;
   
   zeros <= (others => '0');
   
   -- Note:
   -- rd_desc_read, rs_desc_read_reset are two bits vectors - bit 0 is for RX
   -- and bit 1 is for TX
   desc_switch : process(rx_tx_desc, rs_desc_read, rx_desc_addr, desc_dvld, tx_desc_addr)
   begin
      if (rx_tx_desc = '0') then
         desc_read               <= rs_desc_read(0);
         rs_desc_read_reset(0)   <= '1';
         rs_desc_read_reset(1)   <= '0';
         desc_addr               <= zeros(log2(DESC_FLOWS)-1 downto log2(2*RX_IFC_COUNT)) & rx_desc_addr & '0';
         tx_desc_dv              <= desc_dvld;
         rx_desc_dv              <= '0';
      else
         desc_read               <= rs_desc_read(1);
         rs_desc_read_reset(0)   <= '0';
         rs_desc_read_reset(1)   <= '1';
         desc_addr               <= zeros(log2(DESC_FLOWS)-1 downto log2(2*TX_IFC_COUNT)) & tx_desc_addr & '1';
         tx_desc_dv              <= '0';
         rx_desc_dv              <= desc_dvld;
      end if;
   end process;

   -- swiching rs_desc_read
   desc_rs : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            rs_desc_read <= (others => '0');
         else
            -- sharing with RX
            if (rs_desc_read_set(0) = '1') then
               rs_desc_read(0) <= '1';
            elsif (rs_desc_read_reset(0) = '1') then
               rs_desc_read(0) <= '0';
            end if;
            -- sharing with TX
            if (rs_desc_read_set(1) = '1') then
               rs_desc_read(1) <= '1';
            elsif (rs_desc_read_reset(1) = '1') then
               rs_desc_read(1) <= '0';
            end if;
         end if;
      end if;
   end process;

   rs_desc_read_set(0) <= rx_desc_read;
   rs_desc_read_set(1) <= tx_desc_read;
   
   desc_pipe_en <= '1';

   rx_dma_done <= data2bm_dma_done and not data2bm_dma_tag(0) and not data2bm_dma_tag(7);
   tx_dma_done <= data2bm_dma_done and     data2bm_dma_tag(0) and not data2bm_dma_tag(7);
   
   -- ------------------------------------------------
   --          DMA2DATA for RX Controller
   -- ------------------------------------------------
   DMA2DATA_RX_I : entity work.DMA2DATA
      generic map (
         -- frame data width in bits
         DMA_DATA_WIDTH => 32
      )
      port map (
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         DMA_ADDR       => rx_dma_addr,
         DMA_DOUT       => rx_dma_dout,
         DMA_REQ        => rx_dma_req,
         DMA_ACK        => rx_dma_ack,
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

   -- ------------------------------------------------
   --          DMA2DATA for TX Controller
   -- ------------------------------------------------
   DMA2DATA_TX_I : entity work.DMA2DATA
      generic map (
         -- frame data width in bits
         DMA_DATA_WIDTH => 32
      )
      port map (
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         DMA_ADDR       => tx_dma_addr,
         DMA_DOUT       => tx_dma_dout,
         DMA_REQ        => tx_dma_req,
         DMA_ACK        => tx_dma_ack,
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

   -- ------------------------------------------------
   --         DMA2DATA for Descriptor manager
   -- ------------------------------------------------
   DMA2DATA_DESCMAN_I : entity work.DMA2DATA
      generic map (
         -- frame data width in bits
         DMA_DATA_WIDTH => 64
      )
      port map (
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- input interface
         DMA_ADDR       => desc_dma_addr,
         DMA_DOUT       => desc_dma_dout,
         DMA_REQ        => desc_dma_req,
         DMA_ACK        => desc_dma_ack,
         DMA_DONE       => desc_dma_done,
         DMA_TAG        => desc_dma_tag,
         -- output interface
         TX_SRC_RDY_N   => desc_tx_src_rdy_n,
         TX_DST_RDY_N   => desc_tx_dst_rdy_n,
         TX_DATA        => desc_tx_data,
         -- output tag interface
         TX_DMA_DONE    => data2bm_dma_done,
         TX_DMA_TAG     => data2bm_dma_tag
      );

   -- -----------------------------------------------
   --     MultiFifo for data from DMA Controllers
   -- -----------------------------------------------
   NFIFO2FIFO0_I : entity work.NFIFO2FIFO
      generic map (
         -- Data width of input/output
         DATA_WIDTH  => 64,
         -- Number of input flows
         FLOWS       => 2,
         -- Block size
         BLOCK_SIZE  => 2,
         -- LUT memory generation enable
         LUT_MEMORY  => true,
         -- Global state register
         GLOB_STATE  => false
      )
      port map (
         -- Common interface
         CLK         => CLK,
         RESET       => RESET,
         -- Write Interface
         DATA_IN     => dma_tx_data,
         WRITE       => dma_tx_src_rdy,
         FULL        => dma_tx_dst_rdy,
         -- Read Interface
         DATA_OUT    => mfifo1_data_out,
         DATA_VLD    => mfifo1_data_vld,
         BLOCK_ADDR  => mfifo1_block_addr,
         READ        => mfifo1_read,
         PIPE_EN     => mfifo1_read,
         EMPTY       => mfifo1_empty -- is not used
      );
   
   -- -----------------------------------------------
   --  MultiFifo for data from Descriptor Manager and DMA Controllers
   -- -----------------------------------------------
   NFIFO2FIFO1_I : entity work.NFIFO2FIFO
      generic map (
         -- Data width of intput/output
         DATA_WIDTH  => 2*64,
         -- Number of input flows
         FLOWS       => 2,
         -- Size of memory block
         BLOCK_SIZE  => 2,
         -- LUT memory generation enable
         LUT_MEMORY  => true,
         -- Global state register
         GLOB_STATE  => false
      )
      port map (
         -- Common Interface
         CLK         => CLK,
         RESET       => RESET,
         -- Write Interface
         DATA_IN     => mfifo2_data_in,
         WRITE       => mfifo2_write,
         FULL        => mfifo2_full,
         -- Read Interface
         DATA_OUT    => mfifo2_data_out,
         DATA_VLD    => mfifo2_data_vld,
         BLOCK_ADDR  => mfifo2_block_addr,
         READ        => mfifo2_read,
         PIPE_EN     => mfifo2_read,
         EMPTY       => mfifo2_empty -- is not used
      );
   
   -- -----------------------------------------------
   --         Data to BusMaster instance
   -- -----------------------------------------------
   DATA2BM_I : entity work.DATA2BM
      port map (
         -- Common Interface
         CLK            => CLK,
         RESET          => RESET,
         -- Input Interface
         RX_SRC_RDY_N   => data2bm_rx_src_rdy_n,
         RX_DST_RDY_N   => data2bm_rx_dst_rdy_n,
         RX_DATA        => mfifo2_data_out,
         -- Input TAG Interface
         RX_DMA_TAG     => data2bm_dma_tag,
         RX_DMA_DONE    => data2bm_dma_done,
         -- Bus Master Interface
         BM_GLOBAL_ADDR => ib_bm_global_addr_pipe,
         BM_LOCAL_ADDR  => ib_bm_local_addr_pipe,
         BM_LENGTH      => ib_bm_length_pipe,
         BM_TAG         => bm_tag,
         BM_TRANS_TYPE  => bm_trans_type,
         BM_REQ         => bm_req,
         BM_ACK         => bm_ack,
         -- Output
         BM_OP_TAG      => bm_op_tag,
         BM_OP_DONE     => bm_op_done
      );
   
   -- -----------------------------------------------
   --           MultiFifo connections
   -- -----------------------------------------------
   dma_tx_src_rdy    <= not dma_tx_src_rdy_n;
    -- here isn't NOT, because dma_tx_dst_rdy is FULL signal
   dma_tx_dst_rdy_n  <= dma_tx_dst_rdy;
   
   mfifo1_word_transmission   <= mfifo1_data_vld and mfifo1_read;
   cnt_mfifo1_words_ce        <= mfifo1_word_transmission;
   cnt_block_addr_ce          <= (mfifo1_word_transmission and cnt_mfifo1_words) or (not cnt_mfifo1_words and not mfifo1_data_vld);
   
   data2bm_rx_src_rdy_n <= not mfifo2_data_vld;
   mfifo2_read          <= not data2bm_rx_dst_rdy_n;
   mfifo2_data_in       <= desc_tx_data & mfifo1_data_out;
   mfifo2_write         <= (not desc_tx_src_rdy_n) & mfifo1_data_vld;
   mfifo1_read          <= not mfifo2_full(0);
   desc_tx_dst_rdy_n    <= mfifo2_full(1);
   
   cnt_mfifo1_block_addr : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            mfifo1_block_addr <= (others => '0');
         elsif (cnt_block_addr_ce = '1') then
            mfifo1_block_addr <= mfifo1_block_addr + 1;
         end if;
      end if;
   end process;
   
   cnt_mfifo1_words_cnt : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            cnt_mfifo1_words  <= '0';
         elsif (cnt_mfifo1_words_ce = '1') then
            cnt_mfifo1_words  <= not cnt_mfifo1_words;
         end if;
      end if;
   end process;
   
   cnt_mfifo2_block_addr : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            mfifo2_block_addr <= (others => '0');
         else
            if (mfifo2_block_addr_ce = '1') then
               mfifo2_block_addr <= mfifo2_block_addr + 1;
            end if;
         end if;
      end if;
   end process;
   
   -- Step if current channel is being read, or if current channel is empty
   mfifo2_block_addr_ce <= mfifo2_data_vld or (((not mfifo2_block_addr(0)) and mfifo2_empty(0)) or (mfifo2_block_addr(0) and mfifo2_empty(1)));
                           
   -- -----------------------------------------------
   --                   IB endpoint
   -- -----------------------------------------------
   IB_ENDPOINT_I: entity work.IB_ENDPOINT
      generic map(
         DATA_WIDTH          => 64,
         ADDR_WIDTH          => 32,
         BUS_MASTER_ENABLE   => true,
         ENDPOINT_BASE       => IB_EP_ENDPOINT_BASE,
         ENDPOINT_LIMIT      => IB_EP_ENDPOINT_LIMIT,
         CONNECTED_TO        => IB_EP_CONNECTED_TO,
         STRICT_ORDER        => IB_EP_STRICT_ORDER,
         DATA_REORDER        => IB_EP_DATA_REORDER,
         READ_IN_PROCESS     => IB_EP_READ_IN_PROCESS,
         INPUT_BUFFER_SIZE   => IB_EP_INPUT_BUFFER_SIZE,
         OUTPUT_BUFFER_SIZE  => IB_EP_OUTPUT_BUFFER_SIZE
      )
      port map(
         -- Common Interface
         CLK               => CLK,
         RESET             => RESET,
         -- IB Interface
         IB_DOWN_DATA      => DOWN_DATA,
         IB_DOWN_SOF_N     => DOWN_SOF_N,
         IB_DOWN_EOF_N     => DOWN_EOF_N,
         IB_DOWN_SRC_RDY_N => DOWN_SRC_RDY_N,
         IB_DOWN_DST_RDY_N => DOWN_DST_RDY_N,
         IB_UP_DATA        => UP_DATA,
         IB_UP_SOF_N       => UP_SOF_N,
         IB_UP_EOF_N       => UP_EOF_N,
         IB_UP_SRC_RDY_N   => UP_SRC_RDY_N,
         IB_UP_DST_RDY_N   => UP_DST_RDY_N,
         
         -- Write Interface
         WR_REQ            => ib_wr_req,
         WR_RDY            => ib_wr_rdy,
         WR_DATA           => ib_wr_data,
         WR_ADDR           => ib_wr_addr,
         WR_BE             => ib_wr_be,
         WR_LENGTH         => ib_wr_length,
         WR_SOF            => ib_wr_sof,
         WR_EOF            => ib_wr_eof,
         
         -- Read Interface
         RD_REQ            => ib_rd_req,
         RD_ARDY_ACCEPT    => ib_rd_ardy,
         RD_ADDR           => ib_rd_addr,
         RD_BE             => ib_rd_be,
         RD_LENGTH         => open,
         RD_SOF            => ib_rd_sof,
         RD_EOF            => ib_rd_eof,
         
         RD_DATA           => ib_rd_data,
         RD_SRC_RDY        => ib_rd_src_rdy,
         RD_DST_RDY        => ib_rd_dst_rdy,
         
         -- Bus Master Interface
         BM_DATA           => ib_epbm_data,
         BM_SOF_N          => ib_epbm_sof_n,
         BM_EOF_N          => ib_epbm_eof_n,
         BM_SRC_RDY_N      => ib_epbm_src_rdy_n,
         BM_DST_RDY_N      => ib_epbm_dst_rdy_n,
         
         BM_TAG            => ib_epbm_tag,
         BM_TAG_VLD        => ib_epbm_tag_vld
      ); 

      reg_ib_wr_p : process(CLK)
      begin
         if CLK'event and CLK = '1' then
            if RESET = '1' then
               reg_ib_wr_req <= '0';
            else
               reg_ib_wr_req  <= ib_wr_req;
               reg_ib_wr_data <= ib_wr_data;
               reg_ib_wr_addr <= ib_wr_addr;
               reg_ib_wr_be   <= ib_wr_be;
            end if;
         end if;
      end process;

      -- BM converter ---------------------------------------------------------
      BM_CONVERTER_I: entity work.BM_CONVERTER
      generic map (
         DATA_WIDTH       => 64
      )
      port map (
         -- Common interface
         CLK              => CLK,
         RESET            => RESET,
         
         -- BM interface
         BM_GLOBAL_ADDR   => ib_bm_global_addr,
         BM_LOCAL_ADDR    => ib_bm_local_addr,
         BM_LENGTH        => ib_bm_length,
         BM_TAG           => ib_bm_tag,
         BM_TRANS_TYPE    => ib_bm_trans_type,
         BM_REQ           => ib_bm_req,
         BM_ACK           => ib_bm_ack,
         BM_OP_TAG        => ib_bm_op_tag,
         BM_OP_DONE       => ib_bm_op_done,
    
         -- IB interface
         IB_DATA         => ib_epbm_data,
         IB_SOF_N        => ib_epbm_sof_n,
         IB_EOF_N        => ib_epbm_eof_n,
         IB_SRC_RDY_N    => ib_epbm_src_rdy_n,
         IB_DST_RDY_N    => ib_epbm_dst_rdy_n,
         IB_TAG          => ib_epbm_tag,
         IB_TAG_VLD      => ib_epbm_tag_vld
      );

   -- ------------------------------------------------
   --              TAG SEQUENCER entity
   -- ------------------------------------------------
   TAG_SEQ_I : entity work.TAG_SEQUENCER_TOP
      generic map (
         -- Width of TAG signals to endpoint. Has impact on memory depth
         EP_TAG_WIDTH   => 8,
         -- Width of TAG signals to user. Has impact on memory width
         USR_TAG_WIDTH  => 16
      )
      port map (
         -- Common Interface
         CLK            => CLK,
         RESET          => RESET,
         -- Up direction
         USR_TAG        => bm_tag,
         USR_REQ        => bm_req,
         USR_ACK        => bm_ack,
         USR_TRANS_TYPE => bm_trans_type,
         EP_TAG         => ib_bm_tag_pipe,
         EP_REQ         => ib_bm_req_pipe,
         EP_ACK         => ib_bm_ack_pipe2,
         EP_TRANS_TYPE  => ib_bm_trans_type_pipe,
         -- Down direction
         USR_OP_TAG     => bm_op_tag,
         USR_OP_DONE    => bm_op_done,
         EP_OP_TAG      => ib_bm_op_tag,
         EP_OP_DONE     => ib_bm_op_done,
         -- Completition buffer is full
         WR_FULL        => open,
         RD_FULL        => open,
         -- Completition buffer is empty
         WR_EMPTY       => open,
         RD_EMPTY       => open
      );

   -- Pipe signals mapping
   ib_bm_tag               <= data_out_tag_pipe(7 downto 0);
   ib_bm_trans_type        <= data_out_tag_pipe(9 downto 8);
   ib_bm_global_addr       <= data_out_tag_pipe(73 downto 10);
   ib_bm_local_addr        <= data_out_tag_pipe(105 downto 74);
   ib_bm_length            <= data_out_tag_pipe(117 downto 106);
   
   data_in_tag_pipe(7 downto 0)     <= ib_bm_tag_pipe;
   data_in_tag_pipe(9 downto 8)     <= ib_bm_trans_type_pipe;
   data_in_tag_pipe(73 downto 10)   <= ib_bm_global_addr_pipe;
   data_in_tag_pipe(105 downto 74)  <= ib_bm_local_addr_pipe;
   data_in_tag_pipe(117 downto 106) <= ib_bm_length_pipe;

   -- -------------------------------------------------------
   --      Pipe between Tag sequencer and IB Endpoint 
   -- -------------------------------------------------------
   -- It's needed because of getting higher frequency
   PIPE_TAG_I : entity work.PIPE
      generic map (
         -- Data width of data input/output signal
         DATA_WIDTH  => 118,
         -- Use output register
         USE_OUTREG  => false,
         -- Wires only
         FAKE_PIPE   => false
      )
      port map (
         -- Common interface
         CLK         => CLK,
         RESET       => RESET,
         -- Input interface
         IN_DATA     => data_in_tag_pipe,
         IN_SRC_RDY  => ib_bm_req_pipe,
         IN_DST_RDY  => ib_bm_ack_pipe,
         -- Output interface
         OUT_DATA    => data_out_tag_pipe,
         OUT_SRC_RDY => ib_bm_req,
         OUT_DST_RDY => ib_bm_ack
      );
   -- counting appropriate ib_bm_ack signal for tag sequencer
   ib_bm_ack_pipe2 <= ib_bm_req_pipe and ib_bm_ack_pipe;

   -- ------------------------------------------------
   --      Internal Bus addressing and switching
   -- ------------------------------------------------
   -- Address space is like this:
   -- 0x02000000 RX Buffer 0
   -- 0x02002000 RX Buffer 1
   -- 0x02004000 RX Buffer 2
   -- 0x02006000 RX Buffer 3
   -- ....
   -- 0x02100000 TX Buffer 0
   -- 0x02102000 TX Buffer 1
   -- 0x02104000 TX Buffer 2
   -- 0x02106000 RX Buffer 3
   -- ...
   -- 0x02200000 Descriptor Manager
   -- 0x02280000 RX Status Register
   -- 0x02280008 TX Status Register
   
   reg_rd_addr_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_rd_addr <= (others => '0');
         else
            if (ib_rd_ardy_buf = '1') then
               reg_rd_addr <= ib_rd_addr;
            end if;
         end if;
      end if;
   end process;
   
   -- write request signals
   ib_desc_wr_req <= reg_ib_wr_req and ib_desc_wr_sel;

   GEN_TXBUF_IB_WR_SIGS: for j in 0 to TX_IFC_COUNT-1 generate   
      ib_txbuf_wr_req(j) <= reg_ib_wr_req and ib_txbuf_wr(j);
   end generate; 
   
   -- read request signals
   ib_rxbuf_rd_req      <= ib_rd_req and ib_rxbuf_rd_sel;
   ib_rxcontrol_rd_req  <= ib_rd_req and ib_rxcontrol_rd_sel and ib_rd_ardy_buf;
   ib_txcontrol_rd_req  <= ib_rd_req and ib_txcontrol_rd_sel and ib_rd_ardy_buf;
      
   -- read chip select
   rd_cs_p : process(ib_rd_addr)
   begin
      
      ib_rxbuf_rd_sel      <= '0';
      ib_desc_rd_sel       <= '0';
      ib_rxcontrol_rd_sel  <= '0';
      ib_txcontrol_rd_sel  <= '0';
   
      case ib_rd_addr(21) is
         -- ---------------------------------------
         -- Buffers address space
         when '0'    =>
            case ib_rd_addr(20) is
               -- RX buffer is selected
               when '0'    =>
                  ib_rxbuf_rd_sel <= '1';
               -- TX buffer is selected
               when '1'    =>
                  -- reading demand from IB to TX Buffer is nonsense
               when others => null;
            end case;
         -- ---------------------------------------
         -- Descriptor Manager address space
         when '1'    =>
            case ib_rd_addr(19) is
               -- ---------------------------------
               -- Descriptor manager entity
               when '0'    =>
                  ib_desc_rd_sel <= '1';
               -- ---------------------------------
               -- Interrupt control registers
               when '1'    =>
                  case ib_rd_addr(3) is
                     when '0'    => -- RX control register
                        ib_rxcontrol_rd_sel  <= '1';
                     when '1'    => -- TX control register
                        ib_txcontrol_rd_sel  <= '1';
                     when others => null;
                  end case;
               when others => null;
            end case;
         when others => null;
      end case;
   end process;
   
   -- data out multiplexing
   rd_data_p : process(reg_rd_addr, ib_rxbuf_rd_data, reg_control)
   begin
      case reg_rd_addr(21) is
         -- ---------------------------------------
         -- Buffers address space
         when '0'    =>
            case reg_rd_addr(20) is
               -- RX Buffers
               when '0'    =>
                  ib_rd_data <= ib_rxbuf_rd_data;
               -- TX Buffers
               when '1'    =>
                  -- no read from TX Buffers
                  ib_rd_data <= (others => '0');
               when others => 
                  ib_rd_data <= (others => '0');
            end case;
         -- ---------------------------------------
         -- Descriptor Manager address space
         when '1'    =>
            case reg_rd_addr(19) is
               when '0'    => -- Descriptor manager entity
                  -- no read from descriptor manager
                  ib_rd_data <= (others => '0');
               when '1'    => -- interrupt control registers
                  ib_rd_data <= reg_control;
               when others =>
                  ib_rd_data <= (others => '0');
            end case;
         when others => 
            ib_rd_data  <= (others  => '0');
      end case;
   end process;
   
   -- ardy multiplexing
   rd_ardy_p : process(ib_rd_addr, ib_rxcontrol_rd_ardy, ib_txcontrol_rd_ardy, ib_rxbuf_rd_ardy)
   begin
      case ib_rd_addr(21) is
         -- ---------------------------------------
         -- Buffers address space
         when '0'    =>
            case ib_rd_addr(20) is
               -- RX Buffers
               when '0'    =>
                  ib_rd_ardy_buf <= ib_rxbuf_rd_ardy;
               -- TX Buffers
               when '1'    =>
                  -- nonsense
                  ib_rd_ardy_buf <= '0';
               when others => 
                  ib_rd_ardy_buf <= '0';
            end case;
         -- ---------------------------------------
         -- Descriptor Manager address space
         when '1'    =>
            case ib_rd_addr(19) is
               -- Descriptor manager entity
               when '0'    =>
                  -- no read from Descriptor manager
                  ib_rd_ardy_buf <= '0';
               -- Interrupt control register
               when '1'    =>
                  case ib_rd_addr(3) is
                     when '0'    => -- RX Control reqister
                        ib_rd_ardy_buf <= ib_rxcontrol_rd_ardy;
                     when '1'    => -- TX Control register
                        ib_rd_ardy_buf <= ib_txcontrol_rd_ardy;
                     when others =>
                        ib_rd_ardy_buf <= '0';
                  end case;
               when others => 
                  ib_rd_ardy_buf <= '0';
            end case;
         when others =>
            ib_rd_ardy_buf <= '0';
      end case;
   end process;
   
   ib_rd_ardy  <= ib_rd_ardy_buf;
   
   -- register for ib_rxcontrol_rd_req signal
   reg_ib_rxc_rd_src_rdy_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_ib_rxc_rd_src_rdy <= '0';
         else
            if (ib_rd_dst_rdy = '1') then
               reg_ib_rxc_rd_src_rdy <= ib_rxcontrol_rd_req;
            end if;
         end if;
      end if;
   end process;

   -- register for ib_txcontrol_rd_req signal
   reg_ib_txc_rd_src_rdy_p : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            reg_ib_txc_rd_src_rdy <= '0';
         else
            if (ib_rd_dst_rdy = '1') then
               reg_ib_txc_rd_src_rdy <= ib_txcontrol_rd_req;
            end if;
         end if;
      end if;
   end process;
   
   -- src_rdy multiplexing
   rd_src_rdy_p : process(reg_rd_addr, ib_rxbuf_rd_src_rdy, reg_ib_rxc_rd_src_rdy, reg_ib_txc_rd_src_rdy)
   begin
      case reg_rd_addr(21) is
         -- -----------------------------------------
         -- Buffers address space
         when '0'    =>
            case reg_rd_addr(20) is
               when '0'    => -- RX Buffers
                  ib_rd_src_rdy  <= ib_rxbuf_rd_src_rdy;
               when '1'    => -- TX Buffers
                  -- no read from TX Buffers
                  ib_rd_src_rdy  <= '0';
               when others =>
                  ib_rd_src_rdy  <= '0';
            end case;
         -- -----------------------------------------
         -- Descriptor Manager address space
         when '1'    =>
            case reg_rd_addr(19) is
               when '0'    => -- No read from descriptor manager
                  ib_rd_src_rdy  <= '0';
               when '1'    => -- Interrupt control registers
                  case reg_rd_addr(3) is
                     when '0'    => -- RX Interrupt control register
                        ib_rd_src_rdy  <= reg_ib_rxc_rd_src_rdy;
                     when '1'    => -- TX Interrupt control register
                        ib_rd_src_rdy  <= reg_ib_txc_rd_src_rdy;
                     when others =>
                        ib_rd_src_rdy  <= '0';
                  end case;
               when others =>
                  ib_rd_src_rdy  <= '0';
            end case;
         when others =>
            ib_rd_src_rdy  <= '0';
      end case;
   end process;
   
   reg_dma_stat_p : process (CLK)
   begin
      if (CLK'event and CLK = '1') then
        if (ib_rd_ardy_buf = '1') then
           reg_control <= reg_mx_control;
        end if;
      end if;
   end process;

   -- Control registers output mx
   mx_control_out_p : process(ib_txcontrol_rd_sel, ib_rxcontrol_rd_data, ib_txcontrol_rd_data)
   begin
      --if (CLK'event and CLK = '1') then
        -- if (ib_rd_ardy_buf = '1') then
            
            case ib_txcontrol_rd_sel is
               when '0'    =>
                  reg_mx_control <= ib_rxcontrol_rd_data;
               when '1'    =>
                  reg_mx_control <= ib_txcontrol_rd_data;
               when others =>
                  reg_mx_control <= (others => 'X');
            end case;
            
         --end if;
      --end if;
   end process;
 
--     mx_status_outp: process (ib_txcontrol_rd_sel, ib_rxcontrol_rd_data, ib_txcontrol_rd_data)
--    begin
--       case ib_txcontrol_rd_sel is
--          when '0' =>    mx_dma_stat <= ib_rxcontrol_rd_data;
--          when '1' =>    mx_dma_stat <= ib_txcontrol_rd_data;
--          when others => mx_dma_stat <= (others => 'X');
--       end case;
--    end process;
   
   -- write chip select
   wr_cs_p : process(reg_ib_wr_addr)
   begin
   
      ib_txbuf_wr_sel   <= '0';
      ib_desc_wr_sel    <= '0';
      
      case reg_ib_wr_addr(21) is
         -- ---------------------------------------
         -- Buffers address space
         when '0'    =>
            case reg_ib_wr_addr(20) is
               -- RX buffer is selected
               when '0'    =>
                  -- writing demand from IB to RX Buffer is nonsense
               -- TX buffer is selected
               when '1'    =>
                  ib_txbuf_wr_sel <= '1';
               when others => null;
            end case;
         -- ---------------------------------------
         -- Descriptor manager address space
         when '1'    =>
            case reg_ib_wr_addr(19) is
               -- ---------------------------------
               -- Descriptor manager entity
               when '0'    =>
                  ib_desc_wr_sel <= '1';
               -- ---------------------------------
               -- Interrupt control registers
               when '1'    =>
                  case reg_ib_wr_addr(3) is
                     when '0'    => -- RX control register

                     when '1'    => -- TX control register

                     when others => null;
                  end case;
               when others => null;
            end case;
         when others => null;
      end case;
   end process;
   
   
   GEN_IB_TXBUF_MORE_FLOWS: if TX_IFC_COUNT > 1 generate
   
      -- Decoder sending ib_txbuf_wr_sel signal to appropriate TX channel
      -- for counting ib_txbuf_wr_req
      IB_TXBUF_WR_I : entity work.DEC1FN_ENABLE
         generic map (
            -- Number of outputs
            ITEMS    => TX_IFC_COUNT
         )
         port map (
            ADDR     => reg_ib_wr_addr(TX_BUF_ADDR_RANGE),
            DO       => ib_txbuf_wr,
            ENABLE   => ib_txbuf_wr_sel
         );

      -- address for choosing appropriate ib_wr_txbuf_rdy bit
      ib_txbuf_wr_rdy_addr <= reg_ib_wr_addr(TX_BUF_ADDR_RANGE);
      -- Multiplexer selecting appropriate ib_wr_txbuf_rdy bit according
      -- to ib_txbuf_wr_rdy_addr
      IB_TXBUF_WR_RDY_I : entity work.GEN_MUX
         generic map (
            -- data width of one flow
            DATA_WIDTH  => 1,
            -- Number of inputs
            MUX_WIDTH   => TX_IFC_COUNT
         )
         port map (
            DATA_IN     => ib_txbuf_wr_rdy,
            SEL         => ib_txbuf_wr_rdy_addr,
            DATA_OUT    => ib_txbuf_wr_rdy_mx
         );
         
   end generate;
   
   GEN_IB_TXBUF_ONE_FLOW: if TX_IFC_COUNT = 1 generate
   
      ib_txbuf_wr(0) <= ib_txbuf_wr_sel;
      ib_txbuf_wr_rdy_mx(0) <= ib_txbuf_wr_rdy(0);
   
   end generate;
   
   -- wr rdy multiplexing
   wr_rdy_p : process(reg_ib_wr_addr, ib_desc_wr_rdy, ib_txbuf_wr_rdy_mx)
   begin
   
      case reg_ib_wr_addr(21) is
         -- ----------------------------------------
         -- Buffers address space
         when '0'    =>
            case reg_ib_wr_addr(20) is
               when '0'    => -- RX Buffers
                  ib_wr_rdy <= '0'; -- no write to RX buffers
               when '1'    => -- TX Buffers
                  ib_wr_rdy <= ib_txbuf_wr_rdy_mx(0);
               when others => 
                  ib_wr_rdy <= '0';
            end case;
         -- ----------------------------------------
         -- Descriptor manager address space
         when '1'    =>
            case reg_ib_wr_addr(19) is
               -- ----------------------------------
               -- Descriptor manager entity
               when '0'    =>
                  ib_wr_rdy <= ib_desc_wr_rdy;
               -- ----------------------------------
               -- Interrupt control registers
               when '1'    =>
                  ib_wr_rdy <= '0'; -- no write rdy signal
               when others =>
                  ib_wr_rdy <= '0';
            end case;
         when others =>
            ib_wr_rdy <= '0';
      end case;
   end process;
   
   ib_rxcontrol_rd_ardy <= ib_rxcontrol_rd_sel and ib_rd_dst_rdy;
   ib_txcontrol_rd_ardy <= ib_txcontrol_rd_sel and ib_rd_dst_rdy;
   
   -- write addr for tx buffers
   ib_wr_addr_buf(log2(TX_FLOW_SPACE)-1 downto 0) <= reg_ib_wr_addr(log2(TX_FLOW_SPACE)-1 downto 0);
   ib_wr_addr_buf(31 downto log2(TX_FLOW_SPACE))  <= (others => '0');
   
   -- read addr for rx buffer
   ib_rd_addr_buf(19 downto 0)   <= ib_rd_addr(19 downto 0);
   ib_rd_addr_buf(31 downto 20)  <= (others => '0');

end architecture;
-- --------------------------------------------------------
