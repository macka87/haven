-- rxtx_buffers_pac.vhd: Packet DMA cover with dma ctrl block
-- and rx tx buffers as well as ib and lb endpoint
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
--


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
-- Internal bus
use work.ib_ifc_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity RXTX_BUFFERS_PAC_64b is
   generic(
      -- number of network interfaces (up to 64 in this configuration)
      NET_IFC_COUNT           : integer := 2;

      -- Buffers block size 
      BLOCK_SIZE              : integer := 512;
      -- Total size (in bytes) reserved in RX/TX buffers for one interface
      RXTXBUF_IFC_TOTAL_SIZE  : integer := 16384;

      -- Internal Bus endpoints generics
      IB_EP_CONNECTED_TO       : t_ib_comp := SWITCH_SLAVE;
      IB_EP_ENDPOINT_BASE      : std_logic_vector(31 downto 0) := X"02000000";
      IB_EP_ENDPOINT_LIMIT     : std_logic_vector(31 downto 0) := X"00100000";
      IB_EP_STRICT_ORDER       : boolean := false;
      IB_EP_DATA_REORDER       : boolean := false;
      IB_EP_READ_IN_PROCESS    : integer := 1;
      IB_EP_INPUT_BUFFER_SIZE  : integer := 0;
      IB_EP_OUTPUT_BUFFER_SIZE : integer := 1
   );
   port(
      -- Common interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;
      
      -- network interfaces interface
      -- input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(NET_IFC_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(NET_IFC_COUNT*64-1 downto 0);
      RX_REM         : in  std_logic_vector(NET_IFC_COUNT*log2(64/8)-1 downto 0);
      -- output FrameLink interface
      TX_SOF_N       : out std_logic_vector(NET_IFC_COUNT-1 downto 0);
      TX_SOP_N       : out std_logic_vector(NET_IFC_COUNT-1 downto 0);
      TX_EOP_N       : out std_logic_vector(NET_IFC_COUNT-1 downto 0);
      TX_EOF_N       : out std_logic_vector(NET_IFC_COUNT-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(NET_IFC_COUNT-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(NET_IFC_COUNT-1 downto 0);
      TX_DATA        : out std_logic_vector(NET_IFC_COUNT*64-1 downto 0);
      TX_REM         : out std_logic_vector(NET_IFC_COUNT*log2(64/8)-1 downto 0);

      -- Internal Bus interface
      IB_DOWN_DATA      : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in  std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;
      IB_UP_DATA        : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;

      -- MI32 interface
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_WR           : in  std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_ARDY         : out std_logic;
      MI32_DRDY         : out std_logic
   );
end entity RXTX_BUFFERS_PAC_64b;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of RXTX_BUFFERS_PAC_64b is

   -- Chipscope ICON
   component icon3 is
      port (
              CONTROL0 : inout std_logic_vector(35 downto 0);
              CONTROL1 : inout std_logic_vector(35 downto 0);
              CONTROL2 : inout std_logic_vector(35 downto 0)
           );
   end component;

                  -- Chipscope ILA (144-bit trigger port)
   component ila144 is
      port (
              CONTROL : inout std_logic_vector(35 downto 0);
              CLK     : in std_logic;
              TRIG0   : in std_logic_vector(143 downto 0)
           );
   end component;

      -- Chipscope signals
   signal control0            : std_logic_vector(35 downto 0);
   signal control1            : std_logic_vector(35 downto 0);
   signal control2            : std_logic_vector(35 downto 0);
   signal ila144_trig0        : std_logic_vector(143 downto 0);
   signal ila144_trig1        : std_logic_vector(143 downto 0);
   signal ila144_trig2        : std_logic_vector(143 downto 0);

   attribute noopt : boolean;
   attribute dont_touch : boolean;

   attribute noopt of icon3    : component is TRUE;
   attribute noopt of ila144   : component is TRUE;
   attribute dont_touch of icon3    : component is TRUE;
   attribute dont_touch of ila144   : component is TRUE;

   constant IFCS : integer := NET_IFC_COUNT;
   -- DMA Controller internal signals
   signal dma_interrupt       : std_logic_vector(2*IFCS-1 downto 0);
   signal dma_rx_interrupt    : std_logic_vector(NET_IFC_COUNT-1 downto 0);
   signal dma_tx_interrupt    : std_logic_vector(NET_IFC_COUNT-1 downto 0);
   -- Receive buffer interface
   signal rxbuf_newlen        : std_logic_vector(NET_IFC_COUNT*16-1 downto 0);
   signal rxbuf_newlen_dv     : std_logic_vector(NET_IFC_COUNT-1 downto 0);
   signal rxbuf_newlen_rdy    : std_logic_vector(NET_IFC_COUNT-1 downto 0);
   signal rxbuf_rellen        : std_logic_vector(NET_IFC_COUNT*16-1 downto 0);
   signal rxbuf_rellen_dv     : std_logic_vector(NET_IFC_COUNT-1 downto 0);
   -- Transmit buffer interface
   signal txbuf_newlen        : std_logic_vector(NET_IFC_COUNT*16-1 downto 0);
   signal txbuf_newlen_dv     : std_logic_vector(NET_IFC_COUNT-1 downto 0);
   signal txbuf_newlen_rdy    : std_logic_vector(NET_IFC_COUNT-1 downto 0);
   signal txbuf_rellen        : std_logic_vector(NET_IFC_COUNT*16-1 downto 0);
   signal txbuf_rellen_dv     : std_logic_vector(NET_IFC_COUNT-1 downto 0);

   -- Internal Bus read interface
   -- input
   signal ib_rd_addr          : std_logic_vector(31 downto 0);
   signal ib_rd_be            : std_logic_vector(7 downto 0);
   signal ib_rd_req           : std_logic;
   signal ib_rd_ardy          : std_logic;
   signal ib_rd_sof           : std_logic;
   signal ib_rd_eof           : std_logic;
   -- output
   signal ib_rd_data          : std_logic_vector(63 downto 0);
   signal ib_rd_src_rdy       : std_logic;
   signal ib_rd_dst_rdy       : std_logic;

   -- Internal Bus write interface
   signal ib_wr_addr          : std_logic_vector(31 downto 0);
   signal ib_wr_data          : std_logic_vector(63 downto 0);
   signal ib_wr_be            : std_logic_vector(7 downto 0);
   signal ib_wr_req           : std_logic;
   signal ib_wr_rdy           : std_logic;
   signal ib_wr_length        : std_logic_vector(11 downto 0);
   signal ib_wr_sof           : std_logic;
   signal ib_wr_eof           : std_logic;

   -- Internal Bus busmaster interface (parallel ics format, to tag_sequencer)
   -- input
   signal ib_bm_global_addr   : std_logic_vector(63 downto 0);   -- Global Address 
   signal ib_bm_local_addr    : std_logic_vector(31 downto 0);   -- Local Address
   signal ib_bm_length        : std_logic_vector(11 downto 0);   -- Length
   signal ib_bm_tag           : std_logic_vector(15 downto 0);   -- Operation TAG
   signal ib_bm_trans_type    : std_logic_vector(1 downto 0);    -- Transaction Type
   signal ib_bm_req           : std_logic;                       -- Request
   signal ib_bm_ack           : std_logic;                       -- Ack
   -- output
   signal ib_bm_op_tag        : std_logic_vector(15 downto 0);   -- Operation TAG
   signal ib_bm_op_done       : std_logic;                       -- Acknowledge
   
   -- Internal Bus busmaster interface (parallel, tag_sequencer <-> bm_converter)
   signal ib_bm_seq_tag        : std_logic_vector(7 downto 0);   -- Operation TAG
   signal ib_bm_seq_trans_type : std_logic_vector(1 downto 0);   -- Transaction Type
   signal ib_bm_seq_req        : std_logic;                      -- Request
   signal ib_bm_seq_ack        : std_logic;                      -- Ack

   signal ib_bm_seq_op_tag     : std_logic_vector(7 downto 0);   -- Operation TAG
   signal ib_bm_seq_op_done    : std_logic;                      -- Acknowledge
   
   -- Internal Bus busmaster interface (serial gics format, bm_converter <-> endpoint)
   signal ib_epbm_data      : std_logic_vector(63 downto 0);
   signal ib_epbm_sof_n     : std_logic;
   signal ib_epbm_eof_n     : std_logic;
   signal ib_epbm_src_rdy_n : std_logic;
   signal ib_epbm_dst_rdy_n : std_logic;
   
   signal ib_epbm_tag       : std_logic_vector(7 downto 0);
   signal ib_epbm_tag_vld   : std_logic;
   

   -- write request
   signal ib_txbuf0_wr_req        : std_logic;
   signal ib_txbuf1_wr_req        : std_logic;
   signal ib_dma_wr_req          : std_logic;

   -- read selectors
   signal ib_dma_rd_sel          : std_logic;
   signal ib_rxbuf0_rd_sel       : std_logic;
   signal ib_rxbuf1_rd_sel       : std_logic;
   signal ib_rxstatus_rd_sel     : std_logic;
   signal ib_txstatus_rd_sel     : std_logic;

   -- write selectors
   signal ib_dma_wr_sel          : std_logic;
   signal ib_txbuf0_wr_sel        : std_logic;
   signal ib_txbuf1_wr_sel        : std_logic;

   -- read request
   signal ib_dma_rd_req          : std_logic;
   signal ib_rxbuf0_rd_req       : std_logic;
   signal ib_rxbuf1_rd_req       : std_logic;
   signal ib_rxstatus_rd_req     : std_logic;
   signal ib_txstatus_rd_req     : std_logic;

   -- read data
   signal ib_dma_rd_data         : std_logic_vector(63 downto 0);
   signal ib_rxbuf0_rd_data       : std_logic_vector(63 downto 0);
   signal ib_rxbuf1_rd_data       : std_logic_vector(63 downto 0);
   signal ib_rxstatus_rd_data    : std_logic_vector(63 downto 0); 
   signal ib_txstatus_rd_data    : std_logic_vector(63 downto 0); 

   -- read ardy
   signal ib_dma_rd_ardy         : std_logic;
   signal ib_rxbuf0_rd_ardy       : std_logic;
   signal ib_rxbuf1_rd_ardy       : std_logic;
   signal ib_rxstatus_rd_ardy    : std_logic;
   signal ib_txstatus_rd_ardy    : std_logic;

   -- read src_rdy
   signal ib_dma_rd_src_rdy      : std_logic;
   signal ib_rxbuf0_rd_src_rdy    : std_logic;
   signal ib_rxbuf1_rd_src_rdy    : std_logic;
   signal ib_rxstatus_rd_src_rdy : std_logic;
   signal ib_txstatus_rd_src_rdy : std_logic;

   -- interrupt registers mx output -- registerd
   signal mx_dma_stat         : std_logic_vector(63 downto 0);
   signal reg_dma_stat        : std_logic_vector(63 downto 0);

   -- write ready
   signal ib_txbuf0_wr_rdy        : std_logic;
   signal ib_txbuf1_wr_rdy        : std_logic;
   signal ib_dma_wr_rdy          : std_logic;

   -- addresses for buffers
   signal buf_ib_wr_addr         : std_logic_vector(31 downto 0);
   signal buf_ib_rd_addr         : std_logic_vector(31 downto 0);

   signal rx_interrupt_sig    : std_logic_vector(63 downto 0);
   signal tx_interrupt_sig    : std_logic_vector(63 downto 0);

   signal reg_rd_addr            : std_logic_vector(31 downto 0);
   signal buf_ib_rd_ardy         : std_logic;
   signal reg_ib_rxs_rd_src_rdy  : std_logic;
   signal reg_ib_txs_rd_src_rdy  : std_logic;
   signal reg_rx_irq_pending     : std_logic;
   signal reg_rx_irq_pending_set : std_logic;
   signal reg_rx_irq_pending_clr : std_logic;
   signal reg_tx_irq_pending     : std_logic;
   signal reg_tx_irq_pending_set : std_logic;
   signal reg_tx_irq_pending_clr : std_logic;

   signal rx_or_int     : std_logic;
   signal tx_or_int     : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                             CHIPSCOPE
   -- -------------------------------------------------------------------------
   CHIPSCOPE_I: if (false) generate begin
      ICON3_I : icon3
      port map(
         CONTROL0 => control0,
         CONTROL1 => control1,
         CONTROL2 => control2
       );

       ila144_trig0 <= "00"                     --  4
                       & reg_tx_irq_pending     --  1
                       & reg_rx_irq_pending     --  1
                       & dma_interrupt          --  4
                       & ib_txstatus_rd_sel     --  1
                       & ib_txstatus_rd_src_rdy --  1
                       & ib_txstatus_rd_ardy    --  1
                       & ib_txstatus_rd_data    -- 64
                       & ib_txstatus_rd_req     --  1
                       & ib_rxstatus_rd_sel     --  1
                       & ib_rxstatus_rd_src_rdy --  1
                       & ib_rxstatus_rd_ardy    --  1
                       & ib_rxstatus_rd_data    -- 64
                       & ib_rxstatus_rd_req;    --  1
                                                --===
                                                --144

       ib_rxstatus_rd_src_rdy <= reg_ib_rxs_rd_src_rdy;
       ib_txstatus_rd_src_rdy <= reg_ib_txs_rd_src_rdy;

       ILA144_I0 : ila144
       port map(
          CONTROL => control0,
          CLK     => CLK,
          TRIG0   => ila144_trig0
       );

       ila144_trig1 <= "00000000" & "00000000" &   -- 16
                       "00000000" & "00000000" &   -- 16
                       "00"                        --  2
                       & ib_rd_addr                -- 32
                       & ib_rd_be                  --  8
                       & ib_rd_req                 --  1
                       & ib_rd_ardy                --  1
                       & ib_rd_sof                 --  1
                       & ib_rd_eof                 --  1
                       & ib_rd_data                -- 64
                       & ib_rd_src_rdy             --  1
                       & ib_rd_dst_rdy;            --  1
                                                   --===
                                                   --144


       ILA144_I1 : ila144
       port map(
          CONTROL => control1,
          CLK     => CLK,
          TRIG0   => ila144_trig1
       );

       ila144_trig2 <= "00000000" & "00000000" &  -- 16
                       "00000000"                 --  8
                       & ib_wr_addr               -- 32
                       & ib_wr_data               -- 64
                       & ib_wr_be                 --  8
                       & ib_wr_req                --  1
                       & ib_wr_rdy                --  1
                       & ib_wr_length             -- 12
                       & ib_wr_sof                --  1
                       & ib_wr_eof;               --  1
                                                  --===
                                                  --144


       ILA144_I2 : ila144
       port map(
          CONTROL => control2,
          CLK     => CLK,
          TRIG0   => ila144_trig2
       );

   end generate;
   -- -------------------------------------------------------------------------
   --                             END OF DEBUG
   -- -------------------------------------------------------------------------

   gen_interrupt_signals: for i in 0 to NET_IFC_COUNT-1 generate
      dma_rx_interrupt(i) <= dma_interrupt(2*i);
      dma_tx_interrupt(i) <= dma_interrupt(2*i+1);
   end generate;

   -- INTERRUPT signal made from ORed RX/TX interrupt signals
   rx_interruptp : process(dma_rx_interrupt)
      variable or_int : std_logic;
   begin
      or_int := '0';
      
      for k in 0 to NET_IFC_COUNT-1 loop
         or_int := or_int or dma_rx_interrupt(k);
      end loop;

      rx_or_int <= or_int;
   end process;

      RX_INTERRUPT <= rx_or_int and (not reg_rx_irq_pending);

   tx_interruptp : process(dma_tx_interrupt)
      variable or_int : std_logic;
   begin
      or_int := '0';
      
      for k in 0 to NET_IFC_COUNT-1 loop
         or_int := or_int or dma_tx_interrupt(k);
      end loop;

      tx_or_int <= or_int;
   end process;    

      TX_INTERRUPT <= tx_or_int and (not reg_tx_irq_pending);

   -- interrupts output
   rx_interrupt_sig(NET_IFC_COUNT-1 downto 0) <= dma_rx_interrupt;
   tx_interrupt_sig(NET_IFC_COUNT-1 downto 0) <= dma_tx_interrupt;

   rx_interrupt_sig(63 downto NET_IFC_COUNT) <= (others => '0');
   tx_interrupt_sig(63 downto NET_IFC_COUNT) <= (others => '0');
   

   
   reg_rx_irq_pending_set <= rx_or_int;
   reg_rx_irq_pending_clr <= ib_rxstatus_rd_req;
   -- register reg_rx_irq_pending ------------------------------------------------------
   reg_rx_irq_pendingp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_rx_irq_pending <= '0';
         elsif (reg_rx_irq_pending_set = '1') then
            reg_rx_irq_pending <= '1';
         elsif (reg_rx_irq_pending_clr = '1') then
            reg_rx_irq_pending <= '0';
         end if;
      end if;
   end process;

   -- RX status regs
   RX_DMA_STATUS_REG_I: entity work.DMA_STATUS_REG
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Internal Bus interface
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxstatus_rd_req,
         RD_DATA        => ib_rxstatus_rd_data,
         -- DMA Controller interface
         SET_INTERRUPT  => rx_interrupt_sig
      );

   reg_tx_irq_pending_set <= tx_or_int;
   reg_tx_irq_pending_clr <= ib_txstatus_rd_req;
   -- register reg_tx_irq_pending ------------------------------------------------------
   reg_tx_irq_pendingp: process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_tx_irq_pending <= '0';
         elsif (reg_tx_irq_pending_set = '1') then
            reg_tx_irq_pending <= '1';
         elsif (reg_tx_irq_pending_clr = '1') then
            reg_tx_irq_pending <= '0';
         end if;
      end if;
   end process;


   -- TX status regs
   TX_DMA_STATUS_REG_I: entity work.DMA_STATUS_REG
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Internal Bus interface
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_txstatus_rd_req,
         RD_DATA        => ib_txstatus_rd_data,
         -- DMA Controller interface
         SET_INTERRUPT  => tx_interrupt_sig
      );

   -- to remember last read address - we need output multiplexing
   -- register reg_rd_addr ------------------------------------------------------
   reg_rd_addrp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_rd_addr <= (others => '0');
         elsif (buf_ib_rd_ardy = '1') then
            reg_rd_addr <= ib_rd_addr;
         end if;
      end if;
   end process;


   -- read request signals
   ib_rxbuf0_rd_req      <= ib_rd_req and ib_rxbuf0_rd_sel;
   ib_rxbuf1_rd_req      <= ib_rd_req and ib_rxbuf1_rd_sel;
   -- we do not read tx buff
   ib_rxstatus_rd_req   <= ib_rd_req and ib_rxstatus_rd_sel and buf_ib_rd_ardy;
   ib_txstatus_rd_req   <= ib_rd_req and ib_txstatus_rd_sel and buf_ib_rd_ardy;
   ib_dma_rd_req        <= ib_rd_req and ib_dma_rd_sel;

   -- write request signals
   -- we do not write rx buff
   ib_txbuf0_wr_req      <= ib_wr_req and ib_txbuf0_wr_sel;
   ib_txbuf1_wr_req      <= ib_wr_req and ib_txbuf1_wr_sel;
   ib_dma_wr_req        <= ib_wr_req and ib_dma_wr_sel;

   -- read chip select
   rd_csp: process( ib_rd_addr )
   begin
      ib_rxbuf0_rd_sel     <= '0';
      ib_rxbuf1_rd_sel     <= '0';
      ib_rxstatus_rd_sel   <= '0';
      ib_txstatus_rd_sel   <= '0';
      ib_dma_rd_sel        <= '0';

      case ib_rd_addr (21) is
         -- buffers address space -----------------------------
         when '0' =>         
            case ib_rd_addr(20) is
               when '0'    => 
                  case ib_rd_addr(14) is
                     when '0' => ib_rxbuf0_rd_sel      <= '1';
                     when '1' => ib_rxbuf1_rd_sel      <= '1';
                     when others => null;
                  end case;
--                when '1'    =>  -- no read from tx buffers
               when others => null;
            end case;
         -- ---------------------------------------------------   
         -- dma ctrl address space ------------------   
         when '1' =>            
            -- ib_rd_addr bit 20 not used
            case ib_rd_addr(19) is
               when '0'    => ib_dma_rd_sel       <= '1';
               -- interrupt control registers -----------------
               when '1'    =>    
                  case ib_rd_addr(3) is
                     when '0'    => ib_rxstatus_rd_sel  <= '1';
                     when '1'    => ib_txstatus_rd_sel  <= '1';
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
      ib_txbuf0_wr_sel      <= '0';
      ib_txbuf1_wr_sel      <= '0';
      ib_dma_wr_sel        <= '0';

      case ib_wr_addr (21) is
         -- buffers address space -----------------------------
         when '0' =>         
            case ib_wr_addr(20) is
--                when '0'    =>  -- Rx buffer not for writting
               when '1'    => 
                  case ib_wr_addr(14) is
                     when '0' => ib_txbuf0_wr_sel      <= '1';
                     when '1' => ib_txbuf1_wr_sel      <= '1';
                     when others => null;
                  end case;
               when others => null;
            end case;
         -- ---------------------------------------------------   
         -- dma ctrl address space ------------------   
         when '1' =>            
            case ib_wr_addr(19) is
               when '0'    => ib_dma_wr_sel        <= '1';
               when others => null;
            end case;
            -- ------------------------------------------------
         when others => null;
      end case;
      -- ------------------------------------------------------
   end process;


   -- Control registers output mx - registered
   reg_dma_statp: process (CLK)
   begin
      if (clk'event and clk = '1') then
         if (buf_ib_rd_ardy = '1') then
            reg_dma_stat <= mx_dma_stat;
         end if;
      end if;
   end process;

   mx_control_outp: process (ib_txstatus_rd_sel, ib_rxstatus_rd_data, ib_txstatus_rd_data)
   begin
      case ib_txstatus_rd_sel is
         when '0' =>    mx_dma_stat <= ib_rxstatus_rd_data;
         when '1' =>    mx_dma_stat <= ib_txstatus_rd_data;
         when others => mx_dma_stat <= (others => 'X');
      end case;
   end process;


   -- data out multiplexing
   rd_datap: process( reg_rd_addr, ib_rxbuf0_rd_data, ib_rxbuf1_rd_data,
                      reg_dma_stat, ib_dma_rd_data )
   begin
      case reg_rd_addr (21) is
         when '0' =>          -- buffers
            case reg_rd_addr(20) is
               when '0'    => 
                  case reg_rd_addr(14) is
                     when '0' => ib_rd_data <= ib_rxbuf0_rd_data;
                     when '1' => ib_rd_data <= ib_rxbuf1_rd_data;
                     when others => ib_rd_data <= (others => '0');
                  end case;
               --when '1'  => ib_rd_data      -- no read from tx buffers
               when others => ib_rd_data <= (others => '0');
            end case;
         when '1' =>          -- dma
            case reg_rd_addr(19) is
               when '0'    => ib_rd_data <= ib_dma_rd_data;
               when '1'    => ib_rd_data <= reg_dma_stat;   -- interrupt control registers
               when others => ib_rd_data <= (others => '0');
            end case;
         when others => null;
      end case;
   end process;
   
   ib_rxstatus_rd_ardy <= ib_rxstatus_rd_sel and ib_rd_dst_rdy;
   ib_txstatus_rd_ardy <= ib_txstatus_rd_sel and ib_rd_dst_rdy;
   
   -- ardy multiplexing
   rd_ardyp: process( ib_rd_addr, ib_rxbuf0_rd_ardy, ib_rxbuf1_rd_ardy,
      ib_rxstatus_rd_ardy, ib_txstatus_rd_ardy, ib_dma_rd_ardy )
   begin
      case ib_rd_addr (21) is
         when '0' =>          -- buffers
            case ib_rd_addr(20) is
               when '0' => 
                  case ib_rd_addr(14) is
                     when '0' => buf_ib_rd_ardy <= ib_rxbuf0_rd_ardy;
                     when '1' => buf_ib_rd_ardy <= ib_rxbuf1_rd_ardy;
                     when others => buf_ib_rd_ardy <= '0';
                  end case;
               --when '1' => buf_ib_rd_ardy     -- no read from tx buffers
               when others => buf_ib_rd_ardy <= '0';
            end case;
         when '1' =>          -- dma
            case ib_rd_addr(19) is
               when '0' => buf_ib_rd_ardy <= ib_dma_rd_ardy;
               when '1' =>    -- interrupt control register
                  case ib_rd_addr(3) is
                     when '0' => buf_ib_rd_ardy <= ib_rxstatus_rd_ardy;
                     when '1' => buf_ib_rd_ardy <= ib_txstatus_rd_ardy;
                     when others => buf_ib_rd_ardy <= '0';
                  end case;
               when others => buf_ib_rd_ardy <= '0';
            end case;
         when others => buf_ib_rd_ardy <= '0';
      end case;
   end process;

   ib_rd_ardy <= buf_ib_rd_ardy;
    


   -- register reg_ib_rxs_rd_src_rdy ------------------------------------------------------
   reg_ib_rxs_rd_src_rdyp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_ib_rxs_rd_src_rdy <= '0';
         elsif (ib_rd_dst_rdy = '1') then
            reg_ib_rxs_rd_src_rdy <= ib_rxstatus_rd_req;
         end if;
      end if;
   end process;

   -- register reg_ib_txs_rd_src_rdy ------------------------------------------------------
   reg_ib_txs_rd_src_rdyp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_ib_txs_rd_src_rdy <= '0';
         elsif (ib_rd_dst_rdy = '1') then
            reg_ib_txs_rd_src_rdy <= ib_txstatus_rd_req;
         end if;
      end if;
   end process;


   -- src_rdy multiplexing
   rd_src_rdyp: process( reg_rd_addr, ib_rxbuf0_rd_src_rdy,
      ib_rxbuf1_rd_src_rdy, reg_ib_rxs_rd_src_rdy, reg_ib_txs_rd_src_rdy,
      ib_dma_rd_src_rdy)
   begin
      case reg_rd_addr (21) is
         when '0' =>          -- buffers
            case reg_rd_addr(20) is
               when '0' => 
                  case reg_rd_addr(14) is
                     when '0' => ib_rd_src_rdy <= ib_rxbuf0_rd_src_rdy;
                     when '1' => ib_rd_src_rdy <= ib_rxbuf1_rd_src_rdy;
                     when others => ib_rd_src_rdy <= '0';
                  end case;
               --when '1' => ib_rd_src_rdy     -- no read from tx buffers
               when others => ib_rd_src_rdy <= '0';
            end case;
         when '1' =>          -- dma
            case reg_rd_addr(19) is
               when '0' => ib_rd_src_rdy <= ib_dma_rd_src_rdy;
               when '1' =>    -- interrupt control register
                  case reg_rd_addr(3) is
                     when '0' => ib_rd_src_rdy <= reg_ib_rxs_rd_src_rdy;
                     when '1' => ib_rd_src_rdy <= reg_ib_txs_rd_src_rdy;
                     when others => ib_rd_src_rdy <= '0';
                  end case;
               when others => ib_rd_src_rdy <= '0';
            end case;
         when others => ib_rd_src_rdy <= '0';
      end case;
   end process;
   
   -- wr_rdy multiplexing
   wr_rdyp: process( ib_wr_addr, ib_txbuf0_wr_rdy, ib_txbuf1_wr_rdy, 
                     ib_dma_wr_rdy )
   begin
      case ib_wr_addr (21) is
         when '0' =>          -- buffers
            case ib_wr_addr(20) is
               --when '0' => ib_wr_rdy     -- no write to rx buffers
               when '1' => 
                  case ib_wr_addr(14) is
                     when '0' => ib_wr_rdy <= ib_txbuf0_wr_rdy;     
                     when '1' => ib_wr_rdy <= ib_txbuf1_wr_rdy;     
                     when others => ib_wr_rdy <= '0';     
                  end case;
               when others => ib_wr_rdy <= '0';
            end case;
         when '1' =>          -- dma
            case ib_wr_addr(19) is
               when '0' => ib_wr_rdy <= ib_dma_wr_rdy;    
               when '1' =>    -- interrupt control register -- no write to control register
                  case ib_wr_addr(3) is
                     --when '0' => ib_wr_rdy -- no write to rx interrupt status register
                     --when '1' => ib_wr_rdy -- no write to tx interrupt status register
                     when others => ib_wr_rdy <= '0';
                  end case;
               when others => ib_wr_rdy <= '0';
            end case;
         when others => ib_wr_rdy <= '0';
      end case;
   end process;

   -- create correct addresses for buffers
   buf_ib_wr_addr(19 downto 0)  <=  ib_wr_addr(19 downto 0);
   buf_ib_wr_addr(31 downto 20) <= (others => '0');

   buf_ib_rd_addr(19 downto 0)  <=  ib_rd_addr(19 downto 0);
   buf_ib_rd_addr(31 downto 20) <= (others => '0');

   DMA_CTRL_I: entity work.pac_dma_ctrl
      generic map (
         IFCS     => IFCS
      )
      port map (
         -- Common signals
         CLK         => CLK, 
         RESET       => RESET,

         -- pulse with one clk tick wide stride
         INTERRUPT      => dma_interrupt,

         -- Data interface
         -- Write interface
         IB_WR_ADDR     => ib_wr_addr,
         IB_WR_DATA     => ib_wr_data,
         IB_WR_BE       => ib_wr_be,
         IB_WR_REQ      => ib_dma_wr_req,
         IB_WR_RDY      => ib_dma_wr_rdy,
         -- Read interface
         IB_RD_ADDR     => ib_rd_addr,
         IB_RD_DATA     => ib_dma_rd_data,
         IB_RD_BE       => ib_rd_be,
         IB_RD_REQ      => ib_dma_rd_req,
         IB_RD_ARDY     => ib_dma_rd_ardy,
         IB_RD_SRC_RDY  => ib_dma_rd_src_rdy,

         -- BM interface
         IB_BM_GADDR    => ib_bm_global_addr,   -- Global Address 
         IB_BM_LADDR    => ib_bm_local_addr,    -- Local Address
         IB_BM_LENGTH   => ib_bm_length,        -- length
         IB_BM_TAG      => ib_bm_tag,           -- operation TAG
         IB_BM_TTYPE    => ib_bm_trans_type,    -- type of transaction
         IB_BM_REQ      => ib_bm_req,           -- request
         IB_BM_ACK      => ib_bm_ack,           -- ack
         IB_BM_OP_TAG   => ib_bm_op_tag,        -- operation TAG
         IB_BM_OP_DONE  => ib_bm_op_done,       -- Acknowledge

         -- SW memory interface
         MI_SW_DWR      => MI32_DWR,
         MI_SW_ADDR     => MI32_ADDR,
         MI_SW_RD       => MI32_RD,
         MI_SW_WR       => MI32_WR,
         MI_SW_BE       => MI32_BE,
         MI_SW_DRD      => MI32_DRD,
         MI_SW_ARDY     => MI32_ARDY,
         MI_SW_DRDY     => MI32_DRDY,

         -- Receive buffer interface
         RX_NEWLEN      => rxbuf_newlen,
         RX_NEWLEN_DV   => rxbuf_newlen_dv,
         RX_NEWLEN_RDY  => rxbuf_newlen_rdy,
         RX_RELLEN      => rxbuf_rellen,
         RX_RELLEN_DV   => rxbuf_rellen_dv,

         -- Transmit buffer interface
         TX_NEWLEN      => txbuf_newlen,
         TX_NEWLEN_DV   => txbuf_newlen_dv,
         TX_NEWLEN_RDY  => txbuf_newlen_rdy,
         TX_RELLEN      => txbuf_rellen,
         TX_RELLEN_DV   => txbuf_rellen_dv
      );

   -- Receive buffers
   RXBUF0_I : entity work.SW_RXBUF_PAC_TOP
      generic map(
         -- Input data width
         DATA_WIDTH     => 64,
         -- block size
         BLOCK_SIZE     => BLOCK_SIZE,
         -- number of flows
         FLOWS          => 1,
         -- Total size (bytes) for one flow (interface)
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         -- input FrameLink interface
         RX_SOF_N(0)       => RX_SOF_N(0),
         RX_SOP_N(0)       => RX_SOP_N(0),
         RX_EOP_N(0)       => RX_EOP_N(0),
         RX_EOF_N(0)       => RX_EOF_N(0),
         RX_SRC_RDY_N(0)   => RX_SRC_RDY_N(0),
         RX_DST_RDY_N(0)   => RX_DST_RDY_N(0),
         RX_DATA           => RX_DATA(63 downto 0),
         RX_REM            => RX_REM(2 downto 0),

         -- Memory Read Interface
         RD_ADDR        => buf_ib_rd_addr,
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxbuf0_rd_req,
         RD_ARDY        => ib_rxbuf0_rd_ardy,
         RD_DATA        => ib_rxbuf0_rd_data,
         RD_SRC_RDY     => ib_rxbuf0_rd_src_rdy,
         RD_DST_RDY     => ib_rd_dst_rdy,

         -- Receive Buffer Interface --
         RX_NEWLEN         => rxbuf_newlen(15 downto 0),
         RX_NEWLEN_DV(0)   => rxbuf_newlen_dv(0),
         RX_NEWLEN_RDY(0)  => rxbuf_newlen_rdy(0),
         RX_RELLEN         => rxbuf_rellen(15 downto 0),
         RX_RELLEN_DV(0)   => rxbuf_rellen_dv(0)
      );

   RXBUF1_I : entity work.SW_RXBUF_PAC_TOP
      generic map(
         -- Input data width
         DATA_WIDTH     => 64,
         -- block size
         BLOCK_SIZE     => BLOCK_SIZE,
         -- number of flows
         FLOWS          => 1,
         -- Total size (bytes) for one flow (interface)
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,

         -- input FrameLink interface
         RX_SOF_N(0)       => RX_SOF_N(1),
         RX_SOP_N(0)       => RX_SOP_N(1),
         RX_EOP_N(0)       => RX_EOP_N(1),
         RX_EOF_N(0)       => RX_EOF_N(1),
         RX_SRC_RDY_N(0)   => RX_SRC_RDY_N(1),
         RX_DST_RDY_N(0)   => RX_DST_RDY_N(1),
         RX_DATA           => RX_DATA(127 downto 64),
         RX_REM            => RX_REM(5 downto 3),

         -- Memory Read Interface
         RD_ADDR        => buf_ib_rd_addr,
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxbuf1_rd_req,
         RD_ARDY        => ib_rxbuf1_rd_ardy,
         RD_DATA        => ib_rxbuf1_rd_data,
         RD_SRC_RDY     => ib_rxbuf1_rd_src_rdy,
         RD_DST_RDY     => ib_rd_dst_rdy,

         -- Receive Buffer Interface --
         RX_NEWLEN         => rxbuf_newlen(31 downto 16),
         RX_NEWLEN_DV(0)   => rxbuf_newlen_dv(1),
         RX_NEWLEN_RDY(0)  => rxbuf_newlen_rdy(1),
         RX_RELLEN         => rxbuf_rellen(31 downto 16),
         RX_RELLEN_DV(0)   => rxbuf_rellen_dv(1)
      );

   -- Transmit buffers
   TXBUF0_I : entity work.SW_TXBUF_PAC_TOP
      generic map(
         -- Input data width
         DATA_WIDTH     => 64,
         -- block size
         BLOCK_SIZE     => BLOCK_SIZE,
         -- number of flows
         FLOWS          => 1,
         -- Total size (bytes) for one flow (interface)
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- output FrameLink interface
         TX_SOF_N(0)       => TX_SOF_N(0),
         TX_SOP_N(0)       => TX_SOP_N(0),
         TX_EOP_N(0)       => TX_EOP_N(0),
         TX_EOF_N(0)       => TX_EOF_N(0),
         TX_SRC_RDY_N(0)   => TX_SRC_RDY_N(0),
         TX_DST_RDY_N(0)   => TX_DST_RDY_N(0),
         TX_DATA           => TX_DATA(63 downto 0),
         TX_REM            => TX_REM(2 downto 0),
         -- Memory write Interface
         WR_ADDR        => buf_ib_wr_addr,
         WR_DATA        => ib_wr_data,
         WR_BE          => ib_wr_be,
         WR_REQ         => ib_txbuf0_wr_req,
         WR_RDY         => ib_txbuf0_wr_rdy,
         -- Transmit Buffer Interface --
         TX_NEWLEN         => txbuf_newlen(15 downto 0),
         TX_NEWLEN_DV(0)   => txbuf_newlen_dv(0),
         TX_NEWLEN_RDY(0)  => txbuf_newlen_rdy(0),
         TX_RELLEN         => txbuf_rellen(15 downto 0),
         TX_RELLEN_DV(0)   => txbuf_rellen_dv(0)
      );

   TXBUF1_I : entity work.SW_TXBUF_PAC_TOP
      generic map(
         -- Input data width
         DATA_WIDTH     => 64,
         -- block size
         BLOCK_SIZE     => BLOCK_SIZE,
         -- number of flows
         FLOWS          => 1,
         -- Total size (bytes) for one flow (interface)
         TOTAL_FLOW_SIZE=> RXTXBUF_IFC_TOTAL_SIZE
      )
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- output FrameLink interface
         TX_SOF_N(0)       => TX_SOF_N(1),
         TX_SOP_N(0)       => TX_SOP_N(1),
         TX_EOP_N(0)       => TX_EOP_N(1),
         TX_EOF_N(0)       => TX_EOF_N(1),
         TX_SRC_RDY_N(0)   => TX_SRC_RDY_N(1),
         TX_DST_RDY_N(0)   => TX_DST_RDY_N(1),
         TX_DATA           => TX_DATA(127 downto 64),
         TX_REM            => TX_REM(5 downto 3),
         -- Memory write Interface
         WR_ADDR        => buf_ib_wr_addr,
         WR_DATA        => ib_wr_data,
         WR_BE          => ib_wr_be,
         WR_REQ         => ib_txbuf1_wr_req,
         WR_RDY         => ib_txbuf1_wr_rdy,
         -- Transmit Buffer Interface --
         TX_NEWLEN         => txbuf_newlen(31 downto 16),
         TX_NEWLEN_DV(0)   => txbuf_newlen_dv(1),
         TX_NEWLEN_RDY(0)  => txbuf_newlen_rdy(1),
         TX_RELLEN         => txbuf_rellen(31 downto 16),
         TX_RELLEN_DV(0)   => txbuf_rellen_dv(1)
      );

      -- ----------------------------------------------------------------------
      --                               IB endpoint
      -- ----------------------------------------------------------------------
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
         IB_DOWN_DATA      => IB_DOWN_DATA,
         IB_DOWN_SOF_N     => IB_DOWN_SOF_N,
         IB_DOWN_EOF_N     => IB_DOWN_EOF_N,
         IB_DOWN_SRC_RDY_N => IB_DOWN_SRC_RDY_N,
         IB_DOWN_DST_RDY_N => IB_DOWN_DST_RDY_N,
         IB_UP_DATA        => IB_UP_DATA,
         IB_UP_SOF_N       => IB_UP_SOF_N,
         IB_UP_EOF_N       => IB_UP_EOF_N,
         IB_UP_SRC_RDY_N   => IB_UP_SRC_RDY_N,
         IB_UP_DST_RDY_N   => IB_UP_DST_RDY_N,
         
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
         BM_TAG           => ib_bm_seq_tag,
         BM_TRANS_TYPE    => ib_bm_seq_trans_type,
         BM_REQ           => ib_bm_seq_req,
         BM_ACK           => ib_bm_seq_ack,
         BM_OP_TAG        => ib_bm_seq_op_tag,
         BM_OP_DONE       => ib_bm_seq_op_done,
    
         -- IB interface
         IB_DATA         => ib_epbm_data,
         IB_SOF_N        => ib_epbm_sof_n,
         IB_EOF_N        => ib_epbm_eof_n,
         IB_SRC_RDY_N    => ib_epbm_src_rdy_n,
         IB_DST_RDY_N    => ib_epbm_dst_rdy_n,
         IB_TAG          => ib_epbm_tag,
         IB_TAG_VLD      => ib_epbm_tag_vld
      );
      
      -- Tag Sequencer --------------------------------------------------------
      tag_seq_i : entity work.TAG_SEQUENCER_TOP
      generic map(
         EP_TAG_WIDTH   => 8,
         USR_TAG_WIDTH  => 16
      )
      port map(
         CLK         => CLK,
         RESET       => RESET,

         USR_TAG        => ib_bm_tag,
         USR_REQ        => ib_bm_req,
         USR_ACK        => ib_bm_ack,
         USR_TRANS_TYPE => ib_bm_trans_type,
         EP_TAG         => ib_bm_seq_tag,
         EP_REQ         => ib_bm_seq_req,
         EP_ACK         => ib_bm_seq_ack,
         EP_TRANS_TYPE  => ib_bm_seq_trans_type,

         EP_OP_TAG      => ib_bm_seq_op_tag,
         EP_OP_DONE     => ib_bm_seq_op_done,
         USR_OP_TAG     => ib_bm_op_tag,
         USR_OP_DONE    => ib_bm_op_done,

         WR_FULL        => open,
         WR_EMPTY       => open,
         RD_FULL        => open,
         RD_EMPTY       => open
      );

end architecture;
-- ----------------------------------------------------------------------------
