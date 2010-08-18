-- rx_buffers_2x64b.vhd: Optimized cover for N (where N = 2) 64b RXBUFs
--                       with connected DMA Controllers and DESC_MAN
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
--            Jan Vozenilek <xvozen00@stud.fit.vutbr.cz>
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
entity RX_BUFFERS_Nx64b is
   generic(
      -- number of network interfaces (only 2 in this configuration)
      NET_IFC_COUNT           : integer := 8;

      -- RX/TX SW Buffers
      -- Buffers block size 
      BLOCK_SIZE              : integer := 512;
      -- Total size (in bytes) reserved in RX/TX buffers for one interface
      RXBUF_IFC_TOTAL_SIZE  : integer := 16384;

      -- DMA Controller generics
      BUFFER_ADDR             : std_logic_vector(31 downto 0) := X"00000000";
      BUFFER_SIZE             : integer := 4096;
      DESC_BLOCK_SIZE         : integer := 4;
      DESC_BASE_ADDR          : std_logic_vector(31 downto 0) :=  X"02200000";

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
end entity RX_BUFFERS_Nx64b;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of RX_BUFFERS_Nx64b is

   -- Input/Output FrameLink data width
   constant DATA_WIDTH        : integer := 64;
   -- special purpose design - two input interfaces splitted into 8
   -- dma channels - each interface splitted into 4 channels
   constant NET_FLOWS         : integer := NET_IFC_COUNT;

   constant RXBUF_ADDR_WIDTH  : integer := log2(RXBUF_IFC_TOTAL_SIZE);

   constant FL_PARTS          : integer := 1;

   -- Data width for DMA controllers
--    constant CTRL_DMA_DATA_WIDTH : integer := 64/NET_FLOWS;

   -- DMA Controller internal signals
   signal dma_rx_interrupt    : std_logic_vector(2*NET_FLOWS-1 downto 0);
   -- Receive buffer interface
   signal rxbuf_newlen        : std_logic_vector(NET_FLOWS*16-1 downto 0);
   signal rxbuf_newlen_dv     : std_logic_vector(NET_FLOWS-1 downto 0);
   signal rxbuf_newlen_rdy    : std_logic_vector(NET_FLOWS-1 downto 0);
   signal rxbuf_rellen        : std_logic_vector(NET_FLOWS*16-1 downto 0);
   signal rxbuf_rellen_dv     : std_logic_vector(NET_FLOWS-1 downto 0);

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
   
   
   signal ib_rxcontrol_rd_sel    : std_logic;
   signal ib_rxcontrol_rd_req    : std_logic;
   signal ib_rxcontrol_rd_data   : std_logic_vector(63 downto 0); 
   signal ib_rxcontrol_rd_ardy   : std_logic;

   signal ib_rxbuf_rd_src_rdy    : std_logic_vector(NET_FLOWS-1 downto 0);
   signal ib_rxbuf_rd_sel        : std_logic_vector(NET_FLOWS-1 downto 0);
   signal ib_rxbuf_rd_ardy       : std_logic_vector(NET_FLOWS-1 downto 0);
   signal ib_rxbuf_rd_req        : std_logic_vector(NET_FLOWS-1 downto 0);
   signal ib_rxbuf_rd_data       : std_logic_vector(NET_FLOWS*DATA_WIDTH-1 downto 0);

   signal mx_rxbuf_rd_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mx_rxbuf_rd_ardy       : std_logic_vector(0 downto 0);
   signal mx_rxbuf_rd_src_rdy    : std_logic_vector(0 downto 0);

   signal ib_desc_wr_sel         : std_logic;
   signal ib_desc_wr_rdy         : std_logic;
   signal ib_desc_wr_req         : std_logic;

   -- interrupt registers mx output -- registerd
   signal mx_dma_stat            : std_logic_vector(63 downto 0);
   signal reg_dma_stat           : std_logic_vector(63 downto 0);

   -- addresses for buffers
   signal ib_rxbuf_rd_addr         : std_logic_vector(31 downto 0);

   signal dec_buf_rd_addr         : std_logic_vector(NET_FLOWS-1 downto 0);

   -- descriptor manager interface
   signal desc_read           : std_logic_vector(NET_FLOWS-1 downto 0);
   signal s_desc_read         : std_logic_vector(2*NET_FLOWS-1 downto 0);
   signal desc_do             : std_logic_vector(63 downto 0);
   signal desc_empty          : std_logic_vector(NET_FLOWS-1 downto 0);
   signal s_desc_empty        : std_logic_vector(2*NET_FLOWS-1 downto 0);
   
   signal desc_enable         : std_logic_vector(NET_FLOWS-1 downto 0);
   signal s_desc_enable       : std_logic_vector(2*NET_FLOWS-1 downto 0);
   
   signal desc_dma_addr       : std_logic_vector(log2(128/64)-1 downto 0);
   signal desc_dma_dout       : std_logic_vector(63 downto 0);
   signal desc_dma_req        : std_logic;
   signal desc_dma_ack        : std_logic;
   signal desc_dma_done       : std_logic;
   signal desc_dma_tag        : std_logic_vector(15 downto 0); 
        
   signal rx_interrupt_sig    : std_logic_vector(63 downto 0);

   signal reg_rd_addr         : std_logic_vector(31 downto 0);
   signal sig_ib_rd_ardy      : std_logic;
   signal reg_ib_rxc_rd_src_rdy : std_logic;
   signal reg_ib_txc_rd_src_rdy : std_logic;

begin

   -- INTERRUPT signal made from ORed RX interrupt signals
   rx_interruptp : process(dma_rx_interrupt)
      variable or_int : std_logic;
   begin
      or_int := '0';
      
      for k in 0 to 2*NET_FLOWS-1 loop
         or_int := or_int or dma_rx_interrupt(k);
      end loop;

      RX_INTERRUPT <= or_int;
   end process;

   -- interrupts output
   rx_interrupt_sig(2*NET_FLOWS-1 downto 0) <= dma_rx_interrupt;

   rx_interrupt_sig(63 downto 2*NET_FLOWS) <= (others => '0');
   
   -- RX status regs
   RX_DMA_STATUS_REG_I: entity work.DMA_STATUS_REG
      port map(
         CLK            => CLK,
         RESET          => RESET,
         -- Internal Bus interface
         RD_BE          => ib_rd_be,
         RD_REQ         => ib_rxcontrol_rd_req,
         RD_DATA        => ib_rxcontrol_rd_data,
         -- DMA Controller interface
         SET_INTERRUPT  => rx_interrupt_sig
      );



   -- register reg_rd_addr ------------------------------------------------------
   reg_rd_addrp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            reg_rd_addr <= (others => '0');
         elsif (sig_ib_rd_ardy = '1') then
            reg_rd_addr <= ib_rd_addr;
         end if;
      end if;
   end process;


   -- read request signals
   gen_rxbuf_rd_req: for i in 0 to NET_FLOWS-1 generate 
      ib_rxbuf_rd_req(i) <= ib_rd_req and ib_rxbuf_rd_sel(i);
   end generate;
   ib_rxcontrol_rd_req  <= ib_rd_req and ib_rxcontrol_rd_sel and sig_ib_rd_ardy;

   -- write request signal
   ib_desc_wr_req       <= ib_wr_req and ib_desc_wr_sel;

   dec1fn_buf_rd_addr_i: entity work.dec1fn
      generic map (
         ITEMS    => NET_FLOWS
      )
      port map (
         ADDR  => ib_rd_addr(log2(NET_FLOWS)+RXBUF_ADDR_WIDTH-1 
                              downto RXBUF_ADDR_WIDTH),
         DO    => dec_buf_rd_addr
      );

   -- read chip select
   rd_csp: process( ib_rd_addr, dec_buf_rd_addr )
   begin
      ib_rxbuf_rd_sel      <= (others => '0');
      ib_rxcontrol_rd_sel  <= '0';

      case ib_rd_addr (21) is
         -- buffers address space -----------------------------
         when '0' =>         
            case ib_rd_addr(20) is
               when '0'    => -- RX buffer is selected
                              ib_rxbuf_rd_sel  <= dec_buf_rd_addr;
               when '1'    => -- TX buffer is selected
                              null; -- no tx in design
               when others => null;
            end case;
         -- ---------------------------------------------------   
         -- descriptor manager address space ------------------   
         when '1' =>            
            case ib_rd_addr(19) is
               when '0'    => null; -- no reading from DDM
               -- interrupt control registers -----------------
               when '1'    =>    
                  case ib_rd_addr(3) is
                     when '0'    => ib_rxcontrol_rd_sel  <= '1';
                     when '1'    => null; -- no tx in design
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
      ib_desc_wr_sel       <= '0';

      case ib_wr_addr (21) is
         -- buffers address space -----------------------------
         when '0' =>         
            case ib_wr_addr(20) is
               when '0'    => -- RX buffer is selected
                              null; -- no writing to rx
               when '1'    => -- TX buffer is selected
                              null; -- no tx in design
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
                     when '0'    => null; -- no writing to rx control reg
                     when '1'    => null; -- no writing to tx control reg
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


   -- Control registers output mx - registered
   reg_dma_statp: process (CLK)
   begin
      if (clk'event and clk = '1') then
         if (sig_ib_rd_ardy = '1') then
            reg_dma_stat <= mx_dma_stat;
         end if;
      end if;
   end process;

   mx_control_outp: process (ib_rxcontrol_rd_sel, ib_rxcontrol_rd_data)
   begin
      case ib_rxcontrol_rd_sel is
         when '1' => mx_dma_stat <= ib_rxcontrol_rd_data;
         when '0' => mx_dma_stat <= (others => '0');
         when others => mx_dma_stat <= (others => 'X');
      end case;
   end process;


   -- data out multiplexing
   rd_datap: process(reg_rd_addr, mx_rxbuf_rd_data, reg_dma_stat)
   begin
      case reg_rd_addr (21) is
         when '0' =>          -- buffers
            case reg_rd_addr(20) is
               when '0'  => -- RX buffer is selected
                            ib_rd_data <= mx_rxbuf_rd_data;
               --when '1'  => null;      -- no read from tx buffers
               when others => ib_rd_data <= (others => '0');
            end case;
         when '1' =>          -- desc
            case reg_rd_addr(19) is
               --when '0'    => null;                         -- no read from descriptor manager
               when '1'    => ib_rd_data <= reg_dma_stat;   -- interrupt control registers
               when others => ib_rd_data <= (others => '0');
            end case;
         when others => null;
      end case;
   end process;
   
   ib_rxcontrol_rd_ardy <= ib_rxcontrol_rd_sel and ib_rd_dst_rdy;
   
   -- ardy multiplexing
   rd_ardyp: process( ib_rd_addr, mx_rxbuf_rd_ardy, ib_rxcontrol_rd_ardy )
   begin
      case ib_rd_addr (21) is
         when '0' =>          -- buffers
            case ib_rd_addr(20) is
               when '0'    => -- RX buffer is selected
                              sig_ib_rd_ardy <= mx_rxbuf_rd_ardy(0);
               --when '1'    => null; -- no read from tx buffers
               when others => sig_ib_rd_ardy <= '0';
            end case;
         when '1' =>          -- desc
            case ib_rd_addr(19) is
               --when '0' => null;    -- no read from descriptor manager
               when '1' =>    -- interrupt control register
                  case ib_rd_addr(3) is
                     when '0' => sig_ib_rd_ardy <= ib_rxcontrol_rd_ardy;
                     --when '1' => null; -- no tx in design
                     when others => sig_ib_rd_ardy <= '0';
                  end case;
               when others => sig_ib_rd_ardy <= '0';
            end case;
         when others => sig_ib_rd_ardy <= '0';
      end case;
   end process;

   ib_rd_ardy <= sig_ib_rd_ardy;
    


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

   -- src_rdy multiplexing
   rd_src_rdyp: process( reg_rd_addr, mx_rxbuf_rd_src_rdy, reg_ib_rxc_rd_src_rdy )
   begin
      case reg_rd_addr (21) is
         when '0' =>          -- buffers
            case reg_rd_addr(20) is
               when '0'    => -- RX buffer is selected
                              ib_rd_src_rdy <= mx_rxbuf_rd_src_rdy(0);
               --when '1' => null;      -- no read from tx buffers
               when others => ib_rd_src_rdy <= '0';
            end case;
         when '1' =>          -- desc
            case reg_rd_addr(19) is
               -- when '0' => null;    -- no read from descriptor manager
               when '1' =>    -- interrupt control register
                  case reg_rd_addr(3) is
                     when '0' => ib_rd_src_rdy <= reg_ib_rxc_rd_src_rdy;
                     --when '1' => null; -- no tx in design
                     when others => ib_rd_src_rdy <= '0';
                  end case;
               when others => ib_rd_src_rdy <= '0';
            end case;
         when others => ib_rd_src_rdy <= '0';
      end case;
   end process;
   
   -- wr_rdy multiplexing
   wr_rdyp: process( ib_wr_addr, ib_desc_wr_rdy )
   begin
      case ib_wr_addr (21) is
         when '0' =>          -- buffers
            case ib_wr_addr(20) is
               --when '0'  => null;     -- no write to rx buffers
               --when '1'  => null; no tx in design
               when others => ib_wr_rdy <= '0';
            end case;
         when '1' =>          -- desc
            case ib_wr_addr(19) is
               when '0' => ib_wr_rdy <= ib_desc_wr_rdy;    
               --when '1' => null; -- no write to control register
               when others => ib_wr_rdy <= '0';
            end case;
         when others => ib_wr_rdy <= '0';
      end case;
   end process;

   -- create correct read address for buffers
   ib_rxbuf_rd_addr(19 downto 0)  <=  ib_rd_addr(19 downto 0);
   ib_rxbuf_rd_addr(31 downto 20) <= (others => '0');

   gen_mux_rxbuf_rd_data_i: entity work.gen_mux
      generic map (
         DATA_WIDTH => DATA_WIDTH,
         MUX_WIDTH  => NET_FLOWS
      )
      port map (
         DATA_IN  => ib_rxbuf_rd_data,
         SEL      => ib_rd_addr(log2(NET_FLOWS)+RXBUF_ADDR_WIDTH-1 
                              downto RXBUF_ADDR_WIDTH),

         DATA_OUT => mx_rxbuf_rd_data
      );

   gen_mux_rxbuf_rd_ardy_i: entity work.gen_mux
      generic map (
         DATA_WIDTH => 1,
         MUX_WIDTH  => NET_FLOWS
      )
      port map (
         DATA_IN  => ib_rxbuf_rd_ardy,
         SEL      => ib_rd_addr(log2(NET_FLOWS)+RXBUF_ADDR_WIDTH-1 
                              downto RXBUF_ADDR_WIDTH),

         DATA_OUT => mx_rxbuf_rd_ardy
      );

   gen_mux_rxbuf_rd_src_rdy_i: entity work.gen_mux
      generic map (
         DATA_WIDTH => 1,
         MUX_WIDTH  => NET_FLOWS
      )
      port map (
         DATA_IN  => ib_rxbuf_rd_src_rdy,
         SEL      => ib_rd_addr(log2(NET_FLOWS)+RXBUF_ADDR_WIDTH-1 
                              downto RXBUF_ADDR_WIDTH),

         DATA_OUT => mx_rxbuf_rd_src_rdy
      );



   -- descriptor manager
   DESC_MAN_I : entity work.desc_manager
      generic map(
         BASE_ADDR         => DESC_BASE_ADDR, 
         FLOWS             => NET_FLOWS, 
         -- e.g DOWNLOADED_BLOCK_SIZE:
         BLOCK_SIZE        => DESC_BLOCK_SIZE,
         -- data width of DMA memory interface
         DMA_DATA_WIDTH    => 64,
         DESC_INIT_GAP     => 16
      )
      port map(
         CLK      => CLK,
         RESET    => RESET,

         -- Memory interface
         -- Write interface
         WR_ADDR     => ib_wr_addr,
         WR_DATA     => ib_wr_data,  
         WR_BE       => ib_wr_be,    
         WR_REQ      => ib_desc_wr_req,   
         WR_RDY      => ib_desc_wr_rdy,   

         -- DMA Interface --
         DMA_ADDR    => desc_dma_addr,       
         DMA_DOUT    => desc_dma_dout,      
         DMA_REQ     => desc_dma_req,      
         DMA_ACK     => desc_dma_ack,     
         DMA_DONE    => desc_dma_done,   
         DMA_TAG     => desc_dma_tag,   

         -- DMA ctrls interface
         READ        => desc_read,
         DATA_OUT    => desc_do,  
         EMPTY       => desc_empty, -- not DATA_VLD

         -- Per channel enable interface
         ENABLE      => desc_enable 
      );
   
--    gen_s_signals: for i in 0 to NET_FLOWS-1 generate
--       s_desc_read(2*i)    <= desc_read(i);
--       s_desc_read(2*i+1)  <= '0';
--       s_desc_enable(2*i)  <= desc_enable(i);
--       s_desc_enable(2*i+1)<= '0';
--       desc_empty(i)       <= s_desc_empty(2*i);
--    end generate;

   -- DMA Controllers array
   DMA_CTRL_ARRAY_OPT_I : entity work.DMA_CTRL_ARRAY_RX_OPT
      generic map(
         -- number of network interfaces
         NET_IFC_COUNT     => NET_FLOWS,
         -- DMA Controller generics
         BUFFER_ADDR       => BUFFER_ADDR,
         BUFFER_SIZE       => BUFFER_SIZE,
         DMA_CTRL_INIT_GAP => 16#80#
      )
      port map(
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,
         -- Interrupts
         RX_INTERRUPT   => dma_rx_interrupt,
        
         -- Receive buffer interface
         RX_BUF_NEWLEN      => rxbuf_newlen,
         RX_BUF_NEWLEN_DV   => rxbuf_newlen_dv,
         RX_BUF_NEWLEN_RDY  => rxbuf_newlen_rdy,
         RX_BUF_RELLEN      => rxbuf_rellen,
         RX_BUF_RELLEN_DV   => rxbuf_rellen_dv,

         -- MI32 interface
         SW_DWR         => MI32_DWR,
         SW_ADDR        => MI32_ADDR,
         SW_RD          => MI32_RD,
         SW_WR          => MI32_WR,
         SW_BE          => MI32_BE,  
         SW_DRD         => MI32_DRD, 
         SW_ARDY        => MI32_ARDY,
         SW_DRDY        => MI32_DRDY,

         -- Busmaster interface
         BM_GLOBAL_ADDR => ib_bm_global_addr,
         BM_LOCAL_ADDR  => ib_bm_local_addr,
         BM_LENGTH      => ib_bm_length,
         BM_TAG         => ib_bm_tag,
         BM_TRANS_TYPE  => ib_bm_trans_type,
         BM_REQ         => ib_bm_req,
         BM_ACK         => ib_bm_ack,
         BM_OP_TAG      => ib_bm_op_tag,
         BM_OP_DONE     => ib_bm_op_done,

         -- Descriptor Manager Interface
         DESC_READ      => desc_read,   
         DESC_DO        => desc_do,       
         DESC_EMPTY     => desc_empty,    

         DESC_ENABLE    => desc_enable, 

         DESC_DMA_ADDR  => desc_dma_addr,
         DESC_DMA_DOUT  => desc_dma_dout,
         DESC_DMA_REQ   => desc_dma_req, 
         DESC_DMA_ACK   => desc_dma_ack,
         DESC_DMA_DONE  => desc_dma_done,
         DESC_DMA_TAG   => desc_dma_tag 
      );
   

   gen_rxbufs: for i in 0 to NET_FLOWS-1 generate
      -- Receive buffers 0-7
      RXBUF_GEN_I : entity work.SW_RXBUF_TOP
         generic map(
            -- Input data width
            DATA_WIDTH     => DATA_WIDTH,
            -- block size
            BLOCK_SIZE     => BLOCK_SIZE,
            -- number of flows
            FLOWS          => 1,
            TOTAL_FLOW_SIZE=> RXBUF_IFC_TOTAL_SIZE
         )
         port map(
            CLK               => CLK,
            RESET             => RESET,
            -- input FrameLink interface
            RX_SOF_N(0)       => RX_SOF_N(i),
            RX_SOP_N(0)       => RX_SOP_N(i),
            RX_EOP_N(0)       => RX_EOP_N(i),
            RX_EOF_N(0)       => RX_EOF_N(i),
            RX_SRC_RDY_N(0)   => RX_SRC_RDY_N(i),
            RX_DST_RDY_N(0)   => RX_DST_RDY_N(i),
            RX_DATA           => RX_DATA((i+1)*64-1 downto i*64),
            RX_REM            => RX_REM((i+1)*3-1 downto i*3),
            -- Memory Read Interface
            RD_ADDR           => ib_rxbuf_rd_addr,
            RD_BE             => ib_rd_be,
            RD_REQ            => ib_rxbuf_rd_req(i),
            RD_ARDY           => ib_rxbuf_rd_ardy(i),
            RD_DATA           => ib_rxbuf_rd_data((i+1)*64-1 downto i*64),
            RD_SRC_RDY        => ib_rxbuf_rd_src_rdy(i),
            RD_DST_RDY        => ib_rd_dst_rdy,
            -- Receive Buffer Interface --
            RX_NEWLEN         => rxbuf_newlen((i+1)*16-1 downto i*16),
            RX_NEWLEN_DV(0)   => rxbuf_newlen_dv(i),
            RX_NEWLEN_RDY(0)  => rxbuf_newlen_rdy(i),
            RX_RELLEN         => rxbuf_rellen((i+1)*16-1 downto i*16),
            RX_RELLEN_DV(0)   => rxbuf_rellen_dv(i)
         );
   end generate;

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
