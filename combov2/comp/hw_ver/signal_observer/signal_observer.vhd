--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Signal Observer
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity SIGNAL_OBSERVER is

   generic
   (
      -- data width
      IN_DATA_WIDTH  : integer := 64;
      OUT_DATA_WIDTH : integer := 64;
      ENDPOINT_ID    : integer
   );

   port
   (
      RX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;
      TX_CLK         : in  std_logic;
      TX_RESET       : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input raw interface
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;

      -- ------------------ ready signal ------------------------------------
      OUTPUT_READY   : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of SIGNAL_OBSERVER is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- maximum length of a FrameLink frame (depends on the size of DMA buffers)
constant MAX_FRAME_LENGTH       : integer := 4000;

-- length of NetCOPE protocol header
constant HEADER_LENGTH          : integer := 1;

-- depth of the buffer FIFO
constant BUFFER_FIFO_DEPTH      : integer :=
   MAX_FRAME_LENGTH / (OUT_DATA_WIDTH/8) + HEADER_LENGTH;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
-- data fifo signals write ifc
signal sig_data_fifo_wr_data         : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_data_fifo_wr_write        : std_logic;

-- data fifo signals read ifc
signal sig_data_fifo_rd_data   : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_data_fifo_rd_read   : std_logic;
signal sig_data_fifo_rd_empty  : std_logic;
signal sig_data_fifo_rd_almost_empty : std_logic;

-- OBSERVER_REARRANGER input
signal rx_rearranger_data      : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal rx_rearranger_valid     : std_logic;
signal rx_rearranger_read_next : std_logic;

-- OBSERVER_REARRANGER output
signal tx_rearranger_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_rearranger_valid     : std_logic;
signal tx_rearranger_read_next : std_logic;

-- OBSERVER_PACKETIZER input
signal rx_packetizer_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal rx_packetizer_valid     : std_logic;
signal rx_packetizer_read_next : std_logic;

-- OBSERVER_PACKETIZER output
signal tx_packetizer_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_packetizer_rem       : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal tx_packetizer_sof_n     : std_logic;
signal tx_packetizer_sop_n     : std_logic;
signal tx_packetizer_eof_n     : std_logic;
signal tx_packetizer_eop_n     : std_logic;
signal tx_packetizer_src_rdy_n : std_logic;
signal tx_packetizer_dst_rdy_n : std_logic;

-- Buffer FIFO input
signal rx_buffer_fifo_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal rx_buffer_fifo_rem       : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal rx_buffer_fifo_sof_n     : std_logic;
signal rx_buffer_fifo_sop_n     : std_logic;
signal rx_buffer_fifo_eof_n     : std_logic;
signal rx_buffer_fifo_eop_n     : std_logic;
signal rx_buffer_fifo_src_rdy_n : std_logic;
signal rx_buffer_fifo_dst_rdy_n : std_logic;

-- Buffer FIFO output
signal tx_buffer_fifo_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_buffer_fifo_rem       : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal tx_buffer_fifo_sof_n     : std_logic;
signal tx_buffer_fifo_sop_n     : std_logic;
signal tx_buffer_fifo_eof_n     : std_logic;
signal tx_buffer_fifo_eop_n     : std_logic;
signal tx_buffer_fifo_src_rdy_n : std_logic;
signal tx_buffer_fifo_dst_rdy_n : std_logic;

signal tx_buffer_fifo_frame_rdy : std_logic;

-- Frame Sender input
signal rx_sender_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal rx_sender_rem       : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal rx_sender_sof_n     : std_logic;
signal rx_sender_sop_n     : std_logic;
signal rx_sender_eof_n     : std_logic;
signal rx_sender_eop_n     : std_logic;
signal rx_sender_src_rdy_n : std_logic;
signal rx_sender_dst_rdy_n : std_logic;

signal rx_sender_send_next : std_logic;

-- Frame Sender output
signal tx_sender_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal tx_sender_rem       : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal tx_sender_sof_n     : std_logic;
signal tx_sender_sop_n     : std_logic;
signal tx_sender_eof_n     : std_logic;
signal tx_sender_eop_n     : std_logic;
signal tx_sender_src_rdy_n : std_logic;
signal tx_sender_dst_rdy_n : std_logic;

begin

   -- Assertions
   assert (OUT_DATA_WIDTH = 64)
      report "Unsupported OUT_DATA_WIDTH!"
      severity failure;

   -- Mapping of input ports
   sig_data_fifo_wr_data   <= RX_DATA;
   sig_data_fifo_wr_write  <= not RX_RESET;

   -- --------------- DATA FIFO INSTANCE ------------------------------------
   data_async_fifo : entity work.cdc_fifo
   generic map(
      DATA_WIDTH      => IN_DATA_WIDTH
   )
   port map(
      RESET           => TX_RESET,
      
      -- Write interface
      WR_CLK          => RX_CLK,
      WR_DATA         => sig_data_fifo_wr_data,
      WR_WRITE        => sig_data_fifo_wr_write,
      WR_FULL         => open,
      WR_ALMOST_FULL  => open,
      
      RD_CLK          => TX_CLK,
      RD_DATA         => sig_data_fifo_rd_data,
      RD_READ         => sig_data_fifo_rd_read,
      RD_EMPTY        => sig_data_fifo_rd_empty,
      RD_ALMOST_EMPTY => sig_data_fifo_rd_almost_empty
   );

   -- mapping of rearranger inputs
   rx_rearranger_data         <= sig_data_fifo_rd_data;
   rx_rearranger_valid        <= NOT sig_data_fifo_rd_empty;
   sig_data_fifo_rd_read      <= rx_rearranger_read_next;

   -- --------------- OBSERVER_REARRANGER instance ---------------------------
   observer_rearranger_i : entity work.OBSERVER_REARRANGER
   generic map(
      IN_DATA_WIDTH   => IN_DATA_WIDTH,
      OUT_DATA_WIDTH  => OUT_DATA_WIDTH
   )
   port map(
      CLK             => TX_CLK,
      RESET           => TX_RESET,

      -- RX interface
      RX_DATA         => rx_rearranger_data,
      RX_READ_NEXT    => rx_rearranger_read_next,
      RX_VALID        => rx_rearranger_valid,

      -- TX interface
      TX_DATA         => tx_rearranger_data,
      TX_READ_NEXT    => tx_rearranger_read_next,
      TX_VALID        => tx_rearranger_valid
   );

   -- mapping of packetizer inputs
   rx_packetizer_data         <= tx_rearranger_data;
   rx_packetizer_valid        <= tx_rearranger_valid;
   tx_rearranger_read_next    <= rx_packetizer_read_next;

   -- --------------- OBSERVER_PACKETIZER instance -------------------------------
   observer_packetizer_i : entity work.OBSERVER_PACKETIZER
   generic map(
      DATA_WIDTH      => OUT_DATA_WIDTH,
      ENDPOINT_ID     => ENDPOINT_ID,
      MAX_FRAME_LENGTH=> MAX_FRAME_LENGTH
   )
   port map(
      CLK             => TX_CLK,
      RESET           => TX_RESET,
      
      -- RX interface
      RX_DATA         => rx_packetizer_data,
      RX_READ_NEXT    => rx_packetizer_read_next,
      RX_VALID        => rx_packetizer_valid,

      -- TX interface
      TX_DATA         => tx_packetizer_data,
      TX_REM          => tx_packetizer_rem,
      TX_SOF_N        => tx_packetizer_sof_n,
      TX_EOF_N        => tx_packetizer_eof_n,
      TX_SOP_N        => tx_packetizer_sop_n,
      TX_EOP_N        => tx_packetizer_eop_n,
      TX_SRC_RDY_N    => tx_packetizer_src_rdy_n,
      TX_DST_RDY_N    => tx_packetizer_dst_rdy_n
   );
 
   -- mapping observer outputs
   rx_buffer_fifo_data         <= tx_packetizer_data;
   rx_buffer_fifo_rem          <= tx_packetizer_rem;
   rx_buffer_fifo_sof_n        <= tx_packetizer_sof_n;
   rx_buffer_fifo_eof_n        <= tx_packetizer_eof_n;
   rx_buffer_fifo_sop_n        <= tx_packetizer_sop_n;
   rx_buffer_fifo_eop_n        <= tx_packetizer_eop_n;
   rx_buffer_fifo_src_rdy_n    <= tx_packetizer_src_rdy_n;
   tx_packetizer_dst_rdy_n    <= rx_buffer_fifo_dst_rdy_n;

   -- ----------------------- FL_FIFO instance -------------------------------
   buffer_fifo_i : entity work.FL_FIFO
   generic map(
      DATA_WIDTH      => OUT_DATA_WIDTH,
      ITEMS           => BUFFER_FIFO_DEPTH,
      USE_BRAMS       => true,
      PARTS           => 1
   )
   port map(
      CLK             => TX_CLK,
      RESET           => TX_RESET,
      
      -- RX interface
      RX_DATA         => rx_buffer_fifo_data,
      RX_REM          => rx_buffer_fifo_rem,
      RX_SOF_N        => rx_buffer_fifo_sof_n,
      RX_EOF_N        => rx_buffer_fifo_eof_n,
      RX_SOP_N        => rx_buffer_fifo_sop_n,
      RX_EOP_N        => rx_buffer_fifo_eop_n,
      RX_SRC_RDY_N    => rx_buffer_fifo_src_rdy_n,
      RX_DST_RDY_N    => rx_buffer_fifo_dst_rdy_n,

      -- TX interface
      TX_DATA         => tx_buffer_fifo_data,
      TX_REM          => tx_buffer_fifo_rem,
      TX_SOF_N        => tx_buffer_fifo_sof_n,
      TX_EOF_N        => tx_buffer_fifo_eof_n,
      TX_SOP_N        => tx_buffer_fifo_sop_n,
      TX_EOP_N        => tx_buffer_fifo_eop_n,
      TX_SRC_RDY_N    => tx_buffer_fifo_src_rdy_n,
      TX_DST_RDY_N    => tx_buffer_fifo_dst_rdy_n,

      FRAME_RDY       => tx_buffer_fifo_frame_rdy
   );

   -- mapping FIFO outputs
   rx_sender_data         <= tx_buffer_fifo_data;
   rx_sender_rem          <= tx_buffer_fifo_rem;
   rx_sender_sof_n        <= tx_buffer_fifo_sof_n;
   rx_sender_eof_n        <= tx_buffer_fifo_eof_n;
   rx_sender_sop_n        <= tx_buffer_fifo_sop_n;
   rx_sender_eop_n        <= tx_buffer_fifo_eop_n;
   rx_sender_src_rdy_n    <= tx_buffer_fifo_src_rdy_n;
   tx_buffer_fifo_dst_rdy_n    <= rx_sender_dst_rdy_n;

   rx_sender_send_next    <= tx_buffer_fifo_frame_rdy;

   -- --------------- FRAME_SENDER instance -------------------------------
   frame_sender_i : entity work.FRAME_SENDER
   generic map(
      DATA_WIDTH      => OUT_DATA_WIDTH
   )
   port map(
      CLK             => TX_CLK,
      RESET           => TX_RESET,
      
      -- RX interface
      RX_DATA         => rx_sender_data,
      RX_REM          => rx_sender_rem,
      RX_SOF_N        => rx_sender_sof_n,
      RX_EOF_N        => rx_sender_eof_n,
      RX_SOP_N        => rx_sender_sop_n,
      RX_EOP_N        => rx_sender_eop_n,
      RX_SRC_RDY_N    => rx_sender_src_rdy_n,
      RX_DST_RDY_N    => rx_sender_dst_rdy_n,

      -- 'send next frame' signal
      RX_SEND_NEXT    => rx_sender_send_next,

      -- TX interface
      TX_DATA         => tx_sender_data,
      TX_REM          => tx_sender_rem,
      TX_SOF_N        => tx_sender_sof_n,
      TX_EOF_N        => tx_sender_eof_n,
      TX_SOP_N        => tx_sender_sop_n,
      TX_EOP_N        => tx_sender_eop_n,
      TX_SRC_RDY_N    => tx_sender_src_rdy_n,
      TX_DST_RDY_N    => tx_sender_dst_rdy_n
   );

   -- mapping of outputs
   TX_DATA         <= tx_sender_data;
   TX_REM          <= tx_sender_rem;
   TX_SOF_N        <= tx_sender_sof_n;
   TX_EOF_N        <= tx_sender_eof_n;
   TX_SOP_N        <= tx_sender_sop_n;
   TX_EOP_N        <= tx_sender_eop_n;
   TX_SRC_RDY_N    <= tx_sender_src_rdy_n;
   tx_sender_dst_rdy_n    <= TX_DST_RDY_N;

   OUTPUT_READY        <= sig_data_fifo_rd_almost_empty;

end architecture;
