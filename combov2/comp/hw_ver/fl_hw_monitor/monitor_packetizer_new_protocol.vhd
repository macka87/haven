--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Smart FrameLink Monitor input packetizer with new protocol
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity MONITOR_PACKETIZER_NEW_PROTOCOL is

   generic
   (
      -- data width
      DATA_WIDTH     : integer := 64;
      -- ID of the endpoint
      ENDPOINT_ID    : std_logic_vector(7 downto 0);
      -- ID of the FrameLink protocol
      PROTOCOL_ID    : std_logic_vector(7 downto 0)
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of MONITOR_PACKETIZER_NEW_PROTOCOL is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================
type state_type is (
   sending_data_header_state,
   sending_data_content_state,
   sending_eop_header_state,
   sending_eof_header_state);

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- maximum length of a FrameLink frame (depends on the size of DMA buffers)
constant FRAME_LENGTH           : integer := 4000;

-- length of NetCOPE protocol header
constant HEADER_LENGTH          : integer := 1;

-- maximum length of a FrameLink frame in words
constant FRAME_WORDS            : integer :=
   FRAME_LENGTH / (DATA_WIDTH/8) + HEADER_LENGTH;

-- depth of the buffer FIFO
constant BUFFER_FIFO_DEPTH      : integer := FRAME_WORDS + 2;

-- the packet counter
constant CNT_LENGTH_WIDTH       : integer := max(log2(FRAME_WORDS-1)+1, 1);
constant CNT_LENGTH_INIT_VALUE  : 
   std_logic_vector(CNT_LENGTH_WIDTH-1 downto 0) :=
   conv_std_logic_vector(FRAME_WORDS, CNT_LENGTH_WIDTH);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input
signal sig_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_rx_sof_n     : std_logic;
signal sig_rx_sop_n     : std_logic;
signal sig_rx_eof_n     : std_logic;
signal sig_rx_eop_n     : std_logic;
signal sig_rx_src_rdy_n : std_logic;
signal sig_rx_dst_rdy_n : std_logic;

-- output
signal sig_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_sof_n     : std_logic;
signal sig_tx_sop_n     : std_logic;
signal sig_tx_eof_n     : std_logic;
signal sig_tx_eop_n     : std_logic;
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic;

-- the data multiplexer
signal mux_data_out     : std_logic_vector(DATA_WIDTH-1 downto 0);

-- the REM multiplexer
signal mux_rem_out      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal mux_rem_sel      : std_logic;

-- the EOP_N multiplexer
signal mux_eop_n_out    : std_logic;

-- the SRC_RDY_N multiplexer
signal mux_src_rdy_n_out    : std_logic;
signal mux_src_rdy_n_sel    : std_logic;

-- BUFFER FIFO input
signal rx_buffer_fifo_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_buffer_fifo_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_buffer_fifo_sof_n     : std_logic;
signal rx_buffer_fifo_sop_n     : std_logic;
signal rx_buffer_fifo_eof_n     : std_logic;
signal rx_buffer_fifo_eop_n     : std_logic;
signal rx_buffer_fifo_src_rdy_n : std_logic;
signal rx_buffer_fifo_dst_rdy_n : std_logic;

-- BUFFER FIFO output
signal tx_buffer_fifo_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_buffer_fifo_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal tx_buffer_fifo_sof_n     : std_logic;
signal tx_buffer_fifo_sop_n     : std_logic;
signal tx_buffer_fifo_eof_n     : std_logic;
signal tx_buffer_fifo_eop_n     : std_logic;
signal tx_buffer_fifo_src_rdy_n : std_logic;
signal tx_buffer_fifo_dst_rdy_n : std_logic;

signal tx_buffer_fifo_frame_rdy : std_logic;

-- FRAME SENDER input
signal rx_sender_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_sender_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_sender_sof_n     : std_logic;
signal rx_sender_sop_n     : std_logic;
signal rx_sender_eof_n     : std_logic;
signal rx_sender_eop_n     : std_logic;
signal rx_sender_src_rdy_n : std_logic;
signal rx_sender_dst_rdy_n : std_logic;

signal rx_sender_send_next : std_logic;

-- FRAME SENDER output
signal tx_sender_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_sender_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal tx_sender_sof_n     : std_logic;
signal tx_sender_sop_n     : std_logic;
signal tx_sender_eof_n     : std_logic;
signal tx_sender_eop_n     : std_logic;
signal tx_sender_src_rdy_n : std_logic;
signal tx_sender_dst_rdy_n : std_logic;

-- FSM signals ---------------------------------------------------------------
signal state_reg    : state_type;
signal state_next   : state_type;
signal fsm_en       : std_logic;

signal is_sending_data_header  : std_logic;
signal is_sending_data_content : std_logic;
signal is_sending_eop_header   : std_logic;
signal is_sending_eof_header   : std_logic;

signal is_sending_data         : std_logic;

-- headers
signal header        : std_logic_vector(DATA_WIDTH-1 downto 0);
signal data_header   : std_logic_vector(DATA_WIDTH-1 downto 0);
signal eop_header    : std_logic_vector(DATA_WIDTH-1 downto 0);
signal eof_header    : std_logic_vector(DATA_WIDTH-1 downto 0);

-- misc signals
signal sig_last_segment : std_logic;
signal sig_accepting    : std_logic;

-- the length counter
signal cnt_length       : std_logic_vector(CNT_LENGTH_WIDTH-1 downto 0);
signal cnt_length_load  : std_logic;
signal cnt_length_en    : std_logic;

signal cmp_cnt_length_zero : std_logic;

begin

   -- Assertions
   assert (DATA_WIDTH = 64)
      report "Unsupported OUT_DATA_WIDTH!"
      severity failure;

   -- mapping inputs
   sig_rx_data         <= RX_DATA;
   sig_rx_rem          <= RX_REM;
   sig_rx_sof_n        <= RX_SOF_N;
   sig_rx_eof_n        <= RX_EOF_N;
   sig_rx_sop_n        <= RX_SOP_N;
   sig_rx_eop_n        <= RX_EOP_N;
   sig_rx_src_rdy_n    <= RX_SRC_RDY_N;
   RX_DST_RDY_N        <= sig_rx_dst_rdy_n;

   -- headers
   header(63 downto 56) <= X"00";
   header(55 downto 48) <= X"00";
   header(47 downto 40) <= X"00";
   header(39 downto 32) <= X"00";
   header(31 downto 24) <= X"00";
   header(23 downto 16) <= X"00";
   header(15 downto  8) <= PROTOCOL_ID;
   header( 7 downto  0) <= ENDPOINT_ID;

   data_header <= header;

   eop_header(63 downto 40) <= header(63 downto 40);
   eop_header(39 downto 32) <= X"01";
   eop_header(31 downto  0) <= header(31 downto  0);

   eof_header(63 downto 40) <= header(63 downto 40);
   eof_header(39 downto 32) <= X"03";
   eof_header(31 downto  0) <= header(31 downto  0);

   -- the multiplexer of the DATA signal
   mux_data_p: process(is_sending_data_header, is_sending_data_content,
      is_sending_eop_header, is_sending_eof_header, sig_rx_data, data_header,
      eop_header, eof_header)
   begin
      mux_data_out <= sig_rx_data;

      if (is_sending_data_header = '1') then
         mux_data_out <= data_header;
      elsif (is_sending_data_content = '1') then
         mux_data_out <= sig_rx_data;
      elsif (is_sending_eop_header = '1') then
         mux_data_out <= eop_header;
      elsif (is_sending_eof_header = '1') then
         mux_data_out <= eof_header;
      end if;
   end process;

   --
   mux_rem_sel    <= (NOT sig_rx_eop_n) AND is_sending_data_content;

   -- the multiplexer of the REM signal
   mux_rem_p: process(mux_rem_sel, sig_rx_rem)
   begin
      mux_rem_out <= sig_rx_rem;

      case (mux_rem_sel) is
         when '0'    => mux_rem_out <= (others => '1');
         when '1'    => mux_rem_out <= sig_rx_rem;
         when others => null;
      end case;
   end process;

   --
   sig_last_segment <= sig_rx_eop_n AND (NOT cmp_cnt_length_zero);

   -- the multiplexer of the EOP_N signal
   mux_eop_n_p: process(is_sending_data_header, is_sending_data_content,
      is_sending_eop_header, is_sending_eof_header, sig_last_segment)
   begin
      mux_eop_n_out <= sig_last_segment;

      if (is_sending_data_header = '1') then
         mux_eop_n_out <= '1';
      elsif (is_sending_data_content = '1') then
         mux_eop_n_out <= sig_last_segment;
      elsif (is_sending_eop_header = '1') then
         mux_eop_n_out <= '0';
      elsif (is_sending_eof_header = '1') then
         mux_eop_n_out <= '0';
      end if;
   end process;

   --
   mux_src_rdy_n_sel  <= is_sending_data;

   -- the multiplexer of the SRC_RDY_N signal
   mux_src_rdy_n_p: process(mux_src_rdy_n_sel, sig_rx_src_rdy_n)
   begin
      mux_src_rdy_n_out <= sig_rx_src_rdy_n;

      case (mux_src_rdy_n_sel) is
         when '0'    => mux_src_rdy_n_out <= '0';
         when '1'    => mux_src_rdy_n_out <= sig_rx_src_rdy_n;
         when others => null;
      end case;
   end process;

   --
   cnt_length_load <= is_sending_data_header;
   cnt_length_en   <= sig_accepting;

   -- the length counter
   cnt_length_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (cnt_length_load = '1') then
            cnt_length <= CNT_LENGTH_INIT_VALUE;
         elsif (cnt_length_en = '1') then
            cnt_length <= cnt_length - 1;
         end if;
      end if;
   end process;

   -- comparer of the counter value
   cmp_cnt_length_zero_p: process(cnt_length)
   begin
      cmp_cnt_length_zero <= '0';

      if (cnt_length = 0) then
         cmp_cnt_length_zero <= '1';
      end if;
   end process;

   --
   rx_buffer_fifo_data        <= mux_data_out;
   rx_buffer_fifo_rem         <= mux_rem_out;
   rx_buffer_fifo_sof_n       <= is_sending_data_content;
   rx_buffer_fifo_sop_n       <= is_sending_data_content;
   rx_buffer_fifo_eof_n       <= mux_eop_n_out;
   rx_buffer_fifo_eop_n       <= mux_eop_n_out;
   rx_buffer_fifo_src_rdy_n   <= mux_src_rdy_n_out;

   -- the buffer that has enough capacity to buffer at least one whole frame
   buffer_fifo_i : entity work.FL_FIFO
   generic map(
      DATA_WIDTH      => DATA_WIDTH,
      ITEMS           => BUFFER_FIFO_DEPTH,
      USE_BRAMS       => true,
      PARTS           => 1
   )
   port map(
      CLK             => CLK,
      RESET           => RESET,
      
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

   sig_rx_dst_rdy_n  <= rx_buffer_fifo_dst_rdy_n OR (NOT is_sending_data_content);

   sig_accepting <= NOT (rx_buffer_fifo_src_rdy_n OR rx_buffer_fifo_dst_rdy_n);

   --
   rx_sender_data             <= tx_buffer_fifo_data;
   rx_sender_rem              <= tx_buffer_fifo_rem;
   rx_sender_sof_n            <= tx_buffer_fifo_sof_n;
   rx_sender_eof_n            <= tx_buffer_fifo_eof_n;
   rx_sender_sop_n            <= tx_buffer_fifo_sop_n;
   rx_sender_eop_n            <= tx_buffer_fifo_eop_n;
   rx_sender_src_rdy_n        <= tx_buffer_fifo_src_rdy_n;
   tx_buffer_fifo_dst_rdy_n   <= rx_sender_dst_rdy_n;

   rx_sender_send_next        <= tx_buffer_fifo_frame_rdy;

   -- the frame sender... sends only if there is a whole frame waiting in order
   -- not to clog the output stream
   frame_sender_i : entity work.FRAME_SENDER
   generic map(
      DATA_WIDTH      => DATA_WIDTH
   )
   port map(
      CLK             => CLK,
      RESET           => RESET,
      
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

   sig_tx_data          <= tx_sender_data;
   sig_tx_rem           <= tx_sender_rem;
   sig_tx_sof_n         <= tx_sender_sof_n;
   sig_tx_eof_n         <= tx_sender_eof_n;
   sig_tx_sop_n         <= tx_sender_sop_n;
   sig_tx_eop_n         <= tx_sender_eop_n;
   sig_tx_src_rdy_n     <= tx_sender_src_rdy_n;
   tx_sender_dst_rdy_n  <= sig_tx_dst_rdy_n;

   --
   fsm_en <= sig_accepting;

   -- ---------------------- CONTROL FSM ------------------------------------
   -- state register logic
   fsm_state_logic : process (CLK)
   begin
     if (rising_edge(CLK)) then
        if (RESET = '1') then
           state_reg <= sending_data_header_state;
        elsif (fsm_en = '1') then
           state_reg <= state_next;
        end if;   
     end if;   
   end process;

   -- next state logic
   fsm_next_state_logic : process (state_reg, cmp_cnt_length_zero,
      sig_rx_eof_n, sig_rx_eop_n)
   begin
     state_next <= state_reg;
     is_sending_data_header  <= '0';
     is_sending_data_content <= '0';
     is_sending_eop_header   <= '0';
     is_sending_eof_header   <= '0';

     case state_reg is
        when sending_data_header_state => 
           is_sending_data_header <= '1';

           state_next <= sending_data_content_state;

        when sending_data_content_state =>
           is_sending_data_content <= '1';

           if (cmp_cnt_length_zero = '1') then
              state_next <= sending_data_header_state;
           elsif (sig_rx_eof_n = '0') then
              state_next <= sending_eof_header_state;
           elsif (sig_rx_eop_n = '0') then
              state_next <= sending_eop_header_state;
           else
              state_next <= sending_data_content_state;
           end if;

        when sending_eop_header_state =>
           is_sending_eop_header <= '1';

           state_next <= sending_data_header_state;

        when sending_eof_header_state =>
           is_sending_eof_header <= '1';

           state_next <= sending_data_header_state;

        end case;      
   end process;

   is_sending_data <= is_sending_data_header OR is_sending_data_content;


   -- mapping outputs
   TX_DATA              <= sig_tx_data;
   TX_REM               <= sig_tx_rem;
   TX_SOF_N             <= sig_tx_sof_n;
   TX_EOF_N             <= sig_tx_eof_n;
   TX_SOP_N             <= sig_tx_sop_n;
   TX_EOP_N             <= sig_tx_eop_n;
   TX_SRC_RDY_N         <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n     <= TX_DST_RDY_N;

end architecture;
