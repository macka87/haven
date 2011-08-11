--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Signal Observer's Packetizer
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
entity OBSERVER_PACKETIZER is

   generic
   (
      -- data width
      DATA_WIDTH       : integer := 64;
      -- maximum frame length in bytes
      MAX_FRAME_LENGTH : integer := 4096;
      -- Endpoint ID for NetCOPE protocol
      ENDPOINT_ID      : integer
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_READ_NEXT   : out std_logic;
      RX_VALID       : in  std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;

      PACKET_SENT    : out std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of OBSERVER_PACKETIZER is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- the length of the header in words
constant HEAD_WORD_LENGTH  : integer := 1;

-- maximum value of the frame word counter
constant WORD_CNT_MAX_VALUE   : integer := MAX_FRAME_LENGTH/(DATA_WIDTH/8)-1;

-- width of the frame word counter
constant WORD_CNT_WIDTH         : integer := log2(WORD_CNT_MAX_VALUE);

-- types of transactions
constant OBSERVER_TRANS_TYPE :  std_logic_vector(7 downto 0) := X"0B";

-- endpoint tag
constant ENDPOINT_TAG : std_logic_vector(7 downto 0) :=
   conv_std_logic_vector(ENDPOINT_ID, 8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_rx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_rx_valid        : std_logic;
signal sig_rx_read_next    : std_logic;

-- output signals
signal sig_tx_fl_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_fl_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_fl_sof_n     : std_logic;
signal sig_tx_fl_sop_n     : std_logic;
signal sig_tx_fl_eof_n     : std_logic;
signal sig_tx_fl_eop_n     : std_logic;
signal sig_tx_fl_src_rdy_n : std_logic;
signal sig_tx_fl_dst_rdy_n : std_logic;

signal sig_packet_sent     : std_logic;

-- is_sending_header register
signal reg_is_sending_header      : std_logic;
signal reg_is_sending_header_clr  : std_logic;
signal reg_is_sending_header_set  : std_logic;

-- word counter
signal word_cnt            : std_logic_vector(WORD_CNT_WIDTH-1 downto 0);
signal word_cnt_en         : std_logic;
signal word_cnt_clr        : std_logic;


signal is_sending_header   : std_logic;

signal is_word_cnt_max     : std_logic;

signal header_data         : std_logic_vector(DATA_WIDTH-1 downto 0);



begin

   assert (DATA_WIDTH = 64)
      report "Unsupported DATA_WIDTH!"
      severity failure;

   -- mapping of input signals
   sig_rx_data         <= RX_DATA;
   sig_rx_valid        <= RX_VALID;
   RX_READ_NEXT        <= sig_rx_read_next;

   -- input signals
   sig_rx_read_next <= NOT (is_sending_header OR sig_tx_fl_dst_rdy_n);

   -- data in the header
   header_data(63 downto 16) <= (others => '0');
   header_data(15 downto  8) <= OBSERVER_TRANS_TYPE;
   header_data(7  downto  0) <= ENDPOINT_TAG;

   -- ------------------- data multiplexer ----------------------
   mux_p: process(sig_rx_data, header_data, is_sending_header)
   begin
      sig_tx_fl_data <= sig_rx_data;

      if (is_sending_header = '1') then
         sig_tx_fl_data <= header_data;
      else
         sig_tx_fl_data <= sig_rx_data;
      end if;
   end process;


   -- ---------------- is_sending_header register ----------------
   reg_is_sending_header_clr <= sig_rx_valid AND (NOT sig_tx_fl_dst_rdy_n);
   reg_is_sending_header_set <= is_word_cnt_max;

   -- is_sending_header register
   reg_is_sending_header_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_is_sending_header <= '1';
         elsif (reg_is_sending_header_clr = '1') then
            reg_is_sending_header <= '0';
         elsif (reg_is_sending_header_set = '1') then
            reg_is_sending_header <= '1';
         end if;
      end if;
   end process;

   is_sending_header <= reg_is_sending_header;

   -- --------------------- word counter -------------------------
   word_cnt_clr <= is_word_cnt_max;
   word_cnt_en <= sig_rx_valid AND (NOT is_sending_header) AND (NOT
                  sig_tx_fl_dst_rdy_n);

   -- word counter
   word_cnt_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            word_cnt <= (others => '0');
         elsif (word_cnt_clr = '1') then
            word_cnt <= (others => '0');
         elsif (word_cnt_en = '1') then
            word_cnt <= word_cnt + 1;
         end if;
      end if;
   end process;

   -- word counter value comparer
   word_cnt_zero_cmp_p: process (word_cnt)
   begin
      is_word_cnt_max <= '0';

      if (word_cnt = WORD_CNT_MAX_VALUE) then
         is_word_cnt_max <= '1';
      else
         is_word_cnt_max <= '0';
      end if;
   end process;


   -- other output signals
   sig_tx_fl_rem       <= (others => '1');
   sig_tx_fl_sof_n        <= NOT is_sending_header;
   sig_tx_fl_sop_n        <= NOT is_sending_header;
   sig_tx_fl_eof_n        <= NOT is_word_cnt_max;
   sig_tx_fl_eop_n        <= NOT is_word_cnt_max;
   sig_tx_fl_src_rdy_n    <= NOT sig_rx_valid;

   sig_packet_sent     <= (NOT sig_tx_fl_src_rdy_n) AND
                          (NOT sig_tx_fl_dst_rdy_n) AND
                          (NOT sig_tx_fl_eof_n);

   -- mapping of output signals
   TX_DATA             <= sig_tx_fl_data;
   TX_REM              <= sig_tx_fl_rem;
   TX_SOF_N            <= sig_tx_fl_sof_n;
   TX_SOP_N            <= sig_tx_fl_sop_n;
   TX_EOF_N            <= sig_tx_fl_eof_n;
   TX_EOP_N            <= sig_tx_fl_eop_n;
   TX_SRC_RDY_N        <= sig_tx_fl_src_rdy_n;
   sig_tx_fl_dst_rdy_n <= TX_DST_RDY_N;

   PACKET_SENT         <= sig_packet_sent;

end architecture;
