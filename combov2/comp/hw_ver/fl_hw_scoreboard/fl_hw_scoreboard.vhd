--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Scoreboard
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

-- This is a hardware implementation of a FrameLink scoreboard. It tests data
-- from all interfaces for equality (assuming the the order of transactions is
-- kept).
entity FL_HW_SCOREBOARD is

   generic
   (
      -- input data width
      IN_DATA_WIDTH  : integer := 64;
      -- output data width
      OUT_DATA_WIDTH : integer := 64;
      -- number of input interfaces
      INTERFACES     : integer := 2;
      -- the ID of the endpoint
      ENDPOINT_ID    : std_logic_vector(7 downto 0) := X"00";
      -- the ID of the protocol
      SB_PROTOCOL_ID : std_logic_vector(7 downto 0) := X"5B"
   );

   port
   (
      -- common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interfaces
      RX_DATA        : in  std_logic_vector(INTERFACES*IN_DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(INTERFACES*log2(IN_DATA_WIDTH/8)-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_SOF_N       : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(INTERFACES-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(INTERFACES-1 downto 0);
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_HW_SCOREBOARD is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_rx_data        : std_logic_vector(INTERFACES*IN_DATA_WIDTH-1 downto 0);
signal sig_rx_rem         : std_logic_vector(INTERFACES*log2(IN_DATA_WIDTH/8)-1 downto 0);
signal sig_rx_src_rdy_n   : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_dst_rdy_n   : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_sop_n       : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_eop_n       : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_sof_n       : std_logic_vector(INTERFACES-1 downto 0);
signal sig_rx_eof_n       : std_logic_vector(INTERFACES-1 downto 0);

-- output signals
signal sig_tx_data        : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_rem         : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal sig_tx_src_rdy_n   : std_logic;
signal sig_tx_dst_rdy_n   : std_logic;
signal sig_tx_sop_n       : std_logic;
signal sig_tx_eop_n       : std_logic;
signal sig_tx_sof_n       : std_logic;
signal sig_tx_eof_n       : std_logic;

-- input FIFOs inputs
signal fifo_rx_data       : std_logic_vector(INTERFACES*IN_DATA_WIDTH-1 downto 0);
signal fifo_rx_rem        : std_logic_vector(INTERFACES*log2(IN_DATA_WIDTH/8)-1 downto 0);
signal fifo_rx_sop_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_rx_eop_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_rx_sof_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_rx_eof_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_rx_src_rdy_n  : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_rx_dst_rdy_n  : std_logic_vector(INTERFACES-1 downto 0);

-- input FIFOs outputs
signal fifo_tx_data       : std_logic_vector(INTERFACES*IN_DATA_WIDTH-1 downto 0);
signal fifo_tx_rem        : std_logic_vector(INTERFACES*log2(IN_DATA_WIDTH/8)-1 downto 0);
signal fifo_tx_sop_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_tx_eop_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_tx_sof_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_tx_eof_n      : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_tx_src_rdy_n  : std_logic_vector(INTERFACES-1 downto 0);
signal fifo_tx_dst_rdy_n  : std_logic_vector(INTERFACES-1 downto 0);

-- scoreboard checker
signal sb_checker_data    : std_logic_vector(INTERFACES*IN_DATA_WIDTH-1 downto 0);
signal sb_checker_rem     : std_logic_vector(INTERFACES*log2(IN_DATA_WIDTH/8)-1 downto 0);
signal sb_checker_sop_n   : std_logic_vector(INTERFACES-1 downto 0);
signal sb_checker_eop_n   : std_logic_vector(INTERFACES-1 downto 0);
signal sb_checker_sof_n   : std_logic_vector(INTERFACES-1 downto 0);
signal sb_checker_eof_n   : std_logic_vector(INTERFACES-1 downto 0);
signal sb_checker_en      : std_logic;
signal sb_checker_mismatch: std_logic;

-- scoreboard sender signals
signal sb_sender_tx_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sb_sender_tx_rem       : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal sb_sender_tx_sop_n     : std_logic;
signal sb_sender_tx_eop_n     : std_logic;
signal sb_sender_tx_sof_n     : std_logic;
signal sb_sender_tx_eof_n     : std_logic;
signal sb_sender_tx_src_rdy_n : std_logic;
signal sb_sender_tx_dst_rdy_n : std_logic;

signal sb_sender_send         : std_logic;
signal sb_sender_data_content : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);

-- misc signal
signal shared_dst_rdy_n   : std_logic;
signal sig_accepting      : std_logic;

-- the SRC_RDY_N or
signal or_src_rdy_n        : std_logic;
signal or_src_rdy_n_in     : std_logic_vector(INTERFACES-1 downto 0);

-- the word counter
signal word_cnt            : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal word_cnt_en         : std_logic;

begin

   -- Assertions
   assert    (IN_DATA_WIDTH = 16)
          OR (IN_DATA_WIDTH = 32)
          OR (IN_DATA_WIDTH = 64)
          OR (IN_DATA_WIDTH = 128)
          OR (IN_DATA_WIDTH = 256)
      report "Unsupported input FrameLink width!"
      severity failure;

   assert (OUT_DATA_WIDTH = 64)
      report "Unsupported output FrameLink width!"
      severity failure;

   -- mapping input signals
   sig_rx_data        <= RX_DATA;
   sig_rx_rem         <= RX_REM;
   sig_rx_sof_n       <= RX_SOF_N;
   sig_rx_eof_n       <= RX_EOF_N;
   sig_rx_sop_n       <= RX_SOP_N;
   sig_rx_eop_n       <= RX_EOP_N;
   sig_rx_src_rdy_n   <= RX_SRC_RDY_N;
   RX_DST_RDY_N       <= sig_rx_dst_rdy_n;

   --
   fifo_rx_data        <= sig_rx_data;
   fifo_rx_rem         <= sig_rx_rem;
   fifo_rx_sof_n       <= sig_rx_sof_n;
   fifo_rx_eof_n       <= sig_rx_eof_n;
   fifo_rx_sop_n       <= sig_rx_sop_n;
   fifo_rx_eop_n       <= sig_rx_eop_n;
   fifo_rx_src_rdy_n   <= sig_rx_src_rdy_n;
   sig_rx_dst_rdy_n    <= fifo_rx_dst_rdy_n;

   -- input FIFOs
   gen_fifos: for i in 0 to INTERFACES-1 generate

      fifo_i: entity work.FL_FIFO
      generic map(
         DATA_WIDTH      => IN_DATA_WIDTH,
         ITEMS           => 16,
         USE_BRAMS       => false,
         PARTS           => 1
      )
      port map(
         CLK             => CLK,
         RESET           => RESET,
         
         -- RX interface
         RX_DATA         => fifo_rx_data((i+1)*IN_DATA_WIDTH-1 downto i*IN_DATA_WIDTH),
         RX_REM          => fifo_rx_rem((i+1)*log2(IN_DATA_WIDTH/8)-1 downto i*log2(IN_DATA_WIDTH/8)),
         RX_SOF_N        => fifo_rx_sof_n(i),
         RX_EOF_N        => fifo_rx_eof_n(i),
         RX_SOP_N        => fifo_rx_sop_n(i),
         RX_EOP_N        => fifo_rx_eop_n(i),
         RX_SRC_RDY_N    => fifo_rx_src_rdy_n(i),
         RX_DST_RDY_N    => fifo_rx_dst_rdy_n(i),

         -- TX interface
         TX_DATA         => fifo_tx_data((i+1)*IN_DATA_WIDTH-1 downto i*IN_DATA_WIDTH),
         TX_REM          => fifo_tx_rem((i+1)*log2(IN_DATA_WIDTH/8)-1 downto i*log2(IN_DATA_WIDTH/8)),
         TX_SOF_N        => fifo_tx_sof_n(i),
         TX_EOF_N        => fifo_tx_eof_n(i),
         TX_SOP_N        => fifo_tx_sop_n(i),
         TX_EOP_N        => fifo_tx_eop_n(i),
         TX_SRC_RDY_N    => fifo_tx_src_rdy_n(i),
         TX_DST_RDY_N    => fifo_tx_dst_rdy_n(i)
      );

   end generate;

   -- distribution of the shared DST_RDY_N signal
   gen_dst_rdy_n: for i in 0 to INTERFACES-1 generate
      fifo_tx_dst_rdy_n(i) <= shared_dst_rdy_n;
   end generate;

   --
   or_src_rdy_n_in <= fifo_tx_src_rdy_n;

   -- the big OR of SRC_RDY_Ns
   or_src_rdy_n_p: process(or_src_rdy_n_in)
   begin
      or_src_rdy_n <= '0';

      for i in 0 to INTERFACES-1 loop
         if (or_src_rdy_n_in(i) = '1') then
            or_src_rdy_n <= '1';
         end if;
      end loop;
   end process;

   shared_dst_rdy_n <= or_src_rdy_n;
   sig_accepting    <= NOT or_src_rdy_n;

   --
   sb_checker_data        <= fifo_tx_data;
   sb_checker_rem         <= fifo_tx_rem;
   sb_checker_sof_n       <= fifo_tx_sof_n;
   sb_checker_eof_n       <= fifo_tx_eof_n;
   sb_checker_sop_n       <= fifo_tx_sop_n;
   sb_checker_eop_n       <= fifo_tx_eop_n;

   sb_checker_en          <= sig_accepting;

   -- the scoreboard checker
   sb_checker_i: entity work.SCOREBOARD_CHECKER
   generic map(
      DATA_WIDTH      => IN_DATA_WIDTH,
      INTERFACES      => INTERFACES
   )
   port map(
      CLK             => CLK,
      RESET           => RESET,
      
      -- Inputs
      RX_DATA         => sb_checker_data,
      RX_REM          => sb_checker_rem,
      RX_SOF_N        => sb_checker_sof_n,
      RX_EOF_N        => sb_checker_eof_n,
      RX_SOP_N        => sb_checker_sop_n,
      RX_EOP_N        => sb_checker_eop_n,

      -- Enable
      EN              => sb_checker_en,

      -- output
      MISMATCH        => sb_checker_mismatch
   );

   --
   sb_sender_send          <= sb_checker_mismatch;
   sb_sender_data_content  <= word_cnt;

   -- the scoreboard sender
   sb_sender_i: entity work.SCOREBOARD_SENDER
   generic map (
      -- data width
      DATA_WIDTH      => OUT_DATA_WIDTH,
      -- the ID of the endpoint
      ENDPOINT_ID     => ENDPOINT_ID,
      -- the ID of the protocol
      PROTOCOL_ID     => SB_PROTOCOL_ID
   )
   port map
   (
      -- common signals
      CLK             => CLK,
      RESET           => RESET,

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- the command to send a frame
      SEND            => sb_sender_send,
      -- the data to be sent in the data word of the frame
      DATA_CONTENT    => sb_sender_data_content,
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      -- output FrameLink interface
      TX_DATA         => sb_sender_tx_data,
      TX_REM          => sb_sender_tx_rem,
      TX_SOF_N        => sb_sender_tx_sof_n,
      TX_EOF_N        => sb_sender_tx_eof_n,
      TX_SOP_N        => sb_sender_tx_sop_n,
      TX_EOP_N        => sb_sender_tx_eop_n,
      TX_SRC_RDY_N    => sb_sender_tx_src_rdy_n,
      TX_DST_RDY_N    => sb_sender_tx_dst_rdy_n
   );

   sig_tx_data              <= sb_sender_tx_data;
   sig_tx_rem               <= sb_sender_tx_rem;
   sig_tx_sof_n             <= sb_sender_tx_sof_n;
   sig_tx_eof_n             <= sb_sender_tx_eof_n;
   sig_tx_sop_n             <= sb_sender_tx_sop_n;
   sig_tx_eop_n             <= sb_sender_tx_eop_n;
   sig_tx_src_rdy_n         <= sb_sender_tx_src_rdy_n;
   sb_sender_tx_dst_rdy_n   <= sig_tx_dst_rdy_n;

   --
   word_cnt_en       <= sig_accepting;

   -- the word counter
   word_cnt_p: process(CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            word_cnt <= (others => '0');
         elsif (word_cnt_en = '1') then
            word_cnt <= word_cnt + 1;
         end if;
      end if;
   end process;

   -- mapping output signals
   TX_DATA           <= sig_tx_data;
   TX_REM            <= sig_tx_rem;
   TX_SOF_N          <= sig_tx_sof_n;
   TX_EOF_N          <= sig_tx_eof_n;
   TX_SOP_N          <= sig_tx_sop_n;
   TX_EOP_N          <= sig_tx_eop_n;
   TX_SRC_RDY_N      <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n  <= TX_DST_RDY_N;

end architecture;
