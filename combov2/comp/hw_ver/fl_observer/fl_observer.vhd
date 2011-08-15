--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Observer
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
entity FL_OBSERVER is

   generic
   (
      -- data width
      IN_DATA_WIDTH  : integer := 64;
      OUT_DATA_WIDTH : integer := 64;
      -- how many frames should the observer send (0 is unlimited)
      SEND_X_FRAMES  : integer := 0;
      ENDPOINT_ID    : integer
   );

   port
   (
      RX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;
      TX_CLK         : in  std_logic;
      TX_RESET       : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      -- input FrameLink interface
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : in  std_logic;
      
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
architecture arch of FL_OBSERVER is

-- ==========================================================================
--                                 CONSTANTS
-- ==========================================================================

-- input width of the signal observer
constant SIG_OBSERVER_IN_WIDTH : integer := IN_DATA_WIDTH
   + log2(IN_DATA_WIDTH/8) + 6;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- Input signals
signal sig_rx_data      : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_rx_rem       : std_logic_vector(log2(IN_DATA_WIDTH/8)-1 downto 0);
signal sig_rx_sof_n     : std_logic;
signal sig_rx_sop_n     : std_logic;
signal sig_rx_eof_n     : std_logic;
signal sig_rx_eop_n     : std_logic;
signal sig_rx_src_rdy_n : std_logic;
signal sig_rx_dst_rdy_n : std_logic;

-- Signal Observer input signal
signal observer_rx_data : std_logic_vector(SIG_OBSERVER_IN_WIDTH-1 downto 0);

-- Output signals
signal sig_tx_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_rem       : std_logic_vector(log2(OUT_DATA_WIDTH/8)-1 downto 0);
signal sig_tx_sof_n     : std_logic;
signal sig_tx_sop_n     : std_logic;
signal sig_tx_eof_n     : std_logic;
signal sig_tx_eop_n     : std_logic;
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic;

signal observer_output_ready  : std_logic;

begin

   -- Mapping of input ports
   sig_rx_data         <= RX_DATA;
   sig_rx_rem          <= RX_REM;
   sig_rx_sof_n        <= RX_SOF_N;
   sig_rx_eof_n        <= RX_EOF_N;
   sig_rx_sop_n        <= RX_SOP_N;
   sig_rx_eop_n        <= RX_EOP_N;
   sig_rx_src_rdy_n    <= RX_SRC_RDY_N;
   sig_rx_dst_rdy_n    <= RX_DST_RDY_N;

   -- mapping inputs of Signal Observer
   observer_tx_data <= sig_rx_rem &
                       sig_rx_sof_n &
                       sig_rx_sop_n &
                       sig_rx_eof_n &
                       sig_rx_eop_n &
                       sig_rx_src_rdy_n &
                       sig_rx_dst_rdy_n &
                       sig_rx_data;

   -- Signal Observer instantiation
   signal_observer_i: entity work.SIGNAL_OBSERVER
   generic map(
      -- FrameLink data width
     IN_DATA_WIDTH   => SIG_OBSERVER_IN_WIDTH,
     OUT_DATA_WIDTH  => OUT_DATA_WIDTH,
     ENDPOINT_ID     => ENDPOINT_ID,
     SEND_X_FRAMES   => SEND_X_FRAMES
   )
   port map(
      -- input clock domain
      RX_CLK         => RX_CLK,
      RX_RESET       => RX_RESET,

      -- input interface
      RX_DATA       => observer_rx_data,
      
      -- output clock domain
      TX_CLK        => TX_CLK,
      TX_RESET      => TX_RESET,

      -- output interface
      TX_DATA       => sig_tx_data,
      TX_REM        => sig_tx_rem,
      TX_SOF_N      => sig_tx_sof_n,
      TX_SOP_N      => sig_tx_sop_n,
      TX_EOP_N      => sig_tx_eop_n,
      TX_EOF_N      => sig_tx_eof_n,
      TX_SRC_RDY_N  => sig_tx_src_rdy_n,
      TX_DST_RDY_N  => sig_tx_dst_rdy_n,

      -- output ready signal
      OUTPUT_READY  => observer_output_ready
   );

   -- mapping of outputs
   TX_DATA             <= sig_tx_data;
   TX_REM              <= sig_tx_rem;
   TX_SOF_N            <= sig_tx_sof_n;
   TX_EOF_N            <= sig_tx_eof_n;
   TX_SOP_N            <= sig_tx_sop_n;
   TX_EOP_N            <= sig_tx_eop_n;
   TX_SRC_RDY_N        <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n    <= TX_DST_RDY_N;

   OUTPUT_READY        <= observer_output_ready;

end architecture;
