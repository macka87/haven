-- verification_engine.vhd: Architecture of verification engine
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- math package
use work.math_pack.all;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of verification_engine is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- input FrameLink signals
   signal fl_input_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_input_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_input_sof_n      : std_logic;
   signal fl_input_sop_n      : std_logic;
   signal fl_input_eop_n      : std_logic;
   signal fl_input_eof_n      : std_logic;
   signal fl_input_src_rdy_n  : std_logic;
   signal fl_input_dst_rdy_n  : std_logic;

   -- output FrameLink signals
   signal fl_output_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_output_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_output_sof_n      : std_logic;
   signal fl_output_sop_n      : std_logic;
   signal fl_output_eop_n      : std_logic;
   signal fl_output_eof_n      : std_logic;
   signal fl_output_src_rdy_n  : std_logic;
   signal fl_output_dst_rdy_n  : std_logic;

   -- Verification Core FrameLink input
   signal fl_ver_core_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_ver_core_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_ver_core_rx_sof_n     : std_logic;
   signal fl_ver_core_rx_sop_n     : std_logic;
   signal fl_ver_core_rx_eop_n     : std_logic;
   signal fl_ver_core_rx_eof_n     : std_logic;
   signal fl_ver_core_rx_src_rdy_n : std_logic;
   signal fl_ver_core_rx_dst_rdy_n : std_logic;

   -- Verification Core FrameLink output
   signal fl_ver_core_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_ver_core_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_ver_core_tx_sof_n     : std_logic;
   signal fl_ver_core_tx_sop_n     : std_logic;
   signal fl_ver_core_tx_eop_n     : std_logic;
   signal fl_ver_core_tx_eof_n     : std_logic;
   signal fl_ver_core_tx_src_rdy_n : std_logic;
   signal fl_ver_core_tx_dst_rdy_n : std_logic;

   -- FrameLink NetCOPE Adder component input
   signal fl_netcope_adder_in_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_in_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_netcope_adder_in_sof_n     : std_logic;
   signal fl_netcope_adder_in_sop_n     : std_logic;
   signal fl_netcope_adder_in_eop_n     : std_logic;
   signal fl_netcope_adder_in_eof_n     : std_logic;
   signal fl_netcope_adder_in_src_rdy_n : std_logic;
   signal fl_netcope_adder_in_dst_rdy_n : std_logic;

   -- FrameLink NetCOPE Adder component output
   signal fl_netcope_adder_out_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_out_rem      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_netcope_adder_out_sof_n    : std_logic;
   signal fl_netcope_adder_out_sop_n    : std_logic;
   signal fl_netcope_adder_out_eop_n    : std_logic;
   signal fl_netcope_adder_out_eof_n    : std_logic;
   signal fl_netcope_adder_out_src_rdy_n: std_logic;
   signal fl_netcope_adder_out_dst_rdy_n: std_logic;


-- ==========================================================================
--                                   COMPONENTS
-- ==========================================================================

begin

   -- ------------------------------------------------------------------------
   --                           Mapping of inputs
   -- ------------------------------------------------------------------------
   fl_input_data       <= RX_DATA;
   fl_input_rem        <= RX_REM;
   fl_input_sof_n      <= RX_SOF_N;
   fl_input_sop_n      <= RX_SOP_N;
   fl_input_eop_n      <= RX_EOP_N;
   fl_input_eof_n      <= RX_EOF_N;
   fl_input_src_rdy_n  <= RX_SRC_RDY_N;
   RX_DST_RDY_N        <= fl_input_dst_rdy_n;


   -- ------------------------------------------------------------------------
   --                        Input FrameLink Driver
   -- ------------------------------------------------------------------------
   fl_ver_core_rx_data       <= fl_input_data;
   fl_ver_core_rx_rem        <= fl_input_rem;
   fl_ver_core_rx_sof_n      <= fl_input_sof_n;
   fl_ver_core_rx_sop_n      <= fl_input_sop_n;
   fl_ver_core_rx_eop_n      <= fl_input_eop_n;
   fl_ver_core_rx_eof_n      <= fl_input_eof_n;
   fl_ver_core_rx_src_rdy_n  <= fl_input_src_rdy_n;
   fl_input_dst_rdy_n        <= fl_ver_core_rx_dst_rdy_n;


   ver_core_i: entity work.VERIFICATION_CORE
   generic map(
      -- FrameLink data width
      DATA_WIDTH   => DATA_WIDTH
   )
   port map(
      -- input clock domain
      CLK        => CLK,
      RESET      => RESET,

      -- input interface
      RX_DATA       => fl_ver_core_rx_data,
      RX_REM        => fl_ver_core_rx_rem,
      RX_SOF_N      => fl_ver_core_rx_sof_n,
      RX_SOP_N      => fl_ver_core_rx_sop_n,
      RX_EOP_N      => fl_ver_core_rx_eop_n,
      RX_EOF_N      => fl_ver_core_rx_eof_n,
      RX_SRC_RDY_N  => fl_ver_core_rx_src_rdy_n,
      RX_DST_RDY_N  => fl_ver_core_rx_dst_rdy_n,

      -- output interface
      TX_DATA       => fl_ver_core_tx_data,
      TX_REM        => fl_ver_core_tx_rem,
      TX_SOF_N      => fl_ver_core_tx_sof_n,
      TX_SOP_N      => fl_ver_core_tx_sop_n,
      TX_EOP_N      => fl_ver_core_tx_eop_n,
      TX_EOF_N      => fl_ver_core_tx_eof_n,
      TX_SRC_RDY_N  => fl_ver_core_tx_src_rdy_n,
      TX_DST_RDY_N  => fl_ver_core_tx_dst_rdy_n,

      -- MI32 interface
      MI32_DWR      => MI32_DWR,
      MI32_ADDR     => MI32_ADDR,
      MI32_RD       => MI32_RD,
      MI32_WR       => MI32_WR, 
      MI32_BE       => MI32_BE,
      MI32_DRD      => MI32_DRD,
      MI32_ARDY     => MI32_ARDY,
      MI32_DRDY     => MI32_DRDY
   );

   -- ------------------------------------------------------------------------
   --                              NetCOPE Adder
   -- ------------------------------------------------------------------------

   fl_netcope_adder_in_data       <= fl_ver_core_tx_data;
   fl_netcope_adder_in_rem        <= fl_ver_core_tx_rem;
   fl_netcope_adder_in_sof_n      <= fl_ver_core_tx_sof_n;
   fl_netcope_adder_in_sop_n      <= fl_ver_core_tx_sop_n;
   fl_netcope_adder_in_eop_n      <= fl_ver_core_tx_eop_n;
   fl_netcope_adder_in_eof_n      <= fl_ver_core_tx_eof_n;
   fl_netcope_adder_in_src_rdy_n  <= fl_ver_core_tx_src_rdy_n;
   fl_ver_core_tx_dst_rdy_n       <= fl_netcope_adder_in_dst_rdy_n;

   netcope_adder_i: entity work.FL_NETCOPE_ADDER
   generic map(
      DATA_WIDTH => DATA_WIDTH
   )
   port map(
      CLK           => CLK,
      RESET         => RESET,

      -- input interface
      RX_DATA       => fl_netcope_adder_in_data,
      RX_REM        => fl_netcope_adder_in_rem,
      RX_SOF_N      => fl_netcope_adder_in_sof_n,
      RX_SOP_N      => fl_netcope_adder_in_sop_n,
      RX_EOP_N      => fl_netcope_adder_in_eop_n,
      RX_EOF_N      => fl_netcope_adder_in_eof_n,
      RX_SRC_RDY_N  => fl_netcope_adder_in_src_rdy_n,
      RX_DST_RDY_N  => fl_netcope_adder_in_dst_rdy_n,

      -- output interface
      TX_DATA       => fl_netcope_adder_out_data,
      TX_REM        => fl_netcope_adder_out_rem,
      TX_SOF_N      => fl_netcope_adder_out_sof_n,
      TX_SOP_N      => fl_netcope_adder_out_sop_n,
      TX_EOP_N      => fl_netcope_adder_out_eop_n,
      TX_EOF_N      => fl_netcope_adder_out_eof_n,
      TX_SRC_RDY_N  => fl_netcope_adder_out_src_rdy_n,
      TX_DST_RDY_N  => fl_netcope_adder_out_dst_rdy_n
   );

   fl_output_data                  <= fl_netcope_adder_out_data;
   fl_output_rem                   <= fl_netcope_adder_out_rem;
   fl_output_sof_n                 <= fl_netcope_adder_out_sof_n;
   fl_output_sop_n                 <= fl_netcope_adder_out_sop_n;
   fl_output_eop_n                 <= fl_netcope_adder_out_eop_n;
   fl_output_eof_n                 <= fl_netcope_adder_out_eof_n;
   fl_output_src_rdy_n             <= fl_netcope_adder_out_src_rdy_n;
   fl_netcope_adder_out_dst_rdy_n  <= fl_output_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                          Mapping of outputs
   -- ------------------------------------------------------------------------

   TX_DATA              <= fl_output_data;
   TX_REM               <= fl_output_rem;
   TX_SOF_N             <= fl_output_sof_n;
   TX_SOP_N             <= fl_output_sop_n;
   TX_EOP_N             <= fl_output_eop_n;
   TX_EOF_N             <= fl_output_eof_n;
   TX_SRC_RDY_N         <= fl_output_src_rdy_n;
   fl_output_dst_rdy_n  <= TX_DST_RDY_N;

end architecture;
