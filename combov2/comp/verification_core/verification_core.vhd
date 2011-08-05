-- verification_core.vhd: Architecture of verification core
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
architecture arch of verification_core is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================
   constant ENV_DATA_WIDTH  : integer := DATA_WIDTH;
   constant DUT_DATA_WIDTH  : integer := DATA_WIDTH;
   --constant DUT_DATA_WIDTH  : integer := 128;

   -- number of endpoints that transmit data to SW
   constant OUTPUT_ENDPOINTS : integer := 2;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- FrameLink input driver input
   signal fl_hw_driver_rx_data       : std_logic_vector(ENV_DATA_WIDTH-1 downto 0);
   signal fl_hw_driver_rx_rem        : std_logic_vector(log2(ENV_DATA_WIDTH/8)-1 downto 0);
   signal fl_hw_driver_rx_sof_n      : std_logic;
   signal fl_hw_driver_rx_sop_n      : std_logic;
   signal fl_hw_driver_rx_eop_n      : std_logic;
   signal fl_hw_driver_rx_eof_n      : std_logic;
   signal fl_hw_driver_rx_src_rdy_n  : std_logic;
   signal fl_hw_driver_rx_dst_rdy_n  : std_logic;

   -- FrameLink input driver output
   signal fl_hw_driver_tx_data      : std_logic_vector(DUT_DATA_WIDTH-1 downto 0);
   signal fl_hw_driver_tx_rem       : std_logic_vector(log2(DUT_DATA_WIDTH/8)-1 downto 0);
   signal fl_hw_driver_tx_sof_n     : std_logic;
   signal fl_hw_driver_tx_sop_n     : std_logic;
   signal fl_hw_driver_tx_eop_n     : std_logic;
   signal fl_hw_driver_tx_eof_n     : std_logic;
   signal fl_hw_driver_tx_src_rdy_n : std_logic;
   signal fl_hw_driver_tx_dst_rdy_n : std_logic;

   signal fl_hw_driver_output_ready : std_logic;

   -- DUT input
   signal dut_in_data        : std_logic_vector(DUT_DATA_WIDTH-1 downto 0);
   signal dut_in_rem         : std_logic_vector(log2(DUT_DATA_WIDTH/8)-1 downto 0);
   signal dut_in_sof_n       : std_logic;
   signal dut_in_sop_n       : std_logic;
   signal dut_in_eop_n       : std_logic;
   signal dut_in_eof_n       : std_logic;
   signal dut_in_src_rdy_n   : std_logic;
   signal dut_in_dst_rdy_n   : std_logic;

   -- DUT output
   signal dut_out_data       : std_logic_vector(DUT_DATA_WIDTH-1 downto 0);
   signal dut_out_rem        : std_logic_vector(log2(DUT_DATA_WIDTH/8)-1 downto 0);
   signal dut_out_sof_n      : std_logic;
   signal dut_out_sop_n      : std_logic;
   signal dut_out_eop_n      : std_logic;
   signal dut_out_eof_n      : std_logic;
   signal dut_out_src_rdy_n  : std_logic;
   signal dut_out_dst_rdy_n  : std_logic;

   -- FrameLink HW monitor input
   signal fl_hw_monitor_rx_data      : std_logic_vector(DUT_DATA_WIDTH-1 downto 0);
   signal fl_hw_monitor_rx_rem       : std_logic_vector(log2(DUT_DATA_WIDTH/8)-1 downto 0);
   signal fl_hw_monitor_rx_sof_n     : std_logic;
   signal fl_hw_monitor_rx_sop_n     : std_logic;
   signal fl_hw_monitor_rx_eop_n     : std_logic;
   signal fl_hw_monitor_rx_eof_n     : std_logic;
   signal fl_hw_monitor_rx_src_rdy_n : std_logic;
   signal fl_hw_monitor_rx_dst_rdy_n : std_logic;

   -- FrameLink HW monitor output
   signal fl_hw_monitor_tx_data     : std_logic_vector(ENV_DATA_WIDTH-1 downto 0);
   signal fl_hw_monitor_tx_rem      : std_logic_vector(log2(ENV_DATA_WIDTH/8)-1 downto 0);
   signal fl_hw_monitor_tx_sof_n    : std_logic;
   signal fl_hw_monitor_tx_sop_n    : std_logic;
   signal fl_hw_monitor_tx_eop_n    : std_logic;
   signal fl_hw_monitor_tx_eof_n    : std_logic;
   signal fl_hw_monitor_tx_src_rdy_n: std_logic;
   signal fl_hw_monitor_tx_dst_rdy_n: std_logic;

   signal fl_hw_monitor_output_ready    : std_logic;

   -- FrameLink Validity Checker output
   signal fl_val_checker_tx_data        : std_logic_vector(ENV_DATA_WIDTH-1 downto 0);
   signal fl_val_checker_tx_rem         : std_logic_vector(log2(ENV_DATA_WIDTH/8)-1 downto 0);
   signal fl_val_checker_tx_sof_n       : std_logic;
   signal fl_val_checker_tx_sop_n       : std_logic;
   signal fl_val_checker_tx_eop_n       : std_logic;
   signal fl_val_checker_tx_eof_n       : std_logic;
   signal fl_val_checker_tx_src_rdy_n   : std_logic;
   signal fl_val_checker_tx_dst_rdy_n   : std_logic;

   signal fl_val_checker_output_ready   : std_logic;

   -- FrameLink Binder input
   signal fl_binder_in_data     : std_logic_vector(OUTPUT_ENDPOINTS*ENV_DATA_WIDTH-1 downto 0);
   signal fl_binder_in_rem      : std_logic_vector(OUTPUT_ENDPOINTS*log2(ENV_DATA_WIDTH/8)-1 downto 0);
   signal fl_binder_in_sof_n    : std_logic_vector(OUTPUT_ENDPOINTS-1 downto 0);
   signal fl_binder_in_sop_n    : std_logic_vector(OUTPUT_ENDPOINTS-1 downto 0);
   signal fl_binder_in_eop_n    : std_logic_vector(OUTPUT_ENDPOINTS-1 downto 0);
   signal fl_binder_in_eof_n    : std_logic_vector(OUTPUT_ENDPOINTS-1 downto 0);
   signal fl_binder_in_src_rdy_n: std_logic_vector(OUTPUT_ENDPOINTS-1 downto 0);
   signal fl_binder_in_dst_rdy_n: std_logic_vector(OUTPUT_ENDPOINTS-1 downto 0);

   -- FrameLink Binder output
   signal fl_binder_out_data        : std_logic_vector(ENV_DATA_WIDTH-1 downto 0);
   signal fl_binder_out_rem         : std_logic_vector(log2(ENV_DATA_WIDTH/8)-1 downto 0);
   signal fl_binder_out_sof_n       : std_logic;
   signal fl_binder_out_sop_n       : std_logic;
   signal fl_binder_out_eop_n       : std_logic;
   signal fl_binder_out_eof_n       : std_logic;
   signal fl_binder_out_src_rdy_n   : std_logic;
   signal fl_binder_out_dst_rdy_n   : std_logic;

   -- FrameLink NetCOPE Adder component input
   signal fl_netcope_adder_in_data      : std_logic_vector(ENV_DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_in_rem       : std_logic_vector(log2(ENV_DATA_WIDTH/8)-1 downto 0);
   signal fl_netcope_adder_in_sof_n     : std_logic;
   signal fl_netcope_adder_in_sop_n     : std_logic;
   signal fl_netcope_adder_in_eop_n     : std_logic;
   signal fl_netcope_adder_in_eof_n     : std_logic;
   signal fl_netcope_adder_in_src_rdy_n : std_logic;
   signal fl_netcope_adder_in_dst_rdy_n : std_logic;

   -- FrameLink NetCOPE Adder component output
   signal fl_netcope_adder_out_data     : std_logic_vector(ENV_DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_out_rem      : std_logic_vector(log2(ENV_DATA_WIDTH/8)-1 downto 0);
   signal fl_netcope_adder_out_sof_n    : std_logic;
   signal fl_netcope_adder_out_sop_n    : std_logic;
   signal fl_netcope_adder_out_eop_n    : std_logic;
   signal fl_netcope_adder_out_eof_n    : std_logic;
   signal fl_netcope_adder_out_src_rdy_n: std_logic;
   signal fl_netcope_adder_out_dst_rdy_n: std_logic;


   signal output_ready_all       : std_logic;

   -- clock gate signals
   signal clock_enable           : std_logic;
   signal clk_dut                : std_logic;

   -- reset for DUT
   signal reset_dut              : std_logic;

   -- clock enable register
   signal reg_clock_enable       : std_logic;

-- ==========================================================================
--                                   COMPONENTS
-- ==========================================================================

   component icon3
     PORT (
       CONTROL0 : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0);
       CONTROL1 : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0);
       CONTROL2 : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0));

   end component;

   component ila73
     PORT (
       CONTROL : INOUT STD_LOGIC_VECTOR(35 DOWNTO 0);
       CLK : IN STD_LOGIC;
       TRIG0 : IN STD_LOGIC_VECTOR(72 DOWNTO 0));

   end component;

   signal ila0_control   : std_logic_vector(35 downto 0);
   signal ila1_control   : std_logic_vector(35 downto 0);
   signal ila2_control   : std_logic_vector(35 downto 0);
   signal ila0_trig0     : std_logic_vector(72 downto 0);
   signal ila1_trig0     : std_logic_vector(72 downto 0);
   signal ila2_trig0     : std_logic_vector(72 downto 0);

begin
 
   -- ------------------------------------------------------------------------
   --                           Mapping of inputs
   -- ------------------------------------------------------------------------
   fl_hw_driver_rx_data       <= RX_DATA;
   fl_hw_driver_rx_rem        <= RX_REM;
   fl_hw_driver_rx_sof_n      <= RX_SOF_N;
   fl_hw_driver_rx_sop_n      <= RX_SOP_N;
   fl_hw_driver_rx_eop_n      <= RX_EOP_N;
   fl_hw_driver_rx_eof_n      <= RX_EOF_N;
   fl_hw_driver_rx_src_rdy_n  <= RX_SRC_RDY_N;
   RX_DST_RDY_N  <= fl_hw_driver_rx_dst_rdy_n;


   -- ------------------------------------------------------------------------
   --                        Input FrameLink Driver
   -- ------------------------------------------------------------------------
   fl_hw_driver_i: entity work.FL_HW_DRIVER
   generic map(
      -- FrameLink data width
      IN_DATA_WIDTH   => ENV_DATA_WIDTH,
      OUT_DATA_WIDTH  => DUT_DATA_WIDTH
   )
   port map(
      RESET         => RESET,

      -- input clock domain
      RX_CLK        => CLK,

      -- output clock domain
      TX_CLK        => clk_dut,

      -- input interface
      RX_DATA       => fl_hw_driver_rx_data,
      RX_REM        => fl_hw_driver_rx_rem,
      RX_SOF_N      => fl_hw_driver_rx_sof_n,
      RX_SOP_N      => fl_hw_driver_rx_sop_n,
      RX_EOP_N      => fl_hw_driver_rx_eop_n,
      RX_EOF_N      => fl_hw_driver_rx_eof_n,
      RX_SRC_RDY_N  => fl_hw_driver_rx_src_rdy_n, 
      RX_DST_RDY_N  => fl_hw_driver_rx_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => fl_hw_driver_tx_data,
      TX_REM        => fl_hw_driver_tx_rem,
      TX_SOF_N      => fl_hw_driver_tx_sof_n,
      TX_SOP_N      => fl_hw_driver_tx_sop_n,
      TX_EOP_N      => fl_hw_driver_tx_eop_n,
      TX_EOF_N      => fl_hw_driver_tx_eof_n,
      TX_SRC_RDY_N  => fl_hw_driver_tx_src_rdy_n,
      TX_DST_RDY_N  => fl_hw_driver_tx_dst_rdy_n,

      OUTPUT_READY  => fl_hw_driver_output_ready
   );

   dut_in_data                <= fl_hw_driver_tx_data;
   dut_in_rem                 <= fl_hw_driver_tx_rem;
   dut_in_sof_n               <= fl_hw_driver_tx_sof_n;
   dut_in_sop_n               <= fl_hw_driver_tx_sop_n;
   dut_in_eop_n               <= fl_hw_driver_tx_eop_n;
   dut_in_eof_n               <= fl_hw_driver_tx_eof_n;
   dut_in_src_rdy_n           <= fl_hw_driver_tx_src_rdy_n;
   fl_hw_driver_tx_dst_rdy_n  <= dut_in_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                              DUT
   -- ------------------------------------------------------------------------
--   dut_i: entity work.fl_fifo
--   generic map(
--      DATA_WIDTH  => DUT_DATA_WIDTH,
--      USE_BRAMS   => false,
--      ITEMS       => 16,
--      PARTS       => 1
--   )
--   dut_i: entity work.HGEN_VER_COVER
   dut_i: entity work.ERRONEOUS_FL_FIFO
   generic map(
      DATA_WIDTH  => DUT_DATA_WIDTH,
      ITEMS => 16
   )
   port map(
      CLK           => clk_dut,
      RESET         => reset_dut,

      -- input interface
      RX_DATA       => dut_in_data,
      RX_REM        => dut_in_rem,
      RX_SOF_N      => dut_in_sof_n,
      RX_SOP_N      => dut_in_sop_n,
      RX_EOP_N      => dut_in_eop_n,
      RX_EOF_N      => dut_in_eof_n,
      RX_SRC_RDY_N  => dut_in_src_rdy_n, 
      RX_DST_RDY_N  => dut_in_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => dut_out_data,
      TX_REM        => dut_out_rem,
      TX_SOF_N      => dut_out_sof_n,
      TX_SOP_N      => dut_out_sop_n,
      TX_EOP_N      => dut_out_eop_n,
      TX_EOF_N      => dut_out_eof_n,
      TX_SRC_RDY_N  => dut_out_src_rdy_n,
      TX_DST_RDY_N  => dut_out_dst_rdy_n
   );

icon_i : icon3
  port map (
    CONTROL0 => ila0_control,
    CONTROL1 => ila1_control,
    CONTROL2 => ila2_control);

   ila0_trig0(0)            <= dut_in_src_rdy_n;
   ila0_trig0(1)            <= dut_in_dst_rdy_n;
   ila0_trig0(2)            <= dut_in_sof_n;
   ila0_trig0(3)            <= dut_in_sop_n;
   ila0_trig0(4)            <= dut_in_eof_n;
   ila0_trig0(5)            <= dut_in_eop_n;
   ila0_trig0(8 downto 6)   <= dut_in_rem;
   ila0_trig0(72 downto 9)  <= dut_in_data;

   ila0_i : ila73
   port map (
      CONTROL => ila0_control,
      CLK => clk_dut,
      TRIG0 => ila0_trig0
   );

   ila1_trig0(0)            <= dut_out_src_rdy_n;
   ila1_trig0(1)            <= dut_out_dst_rdy_n;
   ila1_trig0(2)            <= dut_out_sof_n;
   ila1_trig0(3)            <= dut_out_sop_n;
   ila1_trig0(4)            <= dut_out_eof_n;
   ila1_trig0(5)            <= dut_out_eop_n;
   ila1_trig0(8 downto 6)   <= dut_out_rem;
   ila1_trig0(72 downto 9)  <= dut_out_data;

   ila1_i : ila73
   port map (
      CONTROL => ila1_control,
      CLK => clk_dut,
      TRIG0 => ila1_trig0
   );

   ila2_trig0(0)            <= fl_netcope_adder_out_src_rdy_n;
   ila2_trig0(1)            <= fl_netcope_adder_out_dst_rdy_n;
   ila2_trig0(2)            <= fl_netcope_adder_out_sof_n;
   ila2_trig0(3)            <= fl_netcope_adder_out_sop_n;
   ila2_trig0(4)            <= fl_netcope_adder_out_eof_n;
   ila2_trig0(5)            <= fl_netcope_adder_out_eop_n;
   ila2_trig0(8 downto 6)   <= fl_netcope_adder_out_rem;
   ila2_trig0(72 downto 9)  <= fl_netcope_adder_out_data;

   ila2_i : ila73
   port map (
      CONTROL => ila2_control,
      CLK => CLK,
      TRIG0 => ila2_trig0
   );

   fl_hw_monitor_rx_data       <= dut_out_data;
   fl_hw_monitor_rx_rem        <= dut_out_rem;
   fl_hw_monitor_rx_sof_n      <= dut_out_sof_n;
   fl_hw_monitor_rx_sop_n      <= dut_out_sop_n;
   fl_hw_monitor_rx_eop_n      <= dut_out_eop_n;
   fl_hw_monitor_rx_eof_n      <= dut_out_eof_n;
   fl_hw_monitor_rx_src_rdy_n  <= dut_out_src_rdy_n;
   dut_out_dst_rdy_n           <= fl_hw_monitor_rx_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                        Output FrameLink Monitor
   -- ------------------------------------------------------------------------
-- NOTE: uncomment lines labelled "-- smart --" in order to use smart monitor
-- smart --   fl_hw_monitor_i: entity work.FL_HW_MONITOR
  fl_hw_monitor_i: entity work.FL_HW_MONITOR_SMART
   generic map(
      -- FrameLink data width
-- smart --      IN_DATA_WIDTH   => DUT_DATA_WIDTH,
-- smart --      OUT_DATA_WIDTH  => ENV_DATA_WIDTH
     IN_DATA_WIDTH   => DUT_DATA_WIDTH,
     OUT_DATA_WIDTH  => ENV_DATA_WIDTH,
     ENDPOINT_ID     => 136   -- 88 hexa
   )
   port map(
      RESET         => RESET,

      -- input clock domain
      RX_CLK        => clk_dut,

      -- output clock domain
      TX_CLK        => CLK,

      -- input interface
      RX_DATA       => fl_hw_monitor_rx_data,
      RX_REM        => fl_hw_monitor_rx_rem,
      RX_SOF_N      => fl_hw_monitor_rx_sof_n,
      RX_SOP_N      => fl_hw_monitor_rx_sop_n,
      RX_EOP_N      => fl_hw_monitor_rx_eop_n,
      RX_EOF_N      => fl_hw_monitor_rx_eof_n,
      RX_SRC_RDY_N  => fl_hw_monitor_rx_src_rdy_n, 
      RX_DST_RDY_N  => fl_hw_monitor_rx_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => fl_hw_monitor_tx_data,
      TX_REM        => fl_hw_monitor_tx_rem,
      TX_SOF_N      => fl_hw_monitor_tx_sof_n,
      TX_SOP_N      => fl_hw_monitor_tx_sop_n,
      TX_EOP_N      => fl_hw_monitor_tx_eop_n,
      TX_EOF_N      => fl_hw_monitor_tx_eof_n,
      TX_SRC_RDY_N  => fl_hw_monitor_tx_src_rdy_n,
      TX_DST_RDY_N  => fl_hw_monitor_tx_dst_rdy_n,

      OUTPUT_READY  => fl_hw_monitor_output_ready
   );


   -- ------------------------------------------------------------------------
   --                    Output FrameLink Validity Checker
   -- ------------------------------------------------------------------------
  fl_val_checker_i: entity work.FL_VAL_CHECKER
   generic map(
      -- FrameLink data width
     OUT_DATA_WIDTH  => ENV_DATA_WIDTH,
     ENDPOINT_ID     => 170   -- AA hexa
   )
   port map(
      -- input clock domain
      PR_CLK         => clk_dut,
      PR_RESET       => reset_dut,

      -- input interface
      PR_SOF_N       => dut_out_sof_n,
      PR_SOP_N       => dut_out_sop_n,
      PR_EOP_N       => dut_out_eop_n,
      PR_EOF_N       => dut_out_eof_n,
      PR_SRC_RDY_N   => dut_out_src_rdy_n, 
      PR_DST_RDY_N   => dut_out_dst_rdy_n, 
      
      -- output clock domain
      OUT_CLK        => CLK,
      OUT_RESET      => RESET,

      -- output interface
      OUT_DATA       => fl_val_checker_tx_data,
      OUT_REM        => fl_val_checker_tx_rem,
      OUT_SOF_N      => fl_val_checker_tx_sof_n,
      OUT_SOP_N      => fl_val_checker_tx_sop_n,
      OUT_EOP_N      => fl_val_checker_tx_eop_n,
      OUT_EOF_N      => fl_val_checker_tx_eof_n,
      OUT_SRC_RDY_N  => fl_val_checker_tx_src_rdy_n,
      OUT_DST_RDY_N  => fl_val_checker_tx_dst_rdy_n,

      -- output ready signal
      OUTPUT_READY  => fl_val_checker_output_ready
   );

   -- FL_BINDER input mapping
   fl_binder_in_data       <= fl_val_checker_tx_data      & fl_hw_monitor_tx_data;
   fl_binder_in_rem        <= fl_val_checker_tx_rem       & fl_hw_monitor_tx_rem;
   fl_binder_in_sof_n      <= fl_val_checker_tx_sof_n     & fl_hw_monitor_tx_sof_n;
   fl_binder_in_sop_n      <= fl_val_checker_tx_sop_n     & fl_hw_monitor_tx_sop_n;
   fl_binder_in_eop_n      <= fl_val_checker_tx_eop_n     & fl_hw_monitor_tx_eop_n;
   fl_binder_in_eof_n      <= fl_val_checker_tx_eof_n     & fl_hw_monitor_tx_eof_n;
   fl_binder_in_src_rdy_n  <= fl_val_checker_tx_src_rdy_n & fl_hw_monitor_tx_src_rdy_n;
   fl_val_checker_tx_dst_rdy_n     <= fl_binder_in_dst_rdy_n(1);
   fl_hw_monitor_tx_dst_rdy_n      <= fl_binder_in_dst_rdy_n(0);

   -- ------------------------------------------------------------------------
   --                              FL_BINDER
   -- ------------------------------------------------------------------------
   binder_i: entity work.FL_BINDER
   generic map(
      INPUT_WIDTH   => ENV_DATA_WIDTH,
      INPUT_COUNT   => OUTPUT_ENDPOINTS,
      OUTPUT_WIDTH  => ENV_DATA_WIDTH,
      FRAME_PARTS   => 1,
      STUPID_BINDER => true
   )
   port map(
      CLK           => CLK,
      RESET         => RESET,

      -- input interface
      RX_DATA       => fl_binder_in_data,
      RX_REM        => fl_binder_in_rem,
      RX_SOF_N      => fl_binder_in_sof_n,
      RX_SOP_N      => fl_binder_in_sop_n,
      RX_EOP_N      => fl_binder_in_eop_n,
      RX_EOF_N      => fl_binder_in_eof_n,
      RX_SRC_RDY_N  => fl_binder_in_src_rdy_n,
      RX_DST_RDY_N  => fl_binder_in_dst_rdy_n,
      
      -- output interface
      TX_DATA       => fl_binder_out_data,
      TX_REM        => fl_binder_out_rem,
      TX_SOF_N      => fl_binder_out_sof_n,
      TX_SOP_N      => fl_binder_out_sop_n,
      TX_EOP_N      => fl_binder_out_eop_n,
      TX_EOF_N      => fl_binder_out_eof_n,
      TX_SRC_RDY_N  => fl_binder_out_src_rdy_n,
      TX_DST_RDY_N  => fl_binder_out_dst_rdy_n
   );


   -- NetCOPE Adder input mapping
   fl_netcope_adder_in_data       <= fl_binder_out_data;
   fl_netcope_adder_in_rem        <= fl_binder_out_rem;
   fl_netcope_adder_in_sof_n      <= fl_binder_out_sof_n;
   fl_netcope_adder_in_sop_n      <= fl_binder_out_sop_n;
   fl_netcope_adder_in_eop_n      <= fl_binder_out_eop_n;
   fl_netcope_adder_in_eof_n      <= fl_binder_out_eof_n;
   fl_netcope_adder_in_src_rdy_n  <= fl_binder_out_src_rdy_n;
   fl_binder_out_dst_rdy_n        <= fl_netcope_adder_in_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                              NetCOPE Adder
   -- ------------------------------------------------------------------------
   netcope_adder_i: entity work.FL_NETCOPE_ADDER
   generic map(
      DATA_WIDTH => ENV_DATA_WIDTH
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


   -- ------------------------------------------------------------------------
   --                          Mapping of outputs
   -- ------------------------------------------------------------------------
   TX_DATA       <= fl_netcope_adder_out_data;
   TX_REM        <= fl_netcope_adder_out_rem;
   TX_SOF_N      <= fl_netcope_adder_out_sof_n;
   TX_SOP_N      <= fl_netcope_adder_out_sop_n;
   TX_EOP_N      <= fl_netcope_adder_out_eop_n;
   TX_EOF_N      <= fl_netcope_adder_out_eof_n;
   TX_SRC_RDY_N  <= fl_netcope_adder_out_src_rdy_n;
   fl_netcope_adder_out_dst_rdy_n  <= TX_DST_RDY_N;


--   TX_DATA       <= RX_DATA;
--   TX_REM        <= RX_REM;
--   TX_SOF_N      <= RX_SOF_N;
--   TX_SOP_N      <= RX_SOP_N;
--   TX_EOP_N      <= RX_EOP_N;
--   TX_EOF_N      <= RX_EOF_N;
--   TX_SRC_RDY_N  <= RX_SRC_RDY_N;
--   RX_DST_RDY_N  <= TX_DST_RDY_N;

   -- ------------------------------------------------------------------------
   --                              Clock gate
   -- ------------------------------------------------------------------------

   clock_gate_i: entity work.clock_gate
   port map (
      CLK_IN        => CLK,
      CLOCK_ENABLE  => clock_enable,
      CLK_OUT       => clk_dut
   );

   -- ------------------------------------------------------------------------
   --                              Reset gen
   -- ------------------------------------------------------------------------

   reset_gen_i: entity work.reset_gen
   generic map (
      RESET_TIME    => 5
   )
   port map (
      RX_CLK        => CLK,
      RESET         => RESET,

      TX_CLK        => clk_dut,
      RESET_OUT     => reset_dut
   );

   -- ------------------------------------------------------------------------
   --                       Register for clock enable
   -- ------------------------------------------------------------------------

   reg_clock_enable_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_clock_enable <= '1';
         elsif (MI32_WR = '1') then
            reg_clock_enable <= MI32_DWR(0);
         end if;
      end if;
   end process;

   clock_enable <= reg_clock_enable AND (output_ready_all OR reset_dut)
      AND (NOT RESET);
   --clock_enable <= reg_clock_enable OR RESET;

   output_ready_all <= fl_hw_driver_output_ready AND
                       fl_hw_monitor_output_ready AND
                       fl_val_checker_output_ready;

   -- ------------------------------------------------------------------------
   --                            MI32 Connection
   -- ------------------------------------------------------------------------

   -- The address ready signal
   MI32_ARDY <= MI32_RD OR MI32_WR;

   -- The data ready signal
   MI32_DRDY <= MI32_RD; 

   -- output MI32 data
   MI32_DRD <= X"00011ACA";

end architecture;
