-- verification_core.vhd: Architecture of verification core
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- math package
use work.math_pack.all;

-- HAVEN constants
use work.haven_const.all;

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
   constant FL_DATA_WIDTH   : integer := 64;
   constant CODIX_DATA_WIDTH: integer := 32;

   -- number of endpoints that transmit data to SW
   constant OUTPUT_ENDPOINTS : integer := 4;

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- program driver - input - Framelink
   signal program_driver_in_data      : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal program_driver_in_rem       : std_logic_vector(2 downto 0);
   signal program_driver_in_sof_n     : std_logic;
   signal program_driver_in_sop_n     : std_logic;
   signal program_driver_in_eop_n     : std_logic;
   signal program_driver_in_eof_n     : std_logic;
   signal program_driver_in_src_rdy_n : std_logic;
   signal program_driver_in_dst_rdy_n : std_logic;


   -- program driver - output - Codix interface
   signal program_driver_out_dbg      : std_logic;
   signal program_driver_out_d0       : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal program_driver_out_wa0      : std_logic_vector(18 downto 0);
   signal program_driver_out_we0      : std_logic;
   signal program_driver_out_wsc0     : std_logic_vector(2 downto 0);
   signal program_driver_out_wsi0     : std_logic_vector(1 downto 0);

   -- =======================================================================

   -- DUT - Codix input interface - write to memory
   signal dut_in_dbg  : std_logic;
   signal dut_in_d0   : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_in_wa0  : std_logic_vector(18 downto 0);
   signal dut_in_we0  : std_logic;
   signal dut_in_wsc0 : std_logic_vector(2 downto 0);
   signal dut_in_wsi0 : std_logic_vector(1 downto 0);

   -- DUT - Codix input interface - read from memory
   signal dut_in_ra0  : std_logic_vector(18 downto 0);
   signal dut_in_ra1  : std_logic_vector(18 downto 0);
   signal dut_in_re0  : std_logic;
   signal dut_in_re1  : std_logic;
   signal dut_in_rsc0 : std_logic_vector(2 downto 0);
   signal dut_in_rsc1 : std_logic_vector(2 downto 0);
   signal dut_in_rsi0 : std_logic_vector(1 downto 0);
   signal dut_in_rsi1 : std_logic_vector(1 downto 0);

   -- DUT - Codix output interface
   signal dut_out_q0  : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_q1  : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_error     : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_halt      : std_logic;
   signal dut_out_port_output    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_output_en : std_logic;

   -- =======================================================================

   -- memory monitor - input - Codix interface
   signal memory_monitor_in_halt  : std_logic;
   signal memory_monitor_out_dbg  : std_logic;
   signal memory_monitor_in_q0    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal memory_monitor_in_q1    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal memory_monitor_out_ra0  : std_logic_vector(18 downto 0);
   signal memory_monitor_out_ra1  : std_logic_vector(18 downto 0);
   signal memory_monitor_out_re0  : std_logic;
   signal memory_monitor_out_re1  : std_logic;
   signal memory_monitor_out_rsc0 : std_logic_vector(2 downto 0);
   signal memory_monitor_out_rsc1 : std_logic_vector(2 downto 0);
   signal memory_monitor_out_rsi0 : std_logic_vector(1 downto 0);
   signal memory_monitor_out_rsi1 : std_logic_vector(1 downto 0);

   -- memory monitor - output - FL interface
   signal memory_monitor_out_data : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal memory_monitor_out_rem  : std_logic_vector(2 downto 0);
   signal memory_monitor_out_src_rdy_n : std_logic;
   signal memory_monitor_in_dst_rdy_n  : std_logic;
   signal memory_monitor_out_sop_n : std_logic;
   signal memory_monitor_out_sof_n : std_logic;
   signal memory_monitor_out_eop_n : std_logic;
   signal memory_monitor_out_eof_n : std_logic;

   -- =======================================================================

   -- portout monitor - input - Codix interface
   signal portout_monitor_in_port_output    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal portout_monitor_in_port_output_en : std_logic;

   -- portout monitor - output - FL interface
   signal portout_monitor_out_data : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal portout_monitor_out_rem  : std_logic_vector(2 downto 0);
   signal portout_monitor_out_src_rdy_n : std_logic;
   signal portout_monitor_in_dst_rdy_n  : std_logic;
   signal portout_monitor_out_sop_n : std_logic;
   signal portout_monitor_out_sof_n : std_logic;
   signal portout_monitor_out_eop_n : std_logic;
   signal portout_monitor_out_eof_n : std_logic;

   -- =======================================================================

   -- halt monitor - input - Codix halt signal
   signal halt_monitor_in_halt   : std_logic;

   -- halt monitor - output - halt propagation and RST signal connected to Codix
   signal halt_monitor_out_halt  : std_logic;
   signal halt_monitor_out_rst_n : std_logic;


   -- =======================================================================

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

begin

   -- ------------------------------------------------------------------------
   --                           Mapping of inputs
   -- ------------------------------------------------------------------------
   program_driver_in_data      <= RX_DATA;
   program_driver_in_rem       <= RX_REM;
   program_driver_in_sof_n     <= RX_SOF_N;
   program_driver_in_sop_n     <= RX_SOP_N;
   program_driver_in_eop_n     <= RX_EOP_N;
   program_driver_in_eof_n     <= RX_EOF_N;
   program_driver_in_src_rdy_n <= RX_SRC_RDY_N;
   RX_DST_RDY_N  <= program_driver_in_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - program driver
   -- ------------------------------------------------------------------------
   program_driver_i: entity work.PROGRAM_DRIVER
   generic map(
      -- FrameLink data & Codix data width
      IN_DATA_WIDTH   => FL_DATA_WIDTH,
      OUT_DATA_WIDTH  => CODIX_DATA_WIDTH
   )
   port map(
      -- input clock domain
      CLK        => CLK,
      RESET      => RESET,

      -- output clock domain TODO?
      --OUT_CLK        => clk_dut,
      --OUT_RESET      => reset_dut,

      -- input interface
      RX_DATA       => program_driver_in_data,
      RX_REM        => program_driver_in_rem,
      RX_SOF_N      => program_driver_in_sof_n,
      RX_SOP_N      => program_driver_in_sop_n,
      RX_EOP_N      => program_driver_in_eop_n,
      RX_EOF_N      => program_driver_in_eof_n,
      RX_SRC_RDY_N  => program_driver_in_src_rdy_n,
      RX_DST_RDY_N  => program_driver_in_dst_rdy_n,

      -- output interface
      dbg_mode_mem  => program_driver_out_dbg,
      D0   => program_driver_out_d0,
      WA0  => program_driver_out_wa0,
      WE0  => program_driver_out_we0,
      WSC0 => program_driver_out_wsc0,
      WSI0 => program_driver_out_wsi0

   );

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - halt monitor
   -- ------------------------------------------------------------------------
   halt_monitor_i: entity work.HALT_MONITOR
   port map(
      -- input clock domain
      CLK        => CLK,
      RESET      => RESET,

      port_halt => halt_monitor_in_halt,
      HALT      => halt_monitor_out_halt,
      RST_n     => halt_monitor_out_rst_n
      
   );

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - memory monitor
   -- ------------------------------------------------------------------------
   memory_monitor_i: entity work.MEMORY_MONITOR
      generic map (
         IN_DATA_WIDTH     => CODIX_DATA_WIDTH,
         OUT_DATA_WIDTH    => FL_DATA_WIDTH
      )
      port map (
         -- input clock domain
         CLK          => CLK,
         RESET        => RESET,

         -- output clock domain TODO?
         --OUT_CLK        => clk,
         --OUT_RESET      => reset,

         -- inputs
         Q0           => memory_monitor_in_q0,
         Q1           => memory_monitor_in_q1,
         TX_DST_RDY_N => memory_monitor_in_dst_rdy_n,
         HALT         => memory_monitor_in_halt,

         -- outputs
         dbg_mode_mem => memory_monitor_out_dbg,
         RA0          => memory_monitor_out_ra0,
         RA1          => memory_monitor_out_ra1,
         RE0          => memory_monitor_out_re0,
         RE1          => memory_monitor_out_re1,
         RSC0         => memory_monitor_out_rsc0,
         RSC1         => memory_monitor_out_rsc1,
         RSI0         => memory_monitor_out_rsi0,
         RSI1         => memory_monitor_out_rsi1,

         TX_DATA      => memory_monitor_out_data,
         TX_REM       => memory_monitor_out_rem,
         TX_SRC_RDY_N => memory_monitor_out_src_rdy_n,
         TX_SOP_N     => memory_monitor_out_sop_n,
         TX_EOP_N     => memory_monitor_out_eop_n,
         TX_SOF_N     => memory_monitor_out_sof_n,
         TX_EOF_N     => memory_monitor_out_eof_n

      );

  
   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - portout monitor
   -- ------------------------------------------------------------------------
   portout_monitor_i: entity work.PORTOUT_MONITOR
      generic map (
         IN_DATA_WIDTH     => CODIX_DATA_WIDTH,
         OUT_DATA_WIDTH    => FL_DATA_WIDTH
      )
      port map (
         -- input clock domain
         CLK          => CLK,
         RESET        => RESET,

         -- output clock domain TODO?
         --OUT_CLK        => clk,
         --OUT_RESET      => reset,

         -- inputs
         port_output    => portout_monitor_in_port_output,
         port_output_en => portout_monitor_in_port_output_en,

         -- outputs
         TX_DATA      => portout_monitor_out_data,
         TX_REM       => portout_monitor_out_rem,
         TX_SRC_RDY_N => portout_monitor_out_src_rdy_n,
         TX_DST_RDY_N => portout_monitor_in_dst_rdy_n,
         TX_SOP_N     => portout_monitor_out_sop_n,
         TX_EOP_N     => portout_monitor_out_eop_n,
         TX_SOF_N     => portout_monitor_out_sof_n,
         TX_EOF_N     => portout_monitor_out_eof_n
      );

   -- ------------------------------------------------------------------------
   --                              DUT
   -- ------------------------------------------------------------------------
   dut_codix_i: entity work.codix_ca_t
   port map (
     CLK               => clk_dut,
     RST               => reset_dut,  -- TODO - active in 0!

     dbg_mode_mem      => dut_in_dbg,
     dbg_mode_mem_D0   => dut_in_d0,
     dbg_mode_mem_WA0  => dut_in_wa0,
     dbg_mode_mem_WE0  => dut_in_we0,
     dbg_mode_mem_WSC0 => dut_in_wsc0,
     dbg_mode_mem_WSI0 => dut_in_wsi0,
     port_halt         => dut_out_port_halt,
     port_output       => dut_out_port_output,
     port_output_en    => dut_out_port_output_en,

     -- TODO interface for memory component
     -- codix_ca_t.codix_ca_mem_t

--     CLK => , -- TODO! clk for memory
--     Q0  => dut_out_q0,
--     Q1  => dut_out_q1,
--     RA0 => dut_in_ra0,
--     RA1 => dut_in_ra1,
--     RE0 => dut_in_re0,
--     RE1 => dut_in_re1,
--     RSC0 => dut_in_rsc0,
--     RSC1 => dut_in_rsc1,
--     RSI0 => dut_in_rsi0,
--     RSI1 => dut_in_rsi1
   );


   -- ------------------------------------------------------------------------
   --                          connection of components
   -- ------------------------------------------------------------------------

   -- dut input signal mapping
   dut_in_dbg <= program_driver_out_dbg; -- TODO! & memory_monitor_out_dbg;
   dut_in_d0  <= program_driver_out_d0;
   dut_in_wa0 <= program_driver_out_wa0;
   dut_in_we0 <= program_driver_out_we0;
   dut_in_wsc0 <= program_driver_out_wsc0;
   dut_in_wsi0 <= program_driver_out_wsi0;
   dut_in_ra0 <= memory_monitor_out_ra0;
   dut_in_ra1 <= memory_monitor_out_ra1;
   dut_in_re0 <= memory_monitor_out_re0;
   dut_in_re1 <= memory_monitor_out_re1;
   dut_in_rsc0 <= memory_monitor_out_rsc0;
   dut_in_rsc1 <= memory_monitor_out_rsc1;
   dut_in_rsi0 <= memory_monitor_out_rsi0;
   dut_in_rsi1 <= memory_monitor_out_rsi1;

   -- dut output signal mapping
   memory_monitor_in_halt <= dut_out_port_halt;
   memory_monitor_in_q0   <= dut_out_q0;
   memory_monitor_in_q1   <= dut_out_q1;

   halt_monitor_in_halt   <= dut_out_port_halt;

   portout_monitor_in_port_output    <= dut_out_port_output;
   portout_monitor_in_port_output_en <= dut_out_port_output_en;

   -- halt monitor connection
   memory_monitor_in_halt <= halt_monitor_out_halt;
--   dut_in_rst             <= halt_monitor_out_rst_n; TODO!!

   -- ------------------------------------------------------------------------
   --                          Mapping of outputs
   -- ------------------------------------------------------------------------
   TX_DATA                  <= memory_monitor_out_data;
   TX_REM                   <= memory_monitor_out_rem;
   TX_SOF_N                 <= memory_monitor_out_sof_n;
   TX_SOP_N                 <= memory_monitor_out_sop_n;
   TX_EOP_N                 <= memory_monitor_out_eop_n;
   TX_EOF_N                 <= memory_monitor_out_eof_n;
   TX_SRC_RDY_N             <= memory_monitor_out_src_rdy_n;
   memory_monitor_in_dst_rdy_n  <= TX_DST_RDY_N;

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

end architecture;
