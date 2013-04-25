-- verification_core.vhd: Architecture of verification core
-- Author(s): Martin Funiak - xfunia00(at)stud.fit.vutbr.cz
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- math package
--use work.math_pack.all; --??

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
   constant ENV_DATA_WIDTH  : integer := FL_DATA_WIDTH;
   constant DUT_DATA_WIDTH  : integer := CODIX_DATA_WIDTH;

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

   -- program driver - control signals   
   signal program_driver_in_halt      : std_logic;

   -- program driver - output - Codix interface
   signal program_driver_out_dbg      : std_logic;
   signal program_driver_out_d0       : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal program_driver_out_wa0      : std_logic_vector(18 downto 0);
   signal program_driver_out_we0      : std_logic;
   signal program_driver_out_wsc0     : std_logic_vector(2 downto 0);
   signal program_driver_out_wsi0     : std_logic_vector(1 downto 0);

   -- =======================================================================

   -- DUT - Codix input interface - write to memory
   signal dut_in_mem_dbg  : std_logic;
   signal dut_in_mem_d0   : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_in_mem_wa0  : std_logic_vector(18 downto 0);
   signal dut_in_mem_we0  : std_logic;
   signal dut_in_mem_wsc0 : std_logic_vector(2 downto 0);
   signal dut_in_mem_wsi0 : std_logic_vector(1 downto 0);

   -- DUT - Codix input interface - read from memory
   signal dut_in_mem_ra0  : std_logic_vector(18 downto 0);
   signal dut_in_mem_re0  : std_logic;
   signal dut_in_mem_rsc0 : std_logic_vector(2 downto 0);
   signal dut_in_mem_rsi0 : std_logic_vector(1 downto 0);

   -- DUT - Codix input interface - read from register file
   signal dut_in_regs_dbg : std_logic;
   signal dut_in_regs_ra0 : std_logic_vector(4 downto 0);
   signal dut_in_regs_re0 : std_logic;

   -- DUT - Codix port for interrupt request
   signal dut_in_irq      : std_logic;

   -- DUT - Codix output interface
   signal dut_out_mem_q0         : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_regs_q0        : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_error     : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_halt      : std_logic;
   signal dut_out_port_output    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_output_en : std_logic;

   -- =======================================================================

   -- halt monitor - input - Codix halt signal
   signal halt_monitor_in_halt   : std_logic;

   -- halt monitor - output - halt propagation and RST signal connected to Codix
   signal halt_monitor_out_halt  : std_logic;
   signal halt_monitor_out_rst_n : std_logic;

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

   -- register monitor - input - Codix interface
   signal register_monitor_in_halt  : std_logic;
   signal register_monitor_out_dbg  : std_logic;
   signal register_monitor_in_q0    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal register_monitor_out_ra0  : std_logic_vector(4 downto 0);
   signal register_monitor_out_re0  : std_logic;

   -- register monitor - output control signal
   signal register_monitor_out_done : std_logic;

   -- register monitor - output - FL interface
   signal register_monitor_out_data : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal register_monitor_out_rem  : std_logic_vector(2 downto 0);
   signal register_monitor_out_src_rdy_n : std_logic;
   signal register_monitor_in_dst_rdy_n  : std_logic;
   signal register_monitor_out_sop_n : std_logic;
   signal register_monitor_out_sof_n : std_logic;
   signal register_monitor_out_eop_n : std_logic;
   signal register_monitor_out_eof_n : std_logic;

   -- =======================================================================

   -- memory monitor - input - Codix interface
   signal memory_monitor_in_halt  : std_logic;
   signal memory_monitor_out_dbg  : std_logic;
   signal memory_monitor_in_q0    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal memory_monitor_out_ra0  : std_logic_vector(18 downto 0);
   signal memory_monitor_out_re0  : std_logic;
   signal memory_monitor_out_rsc0 : std_logic_vector(2 downto 0);
   signal memory_monitor_out_rsi0 : std_logic_vector(1 downto 0);

   -- memory monitor - output control signal
   signal memory_monitor_out_done : std_logic;

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

   -- framelink binder - control signals
   signal fl_binder_in_halt      : std_logic;
   signal fl_binder_in_regs_done : std_logic;
   signal fl_binder_in_mem_done  : std_logic;

   -- framelink binder - input interfaces
   -- PM - portout monitor
   signal fl_binder_in_pm_data : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal fl_binder_in_pm_rem  : std_logic_vector(2 downto 0);
   signal fl_binder_in_pm_src_rdy_n  : std_logic;
   signal fl_binder_out_pm_dst_rdy_n : std_logic;
   signal fl_binder_in_pm_sop_n : std_logic;
   signal fl_binder_in_pm_eop_n : std_logic;
   signal fl_binder_in_pm_sof_n : std_logic;
   signal fl_binder_in_pm_eof_n : std_logic;

   -- RM - register monitor
   signal fl_binder_in_rm_data : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal fl_binder_in_rm_rem  : std_logic_vector(2 downto 0);
   signal fl_binder_in_rm_src_rdy_n  : std_logic;
   signal fl_binder_out_rm_dst_rdy_n : std_logic;
   signal fl_binder_in_rm_sop_n : std_logic;
   signal fl_binder_in_rm_eop_n : std_logic;
   signal fl_binder_in_rm_sof_n : std_logic;
   signal fl_binder_in_rm_eof_n : std_logic;
  
   -- MM - memory monitor
   signal fl_binder_in_mm_data : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal fl_binder_in_mm_rem  : std_logic_vector(2 downto 0);
   signal fl_binder_in_mm_src_rdy_n  : std_logic;
   signal fl_binder_out_mm_dst_rdy_n : std_logic;
   signal fl_binder_in_mm_sop_n : std_logic;
   signal fl_binder_in_mm_eop_n : std_logic;
   signal fl_binder_in_mm_sof_n : std_logic;
   signal fl_binder_in_mm_eof_n : std_logic;

   -- framelink binder - output interface
   signal fl_binder_out_data : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal fl_binder_out_rem  : std_logic_vector(2 downto 0);
   signal fl_binder_out_src_rdy_n : std_logic;
   signal fl_binder_in_dst_rdy_n  : std_logic;
   signal fl_binder_out_sop_n : std_logic;
   signal fl_binder_out_eop_n : std_logic;
   signal fl_binder_out_sof_n : std_logic;
   signal fl_binder_out_eof_n : std_logic;

   -- =======================================================================

-- ==========================================================================
--                                   COMPONENTS
-- ==========================================================================

begin

   -- ------------------------------------------------------------------------
   --              Mapping of inputs (environment)
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

      -- input interface
      RX_DATA       => program_driver_in_data,
      RX_REM        => program_driver_in_rem,
      RX_SOF_N      => program_driver_in_sof_n,
      RX_SOP_N      => program_driver_in_sop_n,
      RX_EOP_N      => program_driver_in_eop_n,
      RX_EOF_N      => program_driver_in_eof_n,
      RX_SRC_RDY_N  => program_driver_in_src_rdy_n,
      RX_DST_RDY_N  => program_driver_in_dst_rdy_n,
      HALT          => program_driver_in_halt,

      -- output interface
      dbg_mode_mem      => program_driver_out_dbg,
      dbg_mode_mem_D0   => program_driver_out_d0,
      dbg_mode_mem_WA0  => program_driver_out_wa0,
      dbg_mode_mem_WE0  => program_driver_out_we0,
      dbg_mode_mem_WSC0 => program_driver_out_wsc0,
      dbg_mode_mem_WSI0 => program_driver_out_wsi0
   );

   -- ------------------------------------------------------------------------
   --              DUT - CODIX
   -- ------------------------------------------------------------------------
   dut_codix_i: entity work.codix_ca_t
   port map (
      CLK               => CLK,    -- clk for memory??
      RST               => RESET,  -- TODO - active in 0!

      dbg_mode_mem      => dut_in_mem_dbg,
      dbg_mode_mem_D0   => dut_in_mem_d0,
      dbg_mode_mem_WA0  => dut_in_mem_wa0,
      dbg_mode_mem_WE0  => dut_in_mem_we0,
      dbg_mode_mem_WSC0 => dut_in_mem_wsc0,
      dbg_mode_mem_WSI0 => dut_in_mem_wsi0,
      dbg_mode_mem_Q0   => dut_out_mem_q0,
      dbg_mode_mem_RA0  => dut_in_mem_ra0,
      dbg_mode_mem_RE0  => dut_in_mem_re0,
      dbg_mode_mem_RSI0 => dut_in_mem_rsi0,
      dbg_mode_mem_RSC0 => dut_in_mem_rsc0,
      dbg_mode_regs     => dut_in_regs_dbg,
      dbg_mode_regs_RA0 => dut_in_regs_ra0,
      dbg_mode_regs_RE0 => dut_in_regs_re0,
      irq               => dut_in_irq,

      port_halt         => dut_out_port_halt,
      port_output       => dut_out_port_output,
      port_output_en    => dut_out_port_output_en
   );

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - halt monitor
   -- ------------------------------------------------------------------------
   halt_monitor_i: entity work.HALT_MONITOR
   port map(
      -- input clock domain
      CLK       => CLK,
      RESET     => RESET,

      port_halt => halt_monitor_in_halt,
      HALT      => halt_monitor_out_halt,
      RST_n     => halt_monitor_out_rst_n 
   );

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - portout monitor
   -- ------------------------------------------------------------------------
   portout_monitor_i: entity work.PORTOUT_MONITOR
   generic map (
      IN_DATA_WIDTH  => CODIX_DATA_WIDTH,
      OUT_DATA_WIDTH => FL_DATA_WIDTH
   )
   port map (
      -- input clock domain
      CLK            => CLK,
      RESET          => RESET,

      -- inputs
      port_output    => portout_monitor_in_port_output,
      port_output_en => portout_monitor_in_port_output_en,

      -- outputs
      TX_DATA        => portout_monitor_out_data,
      TX_REM         => portout_monitor_out_rem,
      TX_SRC_RDY_N   => portout_monitor_out_src_rdy_n,
      TX_DST_RDY_N   => portout_monitor_in_dst_rdy_n,
      TX_SOP_N       => portout_monitor_out_sop_n,
      TX_EOP_N       => portout_monitor_out_eop_n,
      TX_SOF_N       => portout_monitor_out_sof_n,
      TX_EOF_N       => portout_monitor_out_eof_n
   );

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - register monitor
   -- ------------------------------------------------------------------------
   register_monitor_i: entity work.REGISTER_MONITOR
   generic map (
      IN_DATA_WIDTH     => CODIX_DATA_WIDTH,
      OUT_DATA_WIDTH    => FL_DATA_WIDTH
   )
   port map (
      -- input clock domain
      CLK          => CLK,
      RESET        => RESET,

      -- control signals
      DONE              => register_monitor_out_done,

      -- inputs
      dbg_mode_regs_Q0  => register_monitor_in_q0,
      TX_DST_RDY_N      => register_monitor_in_dst_rdy_n,
      HALT              => register_monitor_in_halt,

      -- outputs
      dbg_mode_regs      => register_monitor_out_dbg,
      dbg_mode_regs_RA0  => register_monitor_out_ra0,
      dbg_mode_regs_RE0  => register_monitor_out_re0,

      TX_DATA      => register_monitor_out_data,
      TX_REM       => register_monitor_out_rem,
      TX_SRC_RDY_N => register_monitor_out_src_rdy_n,
      TX_SOP_N     => register_monitor_out_sop_n,
      TX_EOP_N     => register_monitor_out_eop_n,
      TX_SOF_N     => register_monitor_out_sof_n,
      TX_EOF_N     => register_monitor_out_eof_n
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
      CLK               => CLK,
      RESET             => RESET,

      -- control signals
      DONE              => memory_monitor_out_done,

      -- inputs
      dbg_mode_mem_Q0   => memory_monitor_in_q0,
      TX_DST_RDY_N      => memory_monitor_in_dst_rdy_n,
      HALT              => memory_monitor_in_halt,

      -- outputs
      dbg_mode_mem      => memory_monitor_out_dbg,
      dbg_mode_mem_RA0  => memory_monitor_out_ra0,
      dbg_mode_mem_RE0  => memory_monitor_out_re0,
      dbg_mode_mem_RSC0 => memory_monitor_out_rsc0,
      dbg_mode_mem_RSI0 => memory_monitor_out_rsi0,

      TX_DATA           => memory_monitor_out_data,
      TX_REM            => memory_monitor_out_rem,
      TX_SRC_RDY_N      => memory_monitor_out_src_rdy_n,
      TX_SOP_N          => memory_monitor_out_sop_n,
      TX_EOP_N          => memory_monitor_out_eop_n,
      TX_SOF_N          => memory_monitor_out_sof_n,
      TX_EOF_N          => memory_monitor_out_eof_n
   );

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - framelink binder
   -- ------------------------------------------------------------------------
   fl_binder_i: entity work.FL_BINDER
   generic map (
      DATA_WIDTH    => FL_DATA_WIDTH
   )
   port map (
      -- input clock domain
      CLK          => CLK,
      RESET        => RESET,

      -- control signals
      HALT       => fl_binder_in_halt,
      REGS_DONE  => fl_binder_in_regs_done,
      MEM_DONE   => fl_binder_in_mem_done,
         
      -- input interfaces
      -- input framelink - PM - portout monitor
      PM_RX_DATA      => fl_binder_in_pm_data,
      PM_RX_REM       => fl_binder_in_pm_rem,
      PM_RX_SRC_RDY_N => fl_binder_in_pm_src_rdy_n,
      PM_RX_DST_RDY_N => fl_binder_out_pm_dst_rdy_n,
      PM_RX_SOP_N     => fl_binder_in_pm_sop_n,
      PM_RX_EOP_N     => fl_binder_in_pm_eop_n,
      PM_RX_SOF_N     => fl_binder_in_pm_sof_n,
      PM_RX_EOF_N     => fl_binder_in_pm_eof_n,

      -- input framelink - RM - register file monitor
      RM_RX_DATA      => fl_binder_in_rm_data,
      RM_RX_REM       => fl_binder_in_rm_rem,
      RM_RX_SRC_RDY_N => fl_binder_in_rm_src_rdy_n,
      RM_RX_DST_RDY_N => fl_binder_out_rm_dst_rdy_n,
      RM_RX_SOP_N     => fl_binder_in_rm_sop_n,
      RM_RX_EOP_N     => fl_binder_in_rm_eop_n,
      RM_RX_SOF_N     => fl_binder_in_rm_sof_n,
      RM_RX_EOF_N     => fl_binder_in_rm_eof_n,

      -- input framelink - MM - memory monitor
      MM_RX_DATA      => fl_binder_in_mm_data,
      MM_RX_REM       => fl_binder_in_mm_rem,
      MM_RX_SRC_RDY_N => fl_binder_in_mm_src_rdy_n,
      MM_RX_DST_RDY_N => fl_binder_out_mm_dst_rdy_n,
      MM_RX_SOP_N     => fl_binder_in_mm_sop_n,
      MM_RX_EOP_N     => fl_binder_in_mm_eop_n,
      MM_RX_SOF_N     => fl_binder_in_mm_sof_n,
      MM_RX_EOF_N     => fl_binder_in_mm_eof_n,

      -- output interface
      TX_DATA      => fl_binder_out_data,
      TX_REM       => fl_binder_out_rem,
      TX_SRC_RDY_N => fl_binder_out_src_rdy_n,
      TX_DST_RDY_N => fl_binder_in_dst_rdy_n,
      TX_SOP_N     => fl_binder_out_sop_n,
      TX_EOP_N     => fl_binder_out_eop_n,
      TX_SOF_N     => fl_binder_out_sof_n,
      TX_EOF_N     => fl_binder_out_eof_n
   );

   -- ------------------------------------------------------------------------
   --                          connection of components
   -- ------------------------------------------------------------------------

   -- =====  dut input signal mapping =====
   -- program driver -> dut
   dut_in_mem_dbg  <= program_driver_out_dbg; -- TODO! & memory_monitor_out_dbg;
   dut_in_mem_d0   <= program_driver_out_d0;
   dut_in_mem_wa0  <= program_driver_out_wa0;
   dut_in_mem_we0  <= program_driver_out_we0;
   dut_in_mem_wsc0 <= program_driver_out_wsc0;
   dut_in_mem_wsi0 <= program_driver_out_wsi0;

   -- memory monitor -> dut
   dut_in_mem_ra0  <= memory_monitor_out_ra0;
   dut_in_mem_re0  <= memory_monitor_out_re0;
   dut_in_mem_rsc0 <= memory_monitor_out_rsc0;
   dut_in_mem_rsi0 <= memory_monitor_out_rsi0;

   -- register monitor -> dut
   dut_in_regs_dbg <= register_monitor_out_dbg;
   dut_in_regs_ra0 <= register_monitor_out_ra0;
   dut_in_regs_re0 <= register_monitor_out_re0;

   -- =====  dut output signal mapping =====

   -- dut -> halt monitor
   halt_monitor_in_halt   <= dut_out_port_halt;

   -- dut -> portout monitor
   portout_monitor_in_port_output    <= dut_out_port_output;
   portout_monitor_in_port_output_en <= dut_out_port_output_en;

   -- dut -> register monitor
   register_monitor_in_q0 <= dut_out_regs_q0;

   -- dut -> memory monitor
   memory_monitor_in_halt <= dut_out_port_halt;
   memory_monitor_in_q0   <= dut_out_mem_q0;

   -- halt monitor connection
--   dut_in_rst             <= halt_monitor_out_rst_n; TODO!!

   -- halt monitor to other monitors
   register_monitor_in_halt <= halt_monitor_out_halt;
   memory_monitor_in_halt   <= halt_monitor_out_halt;
   fl_binder_in_halt        <= halt_monitor_out_halt;

   -- portout monitor to fl_binder
   fl_binder_in_pm_data      <= portout_monitor_out_data;
   fl_binder_in_pm_rem       <= portout_monitor_out_rem;
   fl_binder_in_pm_src_rdy_n <= portout_monitor_out_src_rdy_n;
   portout_monitor_in_dst_rdy_n <= fl_binder_out_pm_dst_rdy_n;
   fl_binder_in_pm_sop_n     <= portout_monitor_out_sop_n;
   fl_binder_in_pm_eop_n     <= portout_monitor_out_eop_n;
   fl_binder_in_pm_sof_n     <= portout_monitor_out_sof_n;
   fl_binder_in_pm_eof_n     <= portout_monitor_out_eof_n;

   -- register monitor to fl_binder
   fl_binder_in_rm_data      <= register_monitor_out_data;
   fl_binder_in_rm_rem       <= register_monitor_out_rem;
   fl_binder_in_rm_src_rdy_n <= register_monitor_out_src_rdy_n;
   register_monitor_in_dst_rdy_n <= fl_binder_out_rm_dst_rdy_n;
   fl_binder_in_rm_sop_n     <= register_monitor_out_sop_n;
   fl_binder_in_rm_eop_n     <= register_monitor_out_eop_n;
   fl_binder_in_rm_sof_n     <= register_monitor_out_sof_n;
   fl_binder_in_rm_eof_n     <= register_monitor_out_eof_n;
   fl_binder_in_regs_done    <= register_monitor_out_done;

   -- memory monitor to fl_binder
   fl_binder_in_mm_data      <= memory_monitor_out_data;
   fl_binder_in_mm_rem       <= memory_monitor_out_rem;
   fl_binder_in_mm_src_rdy_n <= memory_monitor_out_src_rdy_n;
   memory_monitor_in_dst_rdy_n <= fl_binder_out_mm_dst_rdy_n;
   fl_binder_in_mm_sop_n     <= memory_monitor_out_sop_n;
   fl_binder_in_mm_eop_n     <= memory_monitor_out_eop_n;
   fl_binder_in_mm_sof_n     <= memory_monitor_out_sof_n;
   fl_binder_in_mm_eof_n     <= memory_monitor_out_eof_n;
   fl_binder_in_mem_done     <= memory_monitor_out_done;

   -- ------------------------------------------------------------------------
   --                          Mapping of outputs
   -- ------------------------------------------------------------------------
   TX_DATA                <= fl_binder_out_data;
   TX_REM                 <= fl_binder_out_rem;
   TX_SOF_N               <= fl_binder_out_sof_n;
   TX_SOP_N               <= fl_binder_out_sop_n;
   TX_EOP_N               <= fl_binder_out_eop_n;
   TX_EOF_N               <= fl_binder_out_eof_n;
   TX_SRC_RDY_N           <= fl_binder_out_src_rdy_n;
   fl_binder_in_dst_rdy_n <= TX_DST_RDY_N;

   -- ------------------------------------------------------------------------
   --                              Clock gate
   -- ------------------------------------------------------------------------

--   clock_gate_i: entity work.clock_gate
--   port map (
--      CLK_IN        => CLK,
--      CLOCK_ENABLE  => clock_enable,
--      CLK_OUT       => clk_dut
--   );

   -- ------------------------------------------------------------------------
   --                              Reset gen
   -- ------------------------------------------------------------------------

--   reset_gen_i: entity work.reset_gen
--   generic map (
--      RESET_TIME    => 5
--   )
--   port map (
--      RX_CLK        => CLK,
--      RESET         => RESET,
--      TX_CLK        => clk_dut,
--      RESET_OUT     => reset_dut
--   );

end architecture;
