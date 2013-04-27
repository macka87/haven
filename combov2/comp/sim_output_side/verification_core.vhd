-- verification_core.vhd: Architecture of verification core
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- math package
--use work.math_pack.all;

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

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

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
   --                     Input interface mapping - Codix
   -- ------------------------------------------------------------------------

   dbg_mode_mem         <= memory_monitor_out_dbg;
   memory_monitor_in_q0 <= dbg_mode_mem_Q0;
   dbg_mode_mem_RA0     <= memory_monitor_out_ra0;
   dbg_mode_mem_RE0     <= memory_monitor_out_re0;
   dbg_mode_mem_RSC0    <= memory_monitor_out_rsc0;
   dbg_mode_mem_RSI0    <= memory_monitor_out_rsi0;
   
   dbg_mode_regs          <= register_monitor_out_dbg;
   register_monitor_in_q0 <= dbg_mode_regs_Q0;
   dbg_mode_regs_RA0      <= register_monitor_out_ra0;
   dbg_mode_regs_RE0      <= register_monitor_out_re0;
   
   halt_monitor_in_halt <= port_halt;
   
   portout_monitor_in_port_output <= port_output;
   portout_monitor_in_port_output_en <= port_output_en;

   -- ------------------------------------------------------------------------
   --              HW_SW_CODASIP - halt monitor
   -- ------------------------------------------------------------------------
   halt_monitor_i: entity work.HALT_MONITOR
   port map(
      -- input clock domain
      CLK        => CLK,
      RESET      => RESET,

      port_halt => halt_monitor_in_halt,
      HALT      => halt_monitor_out_halt
--      RST_n     => halt_monitor_out_rst_n???
      
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

         TX_DATA      => memory_monitor_out_data,
         TX_REM       => memory_monitor_out_rem,
         TX_SRC_RDY_N => memory_monitor_out_src_rdy_n,
         TX_SOP_N     => memory_monitor_out_sop_n,
         TX_EOP_N     => memory_monitor_out_eop_n,
         TX_SOF_N     => memory_monitor_out_sof_n,
         TX_EOF_N     => memory_monitor_out_eof_n

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
   --                          connection of components
   -- ------------------------------------------------------------------------

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

end architecture;
