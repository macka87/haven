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
   type codix_memory_type is array (0 to 131071) of std_logic_vector(0 to 7);

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
   signal program_driver_in_mem_done  : std_logic;
   signal program_driver_out_rst_n    : std_logic;

   -- program driver - output - Codix interface
   signal program_driver_out_dbg      : std_logic;
   signal program_driver_out_d0       : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal program_driver_out_wa0      : std_logic_vector(18 downto 0);
   signal program_driver_out_we0      : std_logic;
   signal program_driver_out_wsc0     : std_logic_vector(2 downto 0);
   signal program_driver_out_wsi0     : std_logic_vector(1 downto 0);

   -- =======================================================================

   -- DUT - memory signals
   signal dut_memory_0 : codix_memory_type;
   signal dut_memory_1 : codix_memory_type;
   signal dut_memory_2 : codix_memory_type;
   signal dut_memory_3 : codix_memory_type;

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

   -- DUT reset from program driver
   signal dut_in_rst_n : std_logic;
   -- DUT reset from outside
   signal dut_in_rst_n_OUT : std_logic;

   signal dut_in_clk      : std_logic;

   -- DUT - Codix output interface
   signal dut_out_mem_q0         : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_regs_q0        : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_error     : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_halt      : std_logic;
   signal dut_out_port_output    : std_logic_vector(CODIX_DATA_WIDTH-1 downto 0);
   signal dut_out_port_output_en : std_logic;

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
   dut_in_rst_n_OUT <= DUT_RST_N ;

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
      MEM_DONE      => program_driver_in_mem_done,
      OUT_RST_N     => program_driver_out_rst_n,

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
      CLK               => CLK,
      RST               => dut_in_rst_n,

      dbg_mode_mem      => dut_in_mem_dbg,
      dbg_mode_mem_D0   => dut_in_mem_d0,
      dbg_mode_mem_WA0  => dut_in_mem_wa0,
      dbg_mode_mem_WE0  => dut_in_mem_we0,
      dbg_mode_mem_WSC0 => dut_in_mem_wsc0,
      dbg_mode_mem_WSI0 => dut_in_mem_wsi0,

      dbg_mode_mem_Q0   => open,
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
   --                          connection of components
   -- ------------------------------------------------------------------------

   -- =====  dut input signal mapping =====
   -- program driver -> dut
   dut_in_mem_dbg  <= program_driver_out_dbg;
   dut_in_mem_d0   <= program_driver_out_d0;
   dut_in_mem_wa0  <= program_driver_out_wa0;
   dut_in_mem_we0  <= program_driver_out_we0;
   dut_in_mem_wsc0 <= program_driver_out_wsc0;
   dut_in_mem_wsi0 <= program_driver_out_wsi0;
   dut_in_rst_n    <= program_driver_out_rst_n and dut_in_rst_n_OUT;

   -- ------------------------------------------------------------------------
   --                          Mapping of outputs
   -- ------------------------------------------------------------------------

   port_error     <= dut_out_port_error;
   port_halt      <= dut_out_port_halt;
   port_output    <= dut_out_port_output;
   port_output_en <= dut_out_port_output_en;

end architecture;
