-- verification_core_tb.vhd: Verification core testbench
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_textio.all;
use std.textio.all;

library work;
use work.math_pack.all;
use work.fl_sim_oper.all;
use work.fl_bfm_pkg.all;
use work.fl_bfm_rdy_pkg.all;

-- HAVEN constants
use work.haven_const.all;

entity testbench is
end entity;

architecture test of testbench is

   -- ------------------------------------------------------------------------
   --                                Constants
   -- ------------------------------------------------------------------------

   -- data width of the verification core
   constant FL_DATA_WIDTH    : integer := 64;
   constant CODIX_DATA_WIDTH : integer := 32;

   -- duration of reset
   constant RESET_TIME  : time := 100 ns;
   -- clock period
   constant CLK_PERIOD  : time := 10 ns;

   -- ------------------------------------------------------------------------
   --                                 Signals
   -- ------------------------------------------------------------------------

   -- common signals
   signal clk           : std_logic;
   signal reset         : std_logic;

   -- input interface - codix
   signal dbg_mode_mem      : std_logic;
   signal dbg_mode_mem_Q0   : std_logic_vector(31 downto 0);
   signal dbg_mode_mem_RA0  : std_logic_vector(18 downto 0);
   signal dbg_mode_mem_RE0  : std_logic;
   signal dbg_mode_mem_RSC0 : std_logic_vector(2 downto 0);
   signal dbg_mode_mem_RSI0 : std_logic_vector(1 downto 0);
   signal dbg_mode_regs     : std_logic;
   signal dbg_mode_regs_Q0  : std_logic_vector(31 downto 0);
   signal dbg_mode_regs_RA0 : std_logic_vector(4 downto 0);
   signal dbg_mode_regs_RE0 : std_logic;
   signal port_halt         : std_logic;
   signal port_output       : std_logic_vector(31 downto 0);
   signal port_output_en    : std_logic;

   -- output FrameLink
   signal tx_data       : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal tx_rem        : std_logic_vector(2 downto 0);
   signal tx_sof_n      : std_logic;
   signal tx_eof_n      : std_logic;
   signal tx_sop_n      : std_logic;
   signal tx_eop_n      : std_logic;
   signal tx_src_rdy_n  : std_logic;
   signal tx_dst_rdy_n  : std_logic;

begin

   -- -----------------------------------------------------------------------
   --                             Unit under test
   -- -----------------------------------------------------------------------
   uut: entity work.verification_core
   generic map(
      -- data width 
      FL_DATA_WIDTH      => FL_DATA_WIDTH,
      CODIX_DATA_WIDTH   => CODIX_DATA_WIDTH
   )
   port map(
      CLK            => clk,
      RESET          => reset,

      -- input interface
      dbg_mode_mem      => dbg_mode_mem,
      dbg_mode_mem_Q0   => dbg_mode_mem_Q0,
      dbg_mode_mem_RA0  => dbg_mode_mem_RA0,
      dbg_mode_mem_RE0  => dbg_mode_mem_RE0,
      dbg_mode_mem_RSC0 => dbg_mode_mem_RSC0,
      dbg_mode_mem_RSI0 => dbg_mode_mem_RSI0,
      dbg_mode_regs     => dbg_mode_regs,
      dbg_mode_regs_Q0  => dbg_mode_regs_Q0,
      dbg_mode_regs_RA0 => dbg_mode_regs_RA0,
      dbg_mode_regs_RE0 => dbg_mode_regs_RE0,
      port_halt         => port_halt,
      port_output       => port_output,
      port_output_en    => port_output_en,
 
      -- output interface
      TX_DATA        => tx_data,
      TX_REM         => tx_rem,
      TX_SOF_N       => tx_sof_n,
      TX_EOF_N       => tx_eof_n,
      TX_SOP_N       => tx_sop_n,
      TX_EOP_N       => tx_eop_n,
      TX_SRC_RDY_N   => tx_src_rdy_n,
      TX_DST_RDY_N   => tx_dst_rdy_n
      
   ); 

   -- -------------------------------------------------------------------------
   --                           CLOCKs & RESETs
   -- -------------------------------------------------------------------------
   resetp: process
   begin
      reset <= '1', '0' after RESET_TIME;
      wait;
   end process;

   clk_genp: process
   begin
      clk  <= '1';
      wait for CLK_PERIOD/2;
      clk  <= '0';
      wait for CLK_PERIOD/2;
   end process;

   -- -----------------------------------------------------------------------
   --                                 Test
   -- -----------------------------------------------------------------------
   tb : process
      file mem_content : text open READ_MODE is "input/mem_content";
      file reg_content : text open READ_MODE is "input/reg_content";

      variable my_input_line : line;
      variable my_input_slv  : std_logic_vector(31 downto 0);

   begin


      -- initialization
      dbg_mode_mem_Q0   <= X"00000000";
      dbg_mode_regs_Q0  <= X"00000000";
      port_halt         <= '0';
      port_output       <= X"00000000";
      port_output_en    <= '0'; 

      tx_dst_rdy_n <= '0';     

      wait for RESET_TIME;

      report "========== start of output simulation ==========";

      -- nothing happens - DUT computation
      wait until rising_edge(clk);

      -- portout information
      wait until rising_edge(clk);

      port_output_en <= '1';
      port_output <= X"AABBCCDD";

      -- halt signal
      wait until rising_edge(clk);
      port_output_en <= '0';
      port_halt <= '1';

      -- register file transfer - loop
      -- ================ loop ==================
      while not endfile(reg_content) loop
        readline(reg_content, my_input_line);
        read(my_input_line, my_input_slv);
        dbg_mode_regs_Q0 <= my_input_slv;
        wait until rising_edge(clk) and dbg_mode_regs_RE0 = '1';
        port_halt <= '0';
      end loop;
      -- ============= end of loop ===============

      -- memory content transfer - loop
      -- ================ loop ==================
      while not endfile(mem_content) loop
        wait until rising_edge(clk) and dbg_mode_mem_RE0 = '1';
        readline(mem_content, my_input_line);
        read(my_input_line, my_input_slv);
        dbg_mode_mem_Q0 <= my_input_slv;
      end loop;
      -- ============= end of loop ===============
      
      report "========== end of output simulation ==========";

      wait;
   end process;

end architecture;
