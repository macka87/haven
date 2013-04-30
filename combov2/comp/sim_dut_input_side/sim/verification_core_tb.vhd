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

   -- data width
   constant FL_DATA_WIDTH      : integer := 64;
   constant CODIX_DATA_WIDTH   : integer := 32; 

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

   -- input FrameLink
   signal rx_data       : std_logic_vector(FL_DATA_WIDTH-1 downto 0);
   signal rx_rem        : std_logic_vector(2 downto 0);
   signal rx_sof_n      : std_logic;
   signal rx_eof_n      : std_logic;
   signal rx_sop_n      : std_logic;
   signal rx_eop_n      : std_logic;
   signal rx_src_rdy_n  : std_logic;
   signal rx_dst_rdy_n  : std_logic;

   signal dut_in_out_rst_n : std_logic;

   -- output Codix interface
   signal port_error     : std_logic_vector(31 downto 0);
   signal port_halt      : std_logic;
   signal port_output    : std_logic_vector(31 downto 0);
   signal port_output_en : std_logic;

   -- Reverse function to change bit-order inside byte.
   function reverse( src: std_logic_vector ) return std_logic_vector is
     variable result: std_logic_vector( src'range );
     alias r_src: std_logic_vector( src'reverse_range ) is src;
     begin
       for ii in r_src'range loop
         result(ii) := r_src(ii);
        end loop;
       return result;
   end function;


begin

   -- -----------------------------------------------------------------------
   --                             Unit under test
   -- -----------------------------------------------------------------------
   uut: entity work.verification_core
   generic map(
      -- data width 
      FL_DATA_WIDTH      => FL_DATA_WIDTH,
      CODIX_DATA_WIDTH   => CODIX_DATA_WIDTH,
      -- the CORE_TYPE generic specifies the verified unit in the core
      CORE_TYPE          => core_fifo
   )
   port map(
      CLK            => clk,
      RESET          => reset,

      -- input interface
      RX_DATA        => rx_data,
      RX_REM         => rx_rem,
      RX_SOF_N       => rx_sof_n,
      RX_EOF_N       => rx_eof_n,
      RX_SOP_N       => rx_sop_n,
      RX_EOP_N       => rx_eop_n,
      RX_SRC_RDY_N   => rx_src_rdy_n,
      RX_DST_RDY_N   => rx_dst_rdy_n,

      DUT_RST_N   => dut_in_out_rst_n,

      -- output interface
      port_error     => port_error,
      port_halt      => port_halt,
      port_output    => port_output,
      port_output_en => port_output_en

   );

   -- -------------------------------------------------------------------------
   --                           CLOCKs & RESETs
   -- -------------------------------------------------------------------------
   resetp : process
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

      file my_input : text open READ_MODE is "input/input_program";
      variable my_line : line;
      variable my_input_line : line;
      variable my_input_slv  : std_logic_vector(63 downto 0);

   begin



      wait for RESET_TIME;

      dut_in_out_rst_n <= '1';

      report "========== start of core simulation ==========";

      wait until rising_edge(clk) and RX_DST_RDY_N = '0';

      -- start header
      RX_DATA <= X"0000000100000000";
      RX_REM  <= "111";
      RX_SOF_N <= '0';
      RX_EOF_N <= '0';
      RX_SOP_N <= '0';
      RX_EOP_N <= '0';
      RX_SRC_RDY_N <= '0';

      wait until rising_edge(clk) and RX_DST_RDY_N = '0';

      -- data packet - header
      RX_DATA <= X"0000000000000000";
      RX_REM  <= "111";
      RX_SOF_N <= '0';
      RX_EOF_N <= '1';
      RX_SOP_N <= '0';
      RX_EOP_N <= '1';
      RX_SRC_RDY_N <= '0';

      -- ================ loop ==================
      while not endfile(my_input) loop

        wait until rising_edge(clk) and RX_DST_RDY_N = '0';

        readline(my_input, my_input_line);
        read(my_input_line, my_input_slv);
        -- data packet - data
        RX_DATA <= reverse(my_input_slv(39 downto 32)) & reverse(my_input_slv(47 downto 40)) & reverse(my_input_slv(55 downto 48)) & reverse(my_input_slv(63 downto 56)) & reverse(my_input_slv(7 downto 0)) & reverse(my_input_slv(15 downto 8)) & reverse(my_input_slv(23 downto 16)) & reverse(my_input_slv(31 downto 24));

        RX_REM  <= "111";
        RX_SOF_N <= '1';
        RX_EOF_N <= '1';
        RX_SOP_N <= '1';
        RX_EOP_N <= '1';
        RX_SRC_RDY_N <= '0';

      end loop;
      -- ============= end of loop ===============
      
      wait until rising_edge(clk) and RX_DST_RDY_N = '0';

      -- data packet last line
      RX_DATA <= X"0000000000000000";
      RX_REM  <= "111";
      RX_SOF_N <= '1';
      RX_EOF_N <= '0';
      RX_SOP_N <= '1';
      RX_EOP_N <= '0';
      RX_SRC_RDY_N <= '0';

      wait until rising_edge(clk) and RX_DST_RDY_N = '0';

      -- stop header
      RX_DATA <= X"0000000400000000";
      RX_REM  <= "111";
      RX_SOF_N <= '0';
      RX_EOF_N <= '0';
      RX_SOP_N <= '0';
      RX_EOP_N <= '0';
      RX_SRC_RDY_N <= '0';

      wait until rising_edge(port_halt);

      wait until CLK'event;
      dut_in_out_rst_n <= '0';

      report "========== end of core simulation ==========";

      wait;
   end process;

end architecture;
