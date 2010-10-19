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

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- FrameLink input asynchronous FIFO input
   signal fl_input_asfifo_in_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_input_asfifo_in_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_input_asfifo_in_sof_n      : std_logic;
   signal fl_input_asfifo_in_sop_n      : std_logic;
   signal fl_input_asfifo_in_eop_n      : std_logic;
   signal fl_input_asfifo_in_eof_n      : std_logic;
   signal fl_input_asfifo_in_src_rdy_n  : std_logic;
   signal fl_input_asfifo_in_dst_rdy_n  : std_logic;

   -- FrameLink input asynchronous FIFO output
   signal fl_input_asfifo_out_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_input_asfifo_out_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_input_asfifo_out_sof_n     : std_logic;
   signal fl_input_asfifo_out_sop_n     : std_logic;
   signal fl_input_asfifo_out_eop_n     : std_logic;
   signal fl_input_asfifo_out_eof_n     : std_logic;
   signal fl_input_asfifo_out_src_rdy_n : std_logic;
   signal fl_input_asfifo_out_dst_rdy_n : std_logic;

   -- FrameLink shortener input
   signal fl_shortener_in_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_shortener_in_rem         : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_shortener_in_sof_n       : std_logic;
   signal fl_shortener_in_sop_n       : std_logic;
   signal fl_shortener_in_eop_n       : std_logic;
   signal fl_shortener_in_eof_n       : std_logic;
   signal fl_shortener_in_src_rdy_n   : std_logic;
   signal fl_shortener_in_dst_rdy_n   : std_logic;

   -- FrameLink shortener output
   signal fl_shortener_out_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_shortener_out_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_shortener_out_sof_n      : std_logic;
   signal fl_shortener_out_sop_n      : std_logic;
   signal fl_shortener_out_eop_n      : std_logic;
   signal fl_shortener_out_eof_n      : std_logic;
   signal fl_shortener_out_src_rdy_n  : std_logic;
   signal fl_shortener_out_dst_rdy_n  : std_logic;

   -- FrameLink output asynchronous FIFO input
   signal fl_output_asfifo_in_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_output_asfifo_in_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_output_asfifo_in_sof_n     : std_logic;
   signal fl_output_asfifo_in_sop_n     : std_logic;
   signal fl_output_asfifo_in_eop_n     : std_logic;
   signal fl_output_asfifo_in_eof_n     : std_logic;
   signal fl_output_asfifo_in_src_rdy_n : std_logic;
   signal fl_output_asfifo_in_dst_rdy_n : std_logic;

   -- FrameLink output asynchronous FIFO output
   signal fl_output_asfifo_out_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_output_asfifo_out_rem      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_output_asfifo_out_sof_n    : std_logic;
   signal fl_output_asfifo_out_sop_n    : std_logic;
   signal fl_output_asfifo_out_eop_n    : std_logic;
   signal fl_output_asfifo_out_eof_n    : std_logic;
   signal fl_output_asfifo_out_src_rdy_n: std_logic;
   signal fl_output_asfifo_out_dst_rdy_n: std_logic;

   -- FrameLink first insert component input
   signal fl_first_insert_in_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_first_insert_in_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_first_insert_in_sof_n     : std_logic;
   signal fl_first_insert_in_sop_n     : std_logic;
   signal fl_first_insert_in_eop_n     : std_logic;
   signal fl_first_insert_in_eof_n     : std_logic;
   signal fl_first_insert_in_src_rdy_n : std_logic;
   signal fl_first_insert_in_dst_rdy_n : std_logic;

   -- FrameLink first insert component output
   signal fl_first_insert_out_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_first_insert_out_rem      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_first_insert_out_sof_n    : std_logic;
   signal fl_first_insert_out_sop_n    : std_logic;
   signal fl_first_insert_out_eop_n    : std_logic;
   signal fl_first_insert_out_eof_n    : std_logic;
   signal fl_first_insert_out_src_rdy_n: std_logic;
   signal fl_first_insert_out_dst_rdy_n: std_logic;

   -- clock gate signals
   signal clock_enable           : std_logic;
   signal clk_dut                : std_logic;

   -- reset for DUT
   signal reset_dut              : std_logic;

   -- clock enable register
   signal reg_clock_enable       : std_logic;

begin
 
   -- ------------------------------------------------------------------------
   --                           Mapping of inputs
   -- ------------------------------------------------------------------------
   fl_input_asfifo_in_data       <= RX_DATA;
   fl_input_asfifo_in_rem        <= RX_REM;
   fl_input_asfifo_in_sof_n      <= RX_SOF_N;
   fl_input_asfifo_in_sop_n      <= RX_SOP_N;
   fl_input_asfifo_in_eop_n      <= RX_EOP_N;
   fl_input_asfifo_in_eof_n      <= RX_EOF_N;
   fl_input_asfifo_in_src_rdy_n  <= RX_SRC_RDY_N;
   RX_DST_RDY_N  <= fl_input_asfifo_in_dst_rdy_n;


   -- ------------------------------------------------------------------------
   --                        Input asynchronous FIFO
   -- ------------------------------------------------------------------------
   fl_asfifo_input: entity work.FL_ASFIFO_VIRTEX5
   generic map(
      -- FrameLink data width
      WIDTH => DATA_WIDTH
   )
   port map(
      -- input clock domain
      RX_CLK        => CLK,
      RX_RESET      => RESET,

      -- output clock domain
      TX_CLK        => clk_dut,
      TX_RESET      => reset_dut,

      -- input interface
      RX_DATA       => fl_input_asfifo_in_data,
      RX_REM        => fl_input_asfifo_in_rem,
      RX_SOF_N      => fl_input_asfifo_in_sof_n,
      RX_SOP_N      => fl_input_asfifo_in_sop_n,
      RX_EOP_N      => fl_input_asfifo_in_eop_n,
      RX_EOF_N      => fl_input_asfifo_in_eof_n,
      RX_SRC_RDY_N  => fl_input_asfifo_in_src_rdy_n, 
      RX_DST_RDY_N  => fl_input_asfifo_in_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => fl_input_asfifo_out_data,
      TX_REM        => fl_input_asfifo_out_rem,
      TX_SOF_N      => fl_input_asfifo_out_sof_n,
      TX_SOP_N      => fl_input_asfifo_out_sop_n,
      TX_EOP_N      => fl_input_asfifo_out_eop_n,
      TX_EOF_N      => fl_input_asfifo_out_eof_n,
      TX_SRC_RDY_N  => fl_input_asfifo_out_src_rdy_n,
      TX_DST_RDY_N  => fl_input_asfifo_out_dst_rdy_n
   );

   fl_shortener_in_data       <= fl_input_asfifo_out_data;
   fl_shortener_in_rem        <= fl_input_asfifo_out_rem;
   fl_shortener_in_sof_n      <= fl_input_asfifo_out_sof_n;
   fl_shortener_in_sop_n      <= fl_input_asfifo_out_sop_n;
   fl_shortener_in_eop_n      <= fl_input_asfifo_out_eop_n;
   fl_shortener_in_eof_n      <= fl_input_asfifo_out_eof_n;
   fl_shortener_in_src_rdy_n  <= fl_input_asfifo_out_src_rdy_n;
   fl_input_asfifo_out_dst_rdy_n  <= fl_shortener_in_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                              Frame Shortener
   -- ------------------------------------------------------------------------
   shortener_i: entity work.FL_SHORTENER
   generic map(
      -- FrameLink data width
      DATA_WIDTH => DATA_WIDTH,
      -- number of part in the FrameLink frame that will be truncated
      PART_NUM   => 0,

      -- number of bytes that will be kept in processed part of frame
      -- value of 0 is not accepted
      BYTES_KEPT => DATA_WIDTH / 8,

      -- number of parts in frame
      PARTS      => 1
   )
   port map(
      CLK           => clk_dut,
      RESET         => reset_dut,

      -- input interface
      RX_DATA       => fl_shortener_in_data,
      RX_REM        => fl_shortener_in_rem,
      RX_SOF_N      => fl_shortener_in_sof_n,
      RX_SOP_N      => fl_shortener_in_sop_n,
      RX_EOP_N      => fl_shortener_in_eop_n,
      RX_EOF_N      => fl_shortener_in_eof_n,
      RX_SRC_RDY_N  => fl_shortener_in_src_rdy_n, 
      RX_DST_RDY_N  => fl_shortener_in_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => fl_shortener_out_data,
      TX_REM        => fl_shortener_out_rem,
      TX_SOF_N      => fl_shortener_out_sof_n,
      TX_SOP_N      => fl_shortener_out_sop_n,
      TX_EOP_N      => fl_shortener_out_eop_n,
      TX_EOF_N      => fl_shortener_out_eof_n,
      TX_SRC_RDY_N  => fl_shortener_out_src_rdy_n,
      TX_DST_RDY_N  => fl_shortener_out_dst_rdy_n
   );

   fl_output_asfifo_in_data       <= fl_shortener_out_data;
   fl_output_asfifo_in_rem        <= fl_shortener_out_rem;
   fl_output_asfifo_in_sof_n      <= fl_shortener_out_sof_n;
   fl_output_asfifo_in_sop_n      <= fl_shortener_out_sop_n;
   fl_output_asfifo_in_eop_n      <= fl_shortener_out_eop_n;
   fl_output_asfifo_in_eof_n      <= fl_shortener_out_eof_n;
   fl_output_asfifo_in_src_rdy_n  <= fl_shortener_out_src_rdy_n;
   fl_shortener_out_dst_rdy_n  <= fl_output_asfifo_in_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                        Output asynchronous FIFO
   -- ------------------------------------------------------------------------
   fl_asfifo_output: entity work.FL_ASFIFO_VIRTEX5
   generic map(
      -- FrameLink data width
      WIDTH => DATA_WIDTH
   )
   port map(
      -- input clock domain
      RX_CLK        => clk_dut,
      RX_RESET      => reset_dut,

      -- output clock domain
      TX_CLK        => CLK,
      TX_RESET      => RESET,

      -- input interface
      RX_DATA       => fl_output_asfifo_in_data,
      RX_REM        => fl_output_asfifo_in_rem,
      RX_SOF_N      => fl_output_asfifo_in_sof_n,
      RX_SOP_N      => fl_output_asfifo_in_sop_n,
      RX_EOP_N      => fl_output_asfifo_in_eop_n,
      RX_EOF_N      => fl_output_asfifo_in_eof_n,
      RX_SRC_RDY_N  => fl_output_asfifo_in_src_rdy_n, 
      RX_DST_RDY_N  => fl_output_asfifo_in_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => fl_output_asfifo_out_data,
      TX_REM        => fl_output_asfifo_out_rem,
      TX_SOF_N      => fl_output_asfifo_out_sof_n,
      TX_SOP_N      => fl_output_asfifo_out_sop_n,
      TX_EOP_N      => fl_output_asfifo_out_eop_n,
      TX_EOF_N      => fl_output_asfifo_out_eof_n,
      TX_SRC_RDY_N  => fl_output_asfifo_out_src_rdy_n,
      TX_DST_RDY_N  => fl_output_asfifo_out_dst_rdy_n
   );

   fl_first_insert_in_data       <= fl_output_asfifo_out_data;
   fl_first_insert_in_rem        <= fl_output_asfifo_out_rem;
   fl_first_insert_in_sof_n      <= fl_output_asfifo_out_sof_n;
   fl_first_insert_in_sop_n      <= fl_output_asfifo_out_sop_n;
   fl_first_insert_in_eop_n      <= fl_output_asfifo_out_eop_n;
   fl_first_insert_in_eof_n      <= fl_output_asfifo_out_eof_n;
   fl_first_insert_in_src_rdy_n  <= fl_output_asfifo_out_src_rdy_n;
   fl_output_asfifo_out_dst_rdy_n  <= fl_first_insert_in_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                              First insert
   -- ------------------------------------------------------------------------
   first_insert_i: entity work.FL_FIRST_INSERT
   generic map(
      DATA_WIDTH => DATA_WIDTH
   )
   port map(
      CLK           => CLK,
      RESET         => RESET,

      -- word to insert
      DATA          => X"CA1A010000040010",
      DREM          => "111",

      -- input interface
      RX_DATA       => fl_first_insert_in_data,
      RX_REM        => fl_first_insert_in_rem,
      RX_SOF_N      => fl_first_insert_in_sof_n,
      RX_SOP_N      => fl_first_insert_in_sop_n,
      RX_EOP_N      => fl_first_insert_in_eop_n,
      RX_EOF_N      => fl_first_insert_in_eof_n,
      RX_SRC_RDY_N  => fl_first_insert_in_src_rdy_n,
      RX_DST_RDY_N  => fl_first_insert_in_dst_rdy_n,
      
      -- output interface
      TX_DATA       => fl_first_insert_out_data,
      TX_REM        => fl_first_insert_out_rem,
      TX_SOF_N      => fl_first_insert_out_sof_n,
      TX_SOP_N      => fl_first_insert_out_sop_n,
      TX_EOP_N      => fl_first_insert_out_eop_n,
      TX_EOF_N      => fl_first_insert_out_eof_n,
      TX_SRC_RDY_N  => fl_first_insert_out_src_rdy_n,
      TX_DST_RDY_N  => fl_first_insert_out_dst_rdy_n
   );


   -- ------------------------------------------------------------------------
   --                          Mapping of outputs
   -- ------------------------------------------------------------------------
   TX_DATA       <= fl_first_insert_out_data;
   TX_REM        <= fl_first_insert_out_rem;
   TX_SOF_N      <= fl_first_insert_out_sof_n;
   TX_SOP_N      <= fl_first_insert_out_sop_n;
   TX_EOP_N      <= fl_first_insert_out_eop_n;
   TX_EOF_N      <= fl_first_insert_out_eof_n;
   TX_SRC_RDY_N  <= fl_first_insert_out_src_rdy_n;
   fl_first_insert_out_dst_rdy_n  <= TX_DST_RDY_N;


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

   -- TODO: change to a more correct variant
   reset_dut <= RESET;

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

   clock_enable <= reg_clock_enable;


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
