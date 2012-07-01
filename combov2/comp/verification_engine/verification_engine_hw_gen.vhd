-- verification_engine_hw_gen.vhd: HW_GEN architecture of verification engine
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

   -- MI32 splitter inputs
   signal mi_splitter_dwr      : std_logic_vector(31 downto 0);
   signal mi_splitter_addr     : std_logic_vector(31 downto 0);
   signal mi_splitter_be       : std_logic_vector( 3 downto 0);
   signal mi_splitter_rd       : std_logic;
   signal mi_splitter_wr       : std_logic;
   signal mi_splitter_ardy     : std_logic;
   signal mi_splitter_drd      : std_logic_vector(31 downto 0);
   signal mi_splitter_drdy     : std_logic;

   -- MI32 splitter outputs
   signal mi_spl_out_dwr      : std_logic_vector(63 downto 0);
   signal mi_spl_out_addr     : std_logic_vector(63 downto 0);
   signal mi_spl_out_be       : std_logic_vector( 7 downto 0);
   signal mi_spl_out_rd       : std_logic_vector( 1 downto 0);
   signal mi_spl_out_wr       : std_logic_vector( 1 downto 0);
   signal mi_spl_out_ardy     : std_logic_vector( 1 downto 0);
   signal mi_spl_out_drd      : std_logic_vector(63 downto 0);
   signal mi_spl_out_drdy     : std_logic_vector( 1 downto 0);

   -- FrameLink Generator MI32 interface
   signal fl_rand_gen_mi_dwr      : std_logic_vector(31 downto 0);
   signal fl_rand_gen_mi_addr     : std_logic_vector(31 downto 0);
   signal fl_rand_gen_mi_be       : std_logic_vector( 3 downto 0);
   signal fl_rand_gen_mi_rd       : std_logic;
   signal fl_rand_gen_mi_wr       : std_logic;
   signal fl_rand_gen_mi_ardy     : std_logic;
   signal fl_rand_gen_mi_drd      : std_logic_vector(31 downto 0);
   signal fl_rand_gen_mi_drdy     : std_logic;

   -- FrameLink Generator output
   signal fl_gen_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_gen_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_gen_tx_sof_n     : std_logic;
   signal fl_gen_tx_sop_n     : std_logic;
   signal fl_gen_tx_eop_n     : std_logic;
   signal fl_gen_tx_eof_n     : std_logic;
   signal fl_gen_tx_src_rdy_n : std_logic;
   signal fl_gen_tx_dst_rdy_n : std_logic;

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
   fl_input_dst_rdy_n        <= '0';

   --
   mi_splitter_dwr    <= MI32_DWR;
   mi_splitter_addr   <= MI32_ADDR;
   mi_splitter_be     <= MI32_BE;
   mi_splitter_rd     <= MI32_RD;
   mi_splitter_wr     <= MI32_WR;
   MI32_ARDY          <= mi_splitter_ardy;
   MI32_DRD           <= mi_splitter_drd;
   MI32_DRDY          <= mi_splitter_drdy;

   -- MI Splitter Ondrik's --------------------------------------------------
   mi_splitter_ondriks_i: entity work.MI_SPLITTER_ONDRIKS
   generic map(
      -- Data width
      DATA_WIDTH    => 32,
      -- Number of output ports
      ITEMS         => 2,

      -- ADDRESS SPACE

      -- PORT0: 0x00000000 -- 0x000FFFFF
      PORT0_BASE    => X"00000000",
      PORT0_LIMIT   => X"00100000",

      -- PORT1: 0x00100000 -- 0x001FFFFF
      PORT0_BASE    => X"00100000",
      PORT0_LIMIT   => X"00100000",

      -- Input pipeline
      PIPE          => true,
      PIPE_OUTREG   => true
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK         => CLK,
      RESET       => RESET,

      -- Input MI interface ---------------------------------------------------
      IN_DWR      => mi_splitter_dwr,
      IN_ADDR     => mi_splitter_addr,
      IN_BE       => mi_splitter_be,
      IN_RD       => mi_splitter_rd,
      IN_WR       => mi_splitter_wr,
      IN_ARDY     => mi_splitter_ardy,
      IN_DRD      => mi_splitter_drd,
      IN_DRDY     => mi_splitter_drdy,

      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     => mi_spl_out_dwr,
      OUT_ADDR    => mi_spl_out_addr,
      OUT_BE      => mi_spl_out_be,
      OUT_RD      => mi_spl_out_rd,
      OUT_WR      => mi_spl_out_wr,
      OUT_ARDY    => mi_spl_out_ardy,
      OUT_DRD     => mi_spl_out_drd,
      OUT_DRDY    => mi_spl_out_drdy
   );

   --
   fl_rand_gen_mi_dwr            <= mi_spl_out_dwr( 63 downto 32);
   fl_rand_gen_mi_addr           <= mi_spl_out_addr(63 downto 32);
   fl_rand_gen_mi_rd             <= mi_spl_out_rd(1);
   fl_rand_gen_mi_wr             <= mi_spl_out_wr(1);
   fl_rand_gen_mi_be             <= mi_spl_out_be(7 downto 4);
   mi_spl_out_drd(63 downto 32)  <= fl_rand_gen_mi_drd;
   mi_spl_out_ardy(1)            <= fl_rand_gen_mi_ardy;
   mi_spl_out_drdy(1)            <= fl_rand_gen_mi_drdy;

   mi_spl_out_drd(31 downto 0)   <= X"E1E1E100";
   mi_spl_out_ardy(0)            <= mi_spl_out_rd(0) OR mi_spl_out_wr(0);
   mi_spl_out_drdy(0)            <= mi_spl_out_rd(0);

   -- ------------------------------------------------------------------------
   --                         FrameLink Random Generator
   -- ------------------------------------------------------------------------
   fl_rand_gen_i: entity work.fl_rand_gen
   generic map(
      -- the output FrameLink width
      DATA_WIDTH     => DATA_WIDTH,
      -- ID of the destination endpoint
      ENDPOINT_ID    => 16#EA#
   )
   port map(
      -- input clock domain
      CLK        => CLK,
      RESET      => RESET,

      -- MI32 interface
      MI_DWR      => fl_rand_gen_mi_dwr,
      MI_ADDR     => fl_rand_gen_mi_addr,
      MI_RD       => fl_rand_gen_mi_rd,
      MI_WR       => fl_rand_gen_mi_wr,
      MI_BE       => fl_rand_gen_mi_be,
      MI_DRD      => fl_rand_gen_mi_drd,
      MI_ARDY     => fl_rand_gen_mi_ardy,
      MI_DRDY     => fl_rand_gen_mi_drdy,

      -- output FrameLink
      TX_DATA       => fl_gen_tx_data,
      TX_REM        => fl_gen_tx_rem,
      TX_SOF_N      => fl_gen_tx_sof_n,
      TX_SOP_N      => fl_gen_tx_sop_n,
      TX_EOP_N      => fl_gen_tx_eop_n,
      TX_EOF_N      => fl_gen_tx_eof_n,
      TX_SRC_RDY_N  => fl_gen_tx_src_rdy_n,
      TX_DST_RDY_N  => fl_gen_tx_dst_rdy_n
   );

   -- ------------------------------------------------------------------------
   --                              NetCOPE Adder
   -- ------------------------------------------------------------------------

   fl_netcope_adder_in_data       <= fl_gen_tx_data;
   fl_netcope_adder_in_rem        <= fl_gen_tx_rem;
   fl_netcope_adder_in_sof_n      <= fl_gen_tx_sof_n;
   fl_netcope_adder_in_sop_n      <= fl_gen_tx_sop_n;
   fl_netcope_adder_in_eop_n      <= fl_gen_tx_eop_n;
   fl_netcope_adder_in_eof_n      <= fl_gen_tx_eof_n;
   fl_netcope_adder_in_src_rdy_n  <= fl_gen_tx_src_rdy_n;
   fl_gen_tx_dst_rdy_n            <= fl_netcope_adder_in_dst_rdy_n;

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
