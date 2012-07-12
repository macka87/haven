-- verification_engine_hw_gen_core.vhd: HW_GEN_CORE architecture of verification engine
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
architecture arch of verification_engine is

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

constant DREM_WIDTH   : integer := log2(DATA_WIDTH/8);

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- input FrameLink signals
   signal fl_input_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_input_rem        : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_input_sof_n      : std_logic;
   signal fl_input_sop_n      : std_logic;
   signal fl_input_eop_n      : std_logic;
   signal fl_input_eof_n      : std_logic;
   signal fl_input_src_rdy_n  : std_logic;
   signal fl_input_dst_rdy_n  : std_logic;

   -- output FrameLink signals
   signal fl_output_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_output_rem        : std_logic_vector(DREM_WIDTH-1 downto 0);
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
   signal mi_spl_out_dwr      : std_logic_vector(95 downto 0);
   signal mi_spl_out_addr     : std_logic_vector(95 downto 0);
   signal mi_spl_out_be       : std_logic_vector(11 downto 0);
   signal mi_spl_out_rd       : std_logic_vector( 2 downto 0);
   signal mi_spl_out_wr       : std_logic_vector( 2 downto 0);
   signal mi_spl_out_ardy     : std_logic_vector( 2 downto 0);
   signal mi_spl_out_drd      : std_logic_vector(95 downto 0);
   signal mi_spl_out_drdy     : std_logic_vector( 2 downto 0);

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
   signal fl_gen_tx_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_gen_tx_sof_n     : std_logic;
   signal fl_gen_tx_sop_n     : std_logic;
   signal fl_gen_tx_eop_n     : std_logic;
   signal fl_gen_tx_eof_n     : std_logic;
   signal fl_gen_tx_src_rdy_n : std_logic;
   signal fl_gen_tx_dst_rdy_n : std_logic;

   -- FrameLink fork input
   signal fl_fork_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_fork_rx_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_fork_rx_sof_n     : std_logic;
   signal fl_fork_rx_sop_n     : std_logic;
   signal fl_fork_rx_eop_n     : std_logic;
   signal fl_fork_rx_eof_n     : std_logic;
   signal fl_fork_rx_src_rdy_n : std_logic;
   signal fl_fork_rx_dst_rdy_n : std_logic;

   -- FrameLink fork output
   signal fl_fork_tx_data      : std_logic_vector(2*DATA_WIDTH-1 downto 0);
   signal fl_fork_tx_rem       : std_logic_vector(2*DREM_WIDTH-1 downto 0);
   signal fl_fork_tx_sof_n     : std_logic_vector(1 downto 0);
   signal fl_fork_tx_sop_n     : std_logic_vector(1 downto 0);
   signal fl_fork_tx_eop_n     : std_logic_vector(1 downto 0);
   signal fl_fork_tx_eof_n     : std_logic_vector(1 downto 0);
   signal fl_fork_tx_src_rdy_n : std_logic_vector(1 downto 0);
   signal fl_fork_tx_dst_rdy_n : std_logic_vector(1 downto 0);

   -- FrameLink fork output 0
   signal fl_fork_tx0_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_fork_tx0_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_fork_tx0_sof_n     : std_logic;
   signal fl_fork_tx0_sop_n     : std_logic;
   signal fl_fork_tx0_eop_n     : std_logic;
   signal fl_fork_tx0_eof_n     : std_logic;
   signal fl_fork_tx0_src_rdy_n : std_logic;
   signal fl_fork_tx0_dst_rdy_n : std_logic;

   -- FrameLink fork output 1
   signal fl_fork_tx1_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_fork_tx1_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_fork_tx1_sof_n     : std_logic;
   signal fl_fork_tx1_sop_n     : std_logic;
   signal fl_fork_tx1_eop_n     : std_logic;
   signal fl_fork_tx1_eof_n     : std_logic;
   signal fl_fork_tx1_src_rdy_n : std_logic;
   signal fl_fork_tx1_dst_rdy_n : std_logic;

   -- FrameLink Generator MI32 interface
   signal fl_com_unit_mi_dwr      : std_logic_vector(31 downto 0);
   signal fl_com_unit_mi_addr     : std_logic_vector(31 downto 0);
   signal fl_com_unit_mi_be       : std_logic_vector( 3 downto 0);
   signal fl_com_unit_mi_rd       : std_logic;
   signal fl_com_unit_mi_wr       : std_logic;
   signal fl_com_unit_mi_ardy     : std_logic;
   signal fl_com_unit_mi_drd      : std_logic_vector(31 downto 0);
   signal fl_com_unit_mi_drdy     : std_logic;

   -- FrameLink command unit output FrameLink interface
   signal fl_com_unit_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_com_unit_tx_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_com_unit_tx_sof_n     : std_logic;
   signal fl_com_unit_tx_sop_n     : std_logic;
   signal fl_com_unit_tx_eop_n     : std_logic;
   signal fl_com_unit_tx_eof_n     : std_logic;
   signal fl_com_unit_tx_src_rdy_n : std_logic;
   signal fl_com_unit_tx_dst_rdy_n : std_logic;

   -- input binder input
   signal input_binder_rx_data     : std_logic_vector(3*DATA_WIDTH-1 downto 0);
   signal input_binder_rx_rem      : std_logic_vector(3*DREM_WIDTH-1 downto 0);
   signal input_binder_rx_sof_n    : std_logic_vector(2 downto 0);
   signal input_binder_rx_sop_n    : std_logic_vector(2 downto 0);
   signal input_binder_rx_eop_n    : std_logic_vector(2 downto 0);
   signal input_binder_rx_eof_n    : std_logic_vector(2 downto 0);
   signal input_binder_rx_src_rdy_n: std_logic_vector(2 downto 0);
   signal input_binder_rx_dst_rdy_n: std_logic_vector(2 downto 0);

   -- input binder output
   signal input_binder_tx_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal input_binder_tx_rem      : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal input_binder_tx_sof_n    : std_logic;
   signal input_binder_tx_sop_n    : std_logic;
   signal input_binder_tx_eop_n    : std_logic;
   signal input_binder_tx_eof_n    : std_logic;
   signal input_binder_tx_src_rdy_n: std_logic;
   signal input_binder_tx_dst_rdy_n: std_logic;

   -- Verification Core MI32 interface
   signal ver_core_mi_dwr      : std_logic_vector(31 downto 0);
   signal ver_core_mi_addr     : std_logic_vector(31 downto 0);
   signal ver_core_mi_be       : std_logic_vector( 3 downto 0);
   signal ver_core_mi_rd       : std_logic;
   signal ver_core_mi_wr       : std_logic;
   signal ver_core_mi_ardy     : std_logic;
   signal ver_core_mi_drd      : std_logic_vector(31 downto 0);
   signal ver_core_mi_drdy     : std_logic;

   -- Verification Core FrameLink input
   signal fl_ver_core_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_ver_core_rx_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_ver_core_rx_sof_n     : std_logic;
   signal fl_ver_core_rx_sop_n     : std_logic;
   signal fl_ver_core_rx_eop_n     : std_logic;
   signal fl_ver_core_rx_eof_n     : std_logic;
   signal fl_ver_core_rx_src_rdy_n : std_logic;
   signal fl_ver_core_rx_dst_rdy_n : std_logic;

   -- Verification Core FrameLink output
   signal fl_ver_core_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_ver_core_tx_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_ver_core_tx_sof_n     : std_logic;
   signal fl_ver_core_tx_sop_n     : std_logic;
   signal fl_ver_core_tx_eop_n     : std_logic;
   signal fl_ver_core_tx_eof_n     : std_logic;
   signal fl_ver_core_tx_src_rdy_n : std_logic;
   signal fl_ver_core_tx_dst_rdy_n : std_logic;

   -- FrameLink NetCOPE Adder component input
   signal fl_netcope_adder_in_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_in_rem       : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_netcope_adder_in_sof_n     : std_logic;
   signal fl_netcope_adder_in_sop_n     : std_logic;
   signal fl_netcope_adder_in_eop_n     : std_logic;
   signal fl_netcope_adder_in_eof_n     : std_logic;
   signal fl_netcope_adder_in_src_rdy_n : std_logic;
   signal fl_netcope_adder_in_dst_rdy_n : std_logic;

   -- FrameLink NetCOPE Adder component output
   signal fl_netcope_adder_out_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_netcope_adder_out_rem      : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal fl_netcope_adder_out_sof_n    : std_logic;
   signal fl_netcope_adder_out_sop_n    : std_logic;
   signal fl_netcope_adder_out_eop_n    : std_logic;
   signal fl_netcope_adder_out_eof_n    : std_logic;
   signal fl_netcope_adder_out_src_rdy_n: std_logic;
   signal fl_netcope_adder_out_dst_rdy_n: std_logic;

   -- output binder input
   signal output_binder_rx_data     : std_logic_vector(2*DATA_WIDTH-1 downto 0);
   signal output_binder_rx_rem      : std_logic_vector(2*DREM_WIDTH-1 downto 0);
   signal output_binder_rx_sof_n    : std_logic_vector(1 downto 0);
   signal output_binder_rx_sop_n    : std_logic_vector(1 downto 0);
   signal output_binder_rx_eop_n    : std_logic_vector(1 downto 0);
   signal output_binder_rx_eof_n    : std_logic_vector(1 downto 0);
   signal output_binder_rx_src_rdy_n: std_logic_vector(1 downto 0);
   signal output_binder_rx_dst_rdy_n: std_logic_vector(1 downto 0);

   -- output binder output
   signal output_binder_tx_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal output_binder_tx_rem      : std_logic_vector(DREM_WIDTH-1 downto 0);
   signal output_binder_tx_sof_n    : std_logic;
   signal output_binder_tx_sop_n    : std_logic;
   signal output_binder_tx_eop_n    : std_logic;
   signal output_binder_tx_eof_n    : std_logic;
   signal output_binder_tx_src_rdy_n: std_logic;
   signal output_binder_tx_dst_rdy_n: std_logic;

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
      ITEMS         => 3,

      -- ADDRESS SPACE

      -- PORT0: 0x00000000 -- 0x000FFFFF
      PORT0_BASE    => X"00000000",
      PORT0_LIMIT   => X"00100000",

      -- PORT1: 0x00100000 -- 0x001FFFFF
      PORT1_BASE    => X"00100000",
      PORT1_LIMIT   => X"00100000",

      -- PORT2: 0x00200000 -- 0x002FFFFF
      PORT2_BASE    => X"00200000",
      PORT2_LIMIT   => X"00100000",

      -- Input pipeline
      PIPE          => false,
      PIPE_OUTREG   => false
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
   fl_com_unit_mi_dwr            <= mi_spl_out_dwr( 95 downto 64);
   fl_com_unit_mi_addr           <= mi_spl_out_addr(95 downto 64);
   fl_com_unit_mi_rd             <= mi_spl_out_rd(2);
   fl_com_unit_mi_wr             <= mi_spl_out_wr(2);
   fl_com_unit_mi_be             <= mi_spl_out_be(11 downto 8);
   mi_spl_out_drd(95 downto 64)  <= fl_com_unit_mi_drd;
   mi_spl_out_ardy(2)            <= fl_com_unit_mi_ardy;
   mi_spl_out_drdy(2)            <= fl_com_unit_mi_drdy;

   fl_rand_gen_mi_dwr            <= mi_spl_out_dwr( 63 downto 32);
   fl_rand_gen_mi_addr           <= mi_spl_out_addr(63 downto 32);
   fl_rand_gen_mi_rd             <= mi_spl_out_rd(1);
   fl_rand_gen_mi_wr             <= mi_spl_out_wr(1);
   fl_rand_gen_mi_be             <= mi_spl_out_be(7 downto 4);
   mi_spl_out_drd(63 downto 32)  <= fl_rand_gen_mi_drd;
   mi_spl_out_ardy(1)            <= fl_rand_gen_mi_ardy;
   mi_spl_out_drdy(1)            <= fl_rand_gen_mi_drdy;

   ver_core_mi_dwr               <= mi_spl_out_dwr( 31 downto 0);
   ver_core_mi_addr              <= mi_spl_out_addr(31 downto 0);
   ver_core_mi_rd                <= mi_spl_out_rd(0);
   ver_core_mi_wr                <= mi_spl_out_wr(0);
   ver_core_mi_be                <= mi_spl_out_be(3 downto 0);
   mi_spl_out_drd(31 downto 0)   <= ver_core_mi_drd;
   mi_spl_out_ardy(0)            <= ver_core_mi_ardy;
   mi_spl_out_drdy(0)            <= ver_core_mi_drdy;

   -- ------------------------------------------------------------------------
   --                         FrameLink Random Generator
   -- ------------------------------------------------------------------------
   fl_rand_gen_i: entity work.fl_rand_gen
   generic map(
      -- the output FrameLink width
      DATA_WIDTH     => DATA_WIDTH,
      -- ID of the destination endpoint
      ENDPOINT_ID    => ENDPOINT_ID_FL_RAND_GEN,
      -- ID of the FrameLink protocol
      FL_PROTOCOL_ID => PROTO_IN_FRAMELINK
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
   --                         FrameLink Command Unit
   -- ------------------------------------------------------------------------
   fl_com_unit_i: entity work.fl_command_unit
   generic map(
      -- the output FrameLink width
      DATA_WIDTH     => DATA_WIDTH,
      -- ID of the destination endpoint
      ENDPOINT_ID    => ENDPOINT_ID_FL_RAND_GEN,
      -- ID of the FrameLink protocol
      FL_PROTOCOL_ID => PROTO_IN_FRAMELINK
   )
   port map(
      -- input clock domain
      CLK        => CLK,
      RESET      => RESET,

      -- MI32 interface
      MI_DWR        => fl_com_unit_mi_dwr,
      MI_ADDR       => fl_com_unit_mi_addr,
      MI_RD         => fl_com_unit_mi_rd,
      MI_WR         => fl_com_unit_mi_wr,
      MI_BE         => fl_com_unit_mi_be,
      MI_DRD        => fl_com_unit_mi_drd,
      MI_ARDY       => fl_com_unit_mi_ardy,
      MI_DRDY       => fl_com_unit_mi_drdy,

      -- output FrameLink
      TX_DATA       => fl_com_unit_tx_data,
      TX_REM        => fl_com_unit_tx_rem,
      TX_SOF_N      => fl_com_unit_tx_sof_n,
      TX_SOP_N      => fl_com_unit_tx_sop_n,
      TX_EOP_N      => fl_com_unit_tx_eop_n,
      TX_EOF_N      => fl_com_unit_tx_eof_n,
      TX_SRC_RDY_N  => fl_com_unit_tx_src_rdy_n,
      TX_DST_RDY_N  => fl_com_unit_tx_dst_rdy_n
   );

   --
   fl_fork_rx_data       <= fl_gen_tx_data;
   fl_fork_rx_rem        <= fl_gen_tx_rem;
   fl_fork_rx_sof_n      <= fl_gen_tx_sof_n;
   fl_fork_rx_sop_n      <= fl_gen_tx_sop_n;
   fl_fork_rx_eop_n      <= fl_gen_tx_eop_n;
   fl_fork_rx_eof_n      <= fl_gen_tx_eof_n;
   fl_fork_rx_src_rdy_n  <= fl_gen_tx_src_rdy_n;
   fl_gen_tx_dst_rdy_n   <= fl_fork_rx_dst_rdy_n;

   -- the fork of the output of the random FrameLink generator
   fl_fork_i: entity work.FL_FORK
   generic map(
       DATA_WIDTH     => DATA_WIDTH,
       OUTPUT_PORTS   => 2
   )
   port map(
       -- Common interface
      CLK            => CLK,
      RESET          => RESET,

      -- Frame link input interface
      RX_DATA        => fl_fork_rx_data,
      RX_REM         => fl_fork_rx_rem,
      RX_SOF_N       => fl_fork_rx_sof_n,
      RX_EOF_N       => fl_fork_rx_eof_n,
      RX_SOP_N       => fl_fork_rx_sop_n,
      RX_EOP_N       => fl_fork_rx_eop_n,
      RX_SRC_RDY_N   => fl_fork_rx_src_rdy_n,
      RX_DST_RDY_N   => fl_fork_rx_dst_rdy_n,

      -- Frame link concentrated interface
      TX_DATA        => fl_fork_tx_data,
      TX_REM         => fl_fork_tx_rem,
      TX_SOF_N       => fl_fork_tx_sof_n,
      TX_EOF_N       => fl_fork_tx_eof_n,
      TX_SOP_N       => fl_fork_tx_sop_n,
      TX_EOP_N       => fl_fork_tx_eop_n,
      TX_SRC_RDY_N   => fl_fork_tx_src_rdy_n,
      TX_DST_RDY_N   => fl_fork_tx_dst_rdy_n
   );

   fl_fork_tx0_data        <= fl_fork_tx_data(DATA_WIDTH-1 downto 0);
   fl_fork_tx0_rem         <= fl_fork_tx_rem( DREM_WIDTH-1 downto 0);
   fl_fork_tx0_sof_n       <= fl_fork_tx_sof_n(0);
   fl_fork_tx0_eof_n       <= fl_fork_tx_eof_n(0);
   fl_fork_tx0_sop_n       <= fl_fork_tx_sop_n(0);
   fl_fork_tx0_eop_n       <= fl_fork_tx_eop_n(0);
   fl_fork_tx0_src_rdy_n   <= fl_fork_tx_src_rdy_n(0);
   fl_fork_tx_dst_rdy_n(0) <= fl_fork_tx0_dst_rdy_n;

   fl_fork_tx1_data        <= fl_fork_tx_data(2*DATA_WIDTH-1 downto DATA_WIDTH);
   fl_fork_tx1_rem         <= fl_fork_tx_rem( 2*DREM_WIDTH-1 downto DREM_WIDTH);
   fl_fork_tx1_sof_n       <= fl_fork_tx_sof_n(1);
   fl_fork_tx1_eof_n       <= fl_fork_tx_eof_n(1);
   fl_fork_tx1_sop_n       <= fl_fork_tx_sop_n(1);
   fl_fork_tx1_eop_n       <= fl_fork_tx_eop_n(1);
   fl_fork_tx1_src_rdy_n   <= fl_fork_tx_src_rdy_n(1);
   fl_fork_tx_dst_rdy_n(1) <= fl_fork_tx1_dst_rdy_n;

   --
   input_binder_rx_data(DATA_WIDTH-1 downto 0)  <= fl_input_data;
   input_binder_rx_rem( DREM_WIDTH-1 downto 0)  <= fl_input_rem;
   input_binder_rx_sof_n(0)                     <= fl_input_sof_n;
   input_binder_rx_sop_n(0)                     <= fl_input_sop_n;
   input_binder_rx_eop_n(0)                     <= fl_input_eop_n;
   input_binder_rx_eof_n(0)                     <= fl_input_eof_n;
   input_binder_rx_src_rdy_n(0)                 <= fl_input_src_rdy_n;
   fl_input_dst_rdy_n                           <= input_binder_rx_dst_rdy_n(0);

   input_binder_rx_data(2*DATA_WIDTH-1 downto DATA_WIDTH) <= fl_fork_tx0_data;
   input_binder_rx_rem( 2*DREM_WIDTH-1 downto DREM_WIDTH) <= fl_fork_tx0_rem;
   input_binder_rx_sof_n(1)                               <= fl_fork_tx0_sof_n;
   input_binder_rx_sop_n(1)                               <= fl_fork_tx0_sop_n;
   input_binder_rx_eop_n(1)                               <= fl_fork_tx0_eop_n;
   input_binder_rx_eof_n(1)                               <= fl_fork_tx0_eof_n;
   input_binder_rx_src_rdy_n(1)                           <= fl_fork_tx0_src_rdy_n;
   fl_fork_tx0_dst_rdy_n                                  <= input_binder_rx_dst_rdy_n(1);

   input_binder_rx_data(3*DATA_WIDTH-1 downto 2*DATA_WIDTH)<= fl_com_unit_tx_data;
   input_binder_rx_rem( 3*DREM_WIDTH-1 downto 2*DREM_WIDTH)<= fl_com_unit_tx_rem;
   input_binder_rx_sof_n(2)                                <= fl_com_unit_tx_sof_n;
   input_binder_rx_sop_n(2)                                <= fl_com_unit_tx_sop_n;
   input_binder_rx_eop_n(2)                                <= fl_com_unit_tx_eop_n;
   input_binder_rx_eof_n(2)                                <= fl_com_unit_tx_eof_n;
   input_binder_rx_src_rdy_n(2)                            <= fl_com_unit_tx_src_rdy_n;
   fl_com_unit_tx_dst_rdy_n                                <= input_binder_rx_dst_rdy_n(2);

   -- the binder at the input of verification core
   input_binder_i: entity work.FL_BINDER
   generic map(
      -- width of one input interface. Should be multiple of 8
      INPUT_WIDTH    => DATA_WIDTH,
      -- number of input interfaces: only 2,4,8,16 supported
      INPUT_COUNT    => 3,
      -- output width - most effective value is INPUT_WIDTH*INPUT_COUNT. In 
      -- other cases FL_TRANSFORMER is instantiated
      OUTPUT_WIDTH   => DATA_WIDTH,
      -- number of parts in one FrameLink frame
      FRAME_PARTS    => 1,
      
      -- select BlockRAM or LUT memory
      LUT_MEMORY     => true,
      -- Queue choosing policy
      SIMPLE_BINDER  => true
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input FrameLink interface
      RX_DATA        => input_binder_rx_data,
      RX_REM         => input_binder_rx_rem,
      RX_SOF_N       => input_binder_rx_sof_n,
      RX_SOP_N       => input_binder_rx_sop_n,
      RX_EOP_N       => input_binder_rx_eop_n,
      RX_EOF_N       => input_binder_rx_eof_n,
      RX_SRC_RDY_N   => input_binder_rx_src_rdy_n,
      RX_DST_RDY_N   => input_binder_rx_dst_rdy_n,

      -- output FrameLink interface
      TX_DATA        => input_binder_tx_data,
      TX_REM         => input_binder_tx_rem,
      TX_SOF_N       => input_binder_tx_sof_n,
      TX_SOP_N       => input_binder_tx_sop_n,
      TX_EOP_N       => input_binder_tx_eop_n,
      TX_EOF_N       => input_binder_tx_eof_n,
      TX_SRC_RDY_N   => input_binder_tx_src_rdy_n,
      TX_DST_RDY_N   => input_binder_tx_dst_rdy_n
   );

   --
   fl_ver_core_rx_data       <= input_binder_tx_data;
   fl_ver_core_rx_rem        <= input_binder_tx_rem;
   fl_ver_core_rx_sof_n      <= input_binder_tx_sof_n;
   fl_ver_core_rx_sop_n      <= input_binder_tx_sop_n;
   fl_ver_core_rx_eop_n      <= input_binder_tx_eop_n;
   fl_ver_core_rx_eof_n      <= input_binder_tx_eof_n;
   fl_ver_core_rx_src_rdy_n  <= input_binder_tx_src_rdy_n;
   input_binder_tx_dst_rdy_n <= fl_ver_core_rx_dst_rdy_n;

   -- ------------------------------------------------------------------------
   --                             Verification Core
   -- ------------------------------------------------------------------------
   ver_core_i: entity work.VERIFICATION_CORE
   generic map(
      -- FrameLink data width
      DATA_WIDTH   => DATA_WIDTH,
      -- type of the core
      CORE_TYPE    => VER_CORE0_TYPE
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
      MI32_DWR      => ver_core_mi_dwr,
      MI32_ADDR     => ver_core_mi_addr,
      MI32_RD       => ver_core_mi_rd,
      MI32_WR       => ver_core_mi_wr,
      MI32_BE       => ver_core_mi_be,
      MI32_DRD      => ver_core_mi_drd,
      MI32_ARDY     => ver_core_mi_ardy,
      MI32_DRDY     => ver_core_mi_drdy
   );

   --
   output_binder_rx_data(DATA_WIDTH-1 downto 0)  <= fl_ver_core_tx_data;
   output_binder_rx_rem( DREM_WIDTH-1 downto 0)  <= fl_ver_core_tx_rem;
   output_binder_rx_sof_n(0)                     <= fl_ver_core_tx_sof_n;
   output_binder_rx_sop_n(0)                     <= fl_ver_core_tx_sop_n;
   output_binder_rx_eop_n(0)                     <= fl_ver_core_tx_eop_n;
   output_binder_rx_eof_n(0)                     <= fl_ver_core_tx_eof_n;
   output_binder_rx_src_rdy_n(0)                 <= fl_ver_core_tx_src_rdy_n;
   fl_ver_core_tx_dst_rdy_n                      <= output_binder_rx_dst_rdy_n(0);

   output_binder_rx_data(2*DATA_WIDTH-1 downto DATA_WIDTH)  <= fl_fork_tx1_data;
   output_binder_rx_rem( 2*DREM_WIDTH-1 downto DREM_WIDTH)  <= fl_fork_tx1_rem;
   output_binder_rx_sof_n(1)                                <= fl_fork_tx1_sof_n;
   output_binder_rx_sop_n(1)                                <= fl_fork_tx1_sop_n;
   output_binder_rx_eop_n(1)                                <= fl_fork_tx1_eop_n;
   output_binder_rx_eof_n(1)                                <= fl_fork_tx1_eof_n;
   output_binder_rx_src_rdy_n(1)                            <= fl_fork_tx1_src_rdy_n;
   fl_fork_tx1_dst_rdy_n                                    <= output_binder_rx_dst_rdy_n(1);

   -- the binder at the output of verification core
   output_binder_i: entity work.FL_BINDER
   generic map(
      -- width of one input interface. Should be multiple of 8
      INPUT_WIDTH    => DATA_WIDTH,
      -- number of input interfaces: only 2,4,8,16 supported
      INPUT_COUNT    => 2,
      -- output width - most effective value is INPUT_WIDTH*INPUT_COUNT. In 
      -- other cases FL_TRANSFORMER is instantiated
      OUTPUT_WIDTH   => DATA_WIDTH,
      -- number of parts in one FrameLink frame
      FRAME_PARTS    => 1,
      
      -- select BlockRAM or LUT memory
      LUT_MEMORY     => true,
      -- Queue choosing policy
      SIMPLE_BINDER  => true
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- input FrameLink interface
      RX_DATA        => output_binder_rx_data,
      RX_REM         => output_binder_rx_rem,
      RX_SOF_N       => output_binder_rx_sof_n,
      RX_SOP_N       => output_binder_rx_sop_n,
      RX_EOP_N       => output_binder_rx_eop_n,
      RX_EOF_N       => output_binder_rx_eof_n,
      RX_SRC_RDY_N   => output_binder_rx_src_rdy_n,
      RX_DST_RDY_N   => output_binder_rx_dst_rdy_n,

      -- output FrameLink interface
      TX_DATA        => output_binder_tx_data,
      TX_REM         => output_binder_tx_rem,
      TX_SOF_N       => output_binder_tx_sof_n,
      TX_SOP_N       => output_binder_tx_sop_n,
      TX_EOP_N       => output_binder_tx_eop_n,
      TX_EOF_N       => output_binder_tx_eof_n,
      TX_SRC_RDY_N   => output_binder_tx_src_rdy_n,
      TX_DST_RDY_N   => output_binder_tx_dst_rdy_n
   );

   -- ------------------------------------------------------------------------
   --                              NetCOPE Adder
   -- ------------------------------------------------------------------------

   fl_netcope_adder_in_data       <= output_binder_tx_data;
   fl_netcope_adder_in_rem        <= output_binder_tx_rem;
   fl_netcope_adder_in_sof_n      <= output_binder_tx_sof_n;
   fl_netcope_adder_in_sop_n      <= output_binder_tx_sop_n;
   fl_netcope_adder_in_eop_n      <= output_binder_tx_eop_n;
   fl_netcope_adder_in_eof_n      <= output_binder_tx_eof_n;
   fl_netcope_adder_in_src_rdy_n  <= output_binder_tx_src_rdy_n;
   output_binder_tx_dst_rdy_n     <= fl_netcope_adder_in_dst_rdy_n;

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
