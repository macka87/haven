-- application.vhd : Combov2 NetCOPE application module
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--
-- $Id$
--

-- ----------------------------------------------------------------------------
--                             Entity declaration
-- ----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all; 
use work.combov2_core_const.all;
use work.combov2_user_const.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;
use work.addr_space.all;
Library UNISIM;
use UNISIM.vcomponents.all;

architecture full of APPLICATION is

   -- -------------------------------------------------------------------------
   --                                 Constants
   -- -------------------------------------------------------------------------

   -- DMA data width
   constant DMA_DATA_WIDTH       : integer := 64;

   -- verification core data width
   constant VER_CORE_DATA_WIDTH  : integer := 64;

   -- -------------------------------------------------------------------------
   --                                  Signals
   -- -------------------------------------------------------------------------

   -- input FrameLink
   signal fl_input_data        : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal fl_input_rem         : std_logic_vector(log2(DMA_DATA_WIDTH/8)-1 downto 0);
   signal fl_input_sof_n       : std_logic;
   signal fl_input_eof_n       : std_logic;
   signal fl_input_sop_n       : std_logic;
   signal fl_input_eop_n       : std_logic;
   signal fl_input_src_rdy_n   : std_logic;
   signal fl_input_dst_rdy_n   : std_logic;

   -- output FrameLink
   signal fl_output_data       : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal fl_output_rem        : std_logic_vector(log2(DMA_DATA_WIDTH/8)-1 downto 0);
   signal fl_output_sof_n      : std_logic;
   signal fl_output_eof_n      : std_logic;
   signal fl_output_sop_n      : std_logic;
   signal fl_output_eop_n      : std_logic;
   signal fl_output_src_rdy_n  : std_logic;
   signal fl_output_dst_rdy_n  : std_logic;

   -- output FrameLink pipe input
   signal fl_output_pipe_data       : std_logic_vector(DMA_DATA_WIDTH-1 downto 0);
   signal fl_output_pipe_rem        : std_logic_vector(log2(DMA_DATA_WIDTH/8)-1 downto 0);
   signal fl_output_pipe_sof_n      : std_logic;
   signal fl_output_pipe_eof_n      : std_logic;
   signal fl_output_pipe_sop_n      : std_logic;
   signal fl_output_pipe_eop_n      : std_logic;
   signal fl_output_pipe_src_rdy_n  : std_logic;
   signal fl_output_pipe_dst_rdy_n  : std_logic;

   -- verification core input FrameLink
   signal fl_ver_in_data       : std_logic_vector(VER_CORE_DATA_WIDTH-1 downto 0);
   signal fl_ver_in_rem        : std_logic_vector(log2(VER_CORE_DATA_WIDTH/8)-1 downto 0);
   signal fl_ver_in_sof_n      : std_logic;
   signal fl_ver_in_eof_n      : std_logic;
   signal fl_ver_in_sop_n      : std_logic;
   signal fl_ver_in_eop_n      : std_logic;
   signal fl_ver_in_src_rdy_n  : std_logic;
   signal fl_ver_in_dst_rdy_n  : std_logic;

   -- verification core output FrameLink
   signal fl_ver_out_data      : std_logic_vector(VER_CORE_DATA_WIDTH-1 downto 0);
   signal fl_ver_out_rem       : std_logic_vector(log2(VER_CORE_DATA_WIDTH/8)-1 downto 0);
   signal fl_ver_out_sof_n     : std_logic;
   signal fl_ver_out_eof_n     : std_logic;
   signal fl_ver_out_sop_n     : std_logic;
   signal fl_ver_out_eop_n     : std_logic;
   signal fl_ver_out_src_rdy_n : std_logic;
   signal fl_ver_out_dst_rdy_n : std_logic;

   -- input signals for FrameLink watch
   signal fl_watch_sof_n       : std_logic_vector(1 downto 0);
   signal fl_watch_eof_n       : std_logic_vector(1 downto 0);
   signal fl_watch_sop_n       : std_logic_vector(1 downto 0);
   signal fl_watch_eop_n       : std_logic_vector(1 downto 0);
   signal fl_watch_src_rdy_n   : std_logic_vector(1 downto 0);
   signal fl_watch_dst_rdy_n   : std_logic_vector(1 downto 0);

   -- MI32 interface for watches
   signal mi_watch_dwr         : std_logic_vector(31 downto 0);
   signal mi_watch_addr        : std_logic_vector(31 downto 0);
   signal mi_watch_rd          : std_logic;
   signal mi_watch_wr          : std_logic;
   signal mi_watch_be          : std_logic_vector(3 downto 0);
   signal mi_watch_drd         : std_logic_vector(31 downto 0);
   signal mi_watch_ardy        : std_logic;
   signal mi_watch_drdy        : std_logic;

   -- MI32 interface for verification core
   signal mi_ver_dwr           : std_logic_vector(31 downto 0);
   signal mi_ver_addr          : std_logic_vector(31 downto 0);
   signal mi_ver_rd            : std_logic;
   signal mi_ver_wr            : std_logic;
   signal mi_ver_be            : std_logic_vector(3 downto 0);
   signal mi_ver_drd           : std_logic_vector(31 downto 0);
   signal mi_ver_ardy          : std_logic;
   signal mi_ver_drdy          : std_logic;

   -- MI32 splitter output
   signal mi_spl_out_dwr        : std_logic_vector(63 downto 0);
   signal mi_spl_out_addr       : std_logic_vector(63 downto 0);
   signal mi_spl_out_rd         : std_logic_vector(1 downto 0);
   signal mi_spl_out_wr         : std_logic_vector(1 downto 0);
   signal mi_spl_out_be         : std_logic_vector(7 downto 0);
   signal mi_spl_out_drd        : std_logic_vector(63 downto 0);
   signal mi_spl_out_ardy       : std_logic_vector(1 downto 0);
   signal mi_spl_out_drdy       : std_logic_vector(1 downto 0);

-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   -- Mapping of input signals
   -- -------------------------------------------------------------------------
   fl_input_data        <= RX_DATA;
   fl_input_rem         <= RX_DREM;
   fl_input_sof_n       <= RX_SOF_N;
   fl_input_eof_n       <= RX_EOF_N;
   fl_input_sop_n       <= RX_SOP_N;
   fl_input_eop_n       <= RX_EOP_N;
   fl_input_src_rdy_n   <= RX_SRC_RDY_N;
   RX_DST_RDY_N         <= fl_input_dst_rdy_n;

   -- -------------------------------------------------------------------------
   -- Mapping of output signals
   -- -------------------------------------------------------------------------
   TX_DATA               <= fl_output_data;
   TX_DREM               <= fl_output_rem;
   TX_SOF_N              <= fl_output_sof_n;
   TX_EOF_N              <= fl_output_eof_n;
   TX_SOP_N              <= fl_output_sop_n;
   TX_EOP_N              <= fl_output_eop_n;
   TX_SRC_RDY_N          <= fl_output_src_rdy_n;
   fl_output_dst_rdy_n   <= TX_DST_RDY_N;

   -- -------------------------------------------------------------------------
   -- Verification Core
   -- -------------------------------------------------------------------------
   ver_core_i: entity work.verification_core
   generic map(
      -- frame data width in bits
      DATA_WIDTH     => VER_CORE_DATA_WIDTH
   )
   port map(
      CLK           => CLK,
      RESET         => RESET,

      -- input interface
      RX_DATA       => fl_ver_in_data,
      RX_REM        => fl_ver_in_rem,
      RX_SOF_N      => fl_ver_in_sof_n,
      RX_SOP_N      => fl_ver_in_sop_n,
      RX_EOP_N      => fl_ver_in_eop_n,
      RX_EOF_N      => fl_ver_in_eof_n,
      RX_SRC_RDY_N  => fl_ver_in_src_rdy_n, 
      RX_DST_RDY_N  => fl_ver_in_dst_rdy_n, 
      
      -- output interface
      TX_DATA       => fl_ver_out_data,
      TX_REM        => fl_ver_out_rem,
      TX_SOF_N      => fl_ver_out_sof_n,
      TX_SOP_N      => fl_ver_out_sop_n,
      TX_EOP_N      => fl_ver_out_eop_n,
      TX_EOF_N      => fl_ver_out_eof_n,
      TX_SRC_RDY_N  => fl_ver_out_src_rdy_n, 
      TX_DST_RDY_N  => fl_ver_out_dst_rdy_n, 

      -- MI32 interface
      MI32_DWR      => mi_ver_dwr,
      MI32_ADDR     => mi_ver_addr,
      MI32_RD       => mi_ver_rd,
      MI32_WR       => mi_ver_wr,
      MI32_BE       => mi_ver_be,
      MI32_DRD      => mi_ver_drd,
      MI32_ARDY     => mi_ver_ardy,
      MI32_DRDY     => mi_ver_drdy
   );


   -- -------------------------------------------------------------------------
   -- RX FrameLink transformer
   -- -------------------------------------------------------------------------
   fl_transformer_rx_i: entity work.FL_TRANSFORMER
   generic map(
      -- FrameLink data buses width
      -- only 8, 16, 32, 64 and 128 supported
      RX_DATA_WIDTH  => DMA_DATA_WIDTH,
      TX_DATA_WIDTH  => VER_CORE_DATA_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- RX interface
      RX_DATA        => fl_input_data,
      RX_REM         => fl_input_rem,
      RX_SOF_N       => fl_input_sof_n,
      RX_EOF_N       => fl_input_eof_n,
      RX_SOP_N       => fl_input_sop_n,
      RX_EOP_N       => fl_input_eop_n,
      RX_SRC_RDY_N   => fl_input_src_rdy_n,
      RX_DST_RDY_N   => fl_input_dst_rdy_n,

      -- TX interface
      TX_DATA        => fl_ver_in_data,
      TX_REM         => fl_ver_in_rem,
      TX_SOF_N       => fl_ver_in_sof_n,
      TX_EOF_N       => fl_ver_in_eof_n,
      TX_SOP_N       => fl_ver_in_sop_n,
      TX_EOP_N       => fl_ver_in_eop_n,
      TX_SRC_RDY_N   => fl_ver_in_src_rdy_n,
      TX_DST_RDY_N   => fl_ver_in_dst_rdy_n
   );

   -- -------------------------------------------------------------------------
   -- TX FrameLink transformer
   -- -------------------------------------------------------------------------
   fl_transformer_tx_i: entity work.FL_TRANSFORMER
   generic map(
      -- FrameLink data buses width
      -- only 8, 16, 32, 64 and 128 supported
      RX_DATA_WIDTH  => VER_CORE_DATA_WIDTH,
      TX_DATA_WIDTH  => DMA_DATA_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- RX interface
      RX_DATA        => fl_ver_out_data,
      RX_REM         => fl_ver_out_rem,
      RX_SOF_N       => fl_ver_out_sof_n,
      RX_EOF_N       => fl_ver_out_eof_n,
      RX_SOP_N       => fl_ver_out_sop_n,
      RX_EOP_N       => fl_ver_out_eop_n,
      RX_SRC_RDY_N   => fl_ver_out_src_rdy_n,
      RX_DST_RDY_N   => fl_ver_out_dst_rdy_n,

      -- TX interface
      TX_DATA        => fl_output_pipe_data,
      TX_REM         => fl_output_pipe_rem,
      TX_SOF_N       => fl_output_pipe_sof_n,
      TX_EOF_N       => fl_output_pipe_eof_n,
      TX_SOP_N       => fl_output_pipe_sop_n,
      TX_EOP_N       => fl_output_pipe_eop_n,
      TX_SRC_RDY_N   => fl_output_pipe_src_rdy_n,
      TX_DST_RDY_N   => fl_output_pipe_dst_rdy_n
   );

   -- -------------------------------------------------------------------------
   -- Output FrameLink pipe 
   -- -------------------------------------------------------------------------
   fl_pipe_i: entity work.FL_PIPE
   generic map(
      DATA_WIDTH  => DMA_DATA_WIDTH,
      USE_OUTREG  => true
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- RX interface
      RX_DATA        => fl_output_pipe_data,
      RX_REM         => fl_output_pipe_rem,
      RX_SOF_N       => fl_output_pipe_sof_n,
      RX_EOF_N       => fl_output_pipe_eof_n,
      RX_SOP_N       => fl_output_pipe_sop_n,
      RX_EOP_N       => fl_output_pipe_eop_n,
      RX_SRC_RDY_N   => fl_output_pipe_src_rdy_n,
      RX_DST_RDY_N   => fl_output_pipe_dst_rdy_n,

      -- TX interface
      TX_DATA        => fl_output_data,
      TX_REM         => fl_output_rem,
      TX_SOF_N       => fl_output_sof_n,
      TX_EOF_N       => fl_output_eof_n,
      TX_SOP_N       => fl_output_sop_n,
      TX_EOP_N       => fl_output_eop_n,
      TX_SRC_RDY_N   => fl_output_src_rdy_n,
      TX_DST_RDY_N   => fl_output_dst_rdy_n
   );

   -- -------------------------------------------------------------------------
   -- FrameLink watch
   -- -------------------------------------------------------------------------
   fl_watch_i: entity work.FL_WATCH_NOREC
   generic map(
      INTERFACES     => 2,
      CNTR_WIDTH     => 32,
      PIPELINE_LEN   => 2,
      GUARD          => true,
      HEADER         => false,
      FOOTER         => false
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
                                 
      SOF_N          => fl_watch_sof_n,
      EOF_N          => fl_watch_eof_n,
      SOP_N          => fl_watch_sop_n,
      EOP_N          => fl_watch_eop_n,
      DST_RDY_N      => fl_watch_dst_rdy_n,
      SRC_RDY_N      => fl_watch_src_rdy_n,
                                 
      FRAME_ERR      => open,
                                 
      MI_DWR         => mi_watch_dwr,
      MI_ADDR        => mi_watch_addr,
      MI_RD          => mi_watch_rd,
      MI_WR          => mi_watch_wr,
      MI_BE          => mi_watch_be,
      MI_DRD         => mi_watch_drd,
      MI_ARDY        => mi_watch_ardy,
      MI_DRDY        => mi_watch_drdy
   );

   fl_watch_sof_n      <= fl_output_pipe_sof_n     & fl_input_sof_n;
   fl_watch_eof_n      <= fl_output_pipe_eof_n     & fl_input_eof_n;
   fl_watch_sop_n      <= fl_output_pipe_sop_n     & fl_input_sop_n;
   fl_watch_eop_n      <= fl_output_pipe_eop_n     & fl_input_eop_n;
   fl_watch_dst_rdy_n  <= fl_output_pipe_dst_rdy_n & fl_input_dst_rdy_n;
   fl_watch_src_rdy_n  <= fl_output_pipe_src_rdy_n & fl_input_src_rdy_n;


   -- -------------------------------------------------------------------------
   -- MI Splitter plus
   -- -------------------------------------------------------------------------
   mi_splitter_plus_i: entity work.MI_SPLITTER_PLUS
   generic map(
      -- Data width
      DATA_WIDTH    => 32,
      -- Number of output ports
      ITEMS         => 2,
      -- Bits of address that should been compared
      ADDR_CMP_MASK => X"FFFFFFFF",
      -- Bases of address spaces (base of port0 is 0x00000000)
      PORT1_BASE    => X"00100000",
      -- Input pipeline
      PIPE          => true,
      PIPE_OUTREG   => true
   )
   port map(
      -- Common interface -----------------------------------------------------
      CLK         => CLK,
      RESET       => RESET,
      
      -- Input MI interface ---------------------------------------------------
      IN_DWR      => MI32_DWR,
      IN_ADDR     => MI32_ADDR,
      IN_BE       => MI32_BE,
      IN_RD       => MI32_RD,
      IN_WR       => MI32_WR,
      IN_ARDY     => MI32_ARDY,
      IN_DRD      => MI32_DRD,
      IN_DRDY     => MI32_DRDY,
      
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

   mi_watch_dwr       <= mi_spl_out_dwr(31 downto 0);
   mi_watch_addr      <= mi_spl_out_addr(31 downto 0);
   mi_watch_be        <= mi_spl_out_be(3 downto 0);
   mi_watch_rd        <= mi_spl_out_rd(0);
   mi_watch_wr        <= mi_spl_out_wr(0);

   mi_ver_dwr         <= mi_spl_out_dwr(63 downto 32);
   mi_ver_addr        <= mi_spl_out_addr(63 downto 32);
   mi_ver_be          <= mi_spl_out_be(7 downto 4);
   mi_ver_rd          <= mi_spl_out_rd(1);
   mi_ver_wr          <= mi_spl_out_wr(1);

   mi_spl_out_drd     <= mi_ver_drd  & mi_watch_drd;
   mi_spl_out_ardy    <= mi_ver_ardy & mi_watch_ardy;
   mi_spl_out_drdy    <= mi_ver_drdy & mi_watch_drdy;

end architecture;
