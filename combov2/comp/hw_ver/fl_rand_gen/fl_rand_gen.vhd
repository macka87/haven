-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================

-- generator of random FrameLink frames
entity FL_RAND_GEN is
  generic(
     -- the width of the output FrameLink
     DATA_WIDTH   : integer := 64;
     -- ID of the endpoint that is the destination of the generated frames
     ENDPOINT_ID  : integer := 0
  );
  
  port
  (
     -- common signals
     CLK         : in  std_logic;
     RESET       : in  std_logic;

     -- MI32 interface
     MI_DWR    :  in std_logic_vector(31 downto 0);
     MI_ADDR   :  in std_logic_vector(31 downto 0);
     MI_RD     :  in std_logic;
     MI_WR     :  in std_logic;
     MI_BE     :  in std_logic_vector( 3 downto 0);
     MI_DRD    : out std_logic_vector(31 downto 0);
     MI_ARDY   : out std_logic;
     MI_DRDY   : out std_logic;

     -- output FrameLink
     TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
     TX_REM      : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
     TX_SOF_N    : out std_logic;
     TX_EOF_N    : out std_logic;
     TX_SOP_N    : out std_logic;
     TX_EOP_N    : out std_logic;
     TX_SRC_RDY_N: out std_logic;
     TX_DST_RDY_N:  in std_logic
  );
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of FL_RAND_GEN is

-- ==========================================================================
--                               CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                SIGNALS
-- ==========================================================================

-- input signals
signal sig_mi_dwr       : std_logic_vector(31 downto 0);
signal sig_mi_addr      : std_logic_vector(31 downto 0);
signal sig_mi_rd        : std_logic;
signal sig_mi_wr        : std_logic;
signal sig_mi_be        : std_logic_vector( 3 downto 0);
signal sig_mi_drd       : std_logic_vector(31 downto 0);
signal sig_mi_ardy      : std_logic;
signal sig_mi_drdy      : std_logic;

-- output signals
signal sig_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal sig_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal sig_tx_sof_n     : std_logic;
signal sig_tx_eof_n     : std_logic;
signal sig_tx_sop_n     : std_logic;
signal sig_tx_eop_n     : std_logic;
signal sig_tx_src_rdy_n : std_logic;
signal sig_tx_dst_rdy_n : std_logic;

-- MI32 Splitter input signals
signal mi_splitter_dwr  : std_logic_vector(31 downto 0);
signal mi_splitter_addr : std_logic_vector(31 downto 0);
signal mi_splitter_be   : std_logic_vector(3 downto 0);
signal mi_splitter_rd   : std_logic;
signal mi_splitter_wr   : std_logic;
signal mi_splitter_ardy : std_logic;
signal mi_splitter_drd  : std_logic_vector(31 downto 0);
signal mi_splitter_drdy : std_logic;

-- MI32 Splitter output signals
signal mi_spl_out_dwr  : std_logic_vector(63 downto 0);
signal mi_spl_out_addr : std_logic_vector(63 downto 0);
signal mi_spl_out_be   : std_logic_vector(7 downto 0);
signal mi_spl_out_rd   : std_logic_vector(1 downto 0);
signal mi_spl_out_wr   : std_logic_vector(1 downto 0);
signal mi_spl_out_ardy : std_logic_vector(1 downto 0);
signal mi_spl_out_drd  : std_logic_vector(63 downto 0);
signal mi_spl_out_drdy : std_logic_vector(1 downto 0);

-- Random generator MI32 signals
signal rand_gen_mi_dwr  : std_logic_vector(31 downto 0);
signal rand_gen_mi_addr : std_logic_vector(31 downto 0);
signal rand_gen_mi_be   : std_logic_vector(3 downto 0);
signal rand_gen_mi_rd   : std_logic;
signal rand_gen_mi_wr   : std_logic;
signal rand_gen_mi_ardy : std_logic;
signal rand_gen_mi_drd  : std_logic_vector(31 downto 0);
signal rand_gen_mi_drdy : std_logic;

-- Random generator output
signal rand_gen_rnd_val : std_logic;
signal rand_gen_rnd_run : std_logic;
signal rand_gen_rnd_num : std_logic_vector(DATA_WIDTH-1 downto 0);

-- FrameLink adapter input
signal fl_adapter_gen_flow : std_logic_vector(DATA_WIDTH-1 downto 0);

-- FrameLink adapter MI32 signals
signal fl_adapter_mi_dwr  : std_logic_vector(31 downto 0);
signal fl_adapter_mi_addr : std_logic_vector(31 downto 0);
signal fl_adapter_mi_be   : std_logic_vector(3 downto 0);
signal fl_adapter_mi_rd   : std_logic;
signal fl_adapter_mi_wr   : std_logic;
signal fl_adapter_mi_ardy : std_logic;
signal fl_adapter_mi_drd  : std_logic_vector(31 downto 0);
signal fl_adapter_mi_drdy : std_logic;

-- FrameLink adapter output FrameLink
signal fl_adapter_tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal fl_adapter_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal fl_adapter_tx_sof_n     : std_logic;
signal fl_adapter_tx_eof_n     : std_logic;
signal fl_adapter_tx_sop_n     : std_logic;
signal fl_adapter_tx_eop_n     : std_logic;
signal fl_adapter_tx_src_rdy_n : std_logic;
signal fl_adapter_tx_dst_rdy_n : std_logic;


-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin

   -- mapping input signals
   sig_mi_dwr    <= MI_DWR;
   sig_mi_addr   <= MI_ADDR;
   sig_mi_rd     <= MI_RD;
   sig_mi_wr     <= MI_WR;
   sig_mi_be     <= MI_BE;
   MI_DRD        <= sig_mi_drd;
   MI_ARDY       <= sig_mi_ardy;
   MI_DRDY       <= sig_mi_drdy;

   --
   rand_gen_mi_dwr              <= mi_spl_out_dwr(63 downto 32);
   rand_gen_mi_addr             <= mi_spl_out_addr(63 downto 32);
   rand_gen_mi_be               <= mi_spl_out_be(7 downto 4);
   rand_gen_mi_rd               <= mi_spl_out_rd(1);
   rand_gen_mi_wr               <= mi_spl_out_wr(1);
   mi_spl_out_ardy(1)           <= rand_gen_mi_ardy;
   mi_spl_out_drd(63 downto 32) <= rand_gen_mi_drd;
   mi_spl_out_drdy(1)           <= rand_gen_mi_drdy;

   -- the random number generator -------------------------------------------
   rand_gen_i: entity work.rand_gen
   generic map(
     OUTPUT_WIDTH => DATA_WIDTH
   )
   port map(
     -- common signals
     CLK       => CLK,
     RESET     => RESET,

     -- MI32 interface
     MI_DWR    => rand_gen_mi_dwr,
     MI_ADDR   => rand_gen_mi_addr,
     MI_RD     => rand_gen_mi_rd,
     MI_WR     => rand_gen_mi_wr,
     MI_BE     => rand_gen_mi_be,
     MI_DRD    => rand_gen_mi_drd,
     MI_ARDY   => rand_gen_mi_ardy,
     MI_DRDY   => rand_gen_mi_drdy,

     -- output
     RND_VAL   => rand_gen_rnd_val,
     RND_NUM   => rand_gen_rnd_num,
     RND_RUN   => rand_gen_rnd_run
   );

   rand_gen_rnd_run <= '1';

   --
   fl_adapter_gen_flow <= rand_gen_rnd_num;

   fl_adapter_mi_dwr              <= mi_spl_out_dwr(31 downto 0);
   fl_adapter_mi_addr             <= mi_spl_out_addr(31 downto 0);
   fl_adapter_mi_be               <= mi_spl_out_be(3 downto 0);
   fl_adapter_mi_rd               <= mi_spl_out_rd(0);
   fl_adapter_mi_wr               <= mi_spl_out_wr(0);
   mi_spl_out_ardy(0)             <= fl_adapter_mi_ardy;
   mi_spl_out_drd(31 downto 0)    <= fl_adapter_mi_drd;
   mi_spl_out_drdy(0)             <= fl_adapter_mi_drdy;

   -- the FrameLink adapter -------------------------------------------------
   fl_adapter_i: entity work.fl_adapter_unit
   generic map(
     DATA_WIDTH   => DATA_WIDTH,
     ENDPOINT_ID  => ENDPOINT_ID
   )
   port map(
     -- common signals
     CLK       => CLK,
     RESET     => RESET,

     -- MI32 interface
     MI_DWR    => fl_adapter_mi_dwr,
     MI_ADDR   => fl_adapter_mi_addr,
     MI_RD     => fl_adapter_mi_rd,
     MI_WR     => fl_adapter_mi_wr,
     MI_BE     => fl_adapter_mi_be,
     MI_DRD    => fl_adapter_mi_drd,
     MI_ARDY   => fl_adapter_mi_ardy,
     MI_DRDY   => fl_adapter_mi_drdy,

     -- Input data interface
     GEN_FLOW  => fl_adapter_gen_flow,

     -- Output FrameLink
     TX_DATA          => fl_adapter_tx_data,
     TX_REM           => fl_adapter_tx_rem,
     TX_SOF_N         => fl_adapter_tx_sof_n,
     TX_EOF_N         => fl_adapter_tx_eof_n,
     TX_SOP_N         => fl_adapter_tx_sop_n,
     TX_EOP_N         => fl_adapter_tx_eop_n,
     TX_SRC_RDY_N     => fl_adapter_tx_src_rdy_n,
     TX_DST_RDY_N     => fl_adapter_tx_dst_rdy_n
   );

   sig_tx_data               <= fl_adapter_tx_data;
   sig_tx_rem                <= fl_adapter_tx_rem;
   sig_tx_sof_n              <= fl_adapter_tx_sof_n;
   sig_tx_eof_n              <= fl_adapter_tx_eof_n;
   sig_tx_sop_n              <= fl_adapter_tx_sop_n;
   sig_tx_eop_n              <= fl_adapter_tx_eop_n;
   sig_tx_src_rdy_n          <= fl_adapter_tx_src_rdy_n;
   fl_adapter_tx_dst_rdy_n   <= sig_tx_dst_rdy_n;

   -- -----------------------------------------------------------------------
   --                      The Address Space:
   --
   -- 0x0000 - 0x1FFF : The random number generator
   -- 0x1000 - 0x1FFF : The FrameLink adapter
   -- -----------------------------------------------------------------------

   --
   mi_splitter_dwr   <= sig_mi_dwr;
   mi_splitter_addr  <= sig_mi_addr;
   mi_splitter_be    <= sig_mi_be;
   mi_splitter_rd    <= sig_mi_rd;
   mi_splitter_wr    <= sig_mi_wr;
   sig_mi_ardy       <= mi_splitter_ardy;
   sig_mi_drd        <= mi_splitter_drd;
   sig_mi_drdy       <= mi_splitter_drdy;

   -- MI Splitter Ondrik's --------------------------------------------------
   mi_splitter_ondriks_i: entity work.MI_SPLITTER_ONDRIKS
   generic map(
      -- Data width
      DATA_WIDTH    => 32,
      -- Number of output ports
      ITEMS         => 2,

      -- ADDRESS SPACE

      -- PORT0: 0x00000000 -- 0x00000FFF
      PORT0_BASE    => X"00000000",
      PORT0_LIMIT   => X"00001000",
      -- PORT1: 0x00001000 -- 0x00001FFF
      PORT1_BASE    => X"00001000",
      PORT1_LIMIT   => X"00001000",

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

   -- mapping outputs
   TX_DATA          <= sig_tx_data;
   TX_REM           <= sig_tx_rem;
   TX_SOF_N         <= sig_tx_sof_n;
   TX_EOF_N         <= sig_tx_eof_n;
   TX_SOP_N         <= sig_tx_sop_n;
   TX_EOP_N         <= sig_tx_eop_n;
   TX_SRC_RDY_N     <= sig_tx_src_rdy_n;
   sig_tx_dst_rdy_n <= TX_DST_RDY_N;
 
end architecture;
