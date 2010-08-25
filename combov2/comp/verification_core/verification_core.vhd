-- verification_core.vhd: Architecture of verification core
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
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

   signal fl_shortener_out_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_shortener_out_rem        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal fl_shortener_out_sof_n      : std_logic;
   signal fl_shortener_out_sop_n      : std_logic;
   signal fl_shortener_out_eop_n      : std_logic;
   signal fl_shortener_out_eof_n      : std_logic;
   signal fl_shortener_out_src_rdy_n  : std_logic;
   signal fl_shortener_out_dst_rdy_n  : std_logic;

begin

--   -- ------------------------------------------------------------------------
--   --                              Frame Meter
--   -- ------------------------------------------------------------------------
--   frame_meter_i: entity work.FL_FRAME_METER
--   generic map(
--      -- frame data width in bits
--      DATA_WIDTH     => DATA_WIDTH,
--      -- block size in Bytes. Should be power of 2. Has to be greater than MTU!
--      BLOCK_SIZE     => 4096,
--      -- number of parts in frame (header, payload)
--      FRAME_PARTS    => 1
--   )
--   port map(
--      CLK           => CLK,
--      RESET         => RESET,
--
--      -- input interface
--      RX_DATA       => RX_DATA,
--      RX_REM        => RX_REM,
--      RX_SOF_N      => RX_SOF_N,
--      RX_SOP_N      => RX_SOP_N,
--      RX_EOP_N      => RX_EOP_N,
--      RX_EOF_N      => RX_EOF_N,
--      RX_SRC_RDY_N  => RX_SRC_RDY_N, 
--      RX_DST_RDY_N  => RX_DST_RDY_N, 
--      
--      -- output interface
--      TX_DATA       => TX_DATA,
--      TX_REM        => TX_REM,
--      TX_SOF_N      => TX_SOF_N,
--      TX_SOP_N      => TX_SOP_N,
--      TX_EOP_N      => TX_EOP_N,
--      TX_EOF_N      => TX_EOF_N,
--      TX_SRC_RDY_N  => TX_SRC_RDY_N,
--      TX_DST_RDY_N  => TX_DST_RDY_N
--   );
 

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
      CLK           => CLK,
      RESET         => RESET,

      -- input interface
      RX_DATA       => RX_DATA,
      RX_REM        => RX_REM,
      RX_SOF_N      => RX_SOF_N,
      RX_SOP_N      => RX_SOP_N,
      RX_EOP_N      => RX_EOP_N,
      RX_EOF_N      => RX_EOF_N,
      RX_SRC_RDY_N  => RX_SRC_RDY_N, 
      RX_DST_RDY_N  => RX_DST_RDY_N, 
      
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
      RX_DATA       => fl_shortener_out_data,
      RX_REM        => fl_shortener_out_rem,
      RX_SOF_N      => fl_shortener_out_sof_n,
      RX_SOP_N      => fl_shortener_out_sop_n,
      RX_EOP_N      => fl_shortener_out_eop_n,
      RX_EOF_N      => fl_shortener_out_eof_n,
      RX_SRC_RDY_N  => fl_shortener_out_src_rdy_n,
      RX_DST_RDY_N  => fl_shortener_out_dst_rdy_n,
      
      -- output interface
      TX_DATA       => TX_DATA,
      TX_REM        => TX_REM,
      TX_SOF_N      => TX_SOF_N,
      TX_SOP_N      => TX_SOP_N,
      TX_EOP_N      => TX_EOP_N,
      TX_EOF_N      => TX_EOF_N,
      TX_SRC_RDY_N  => TX_SRC_RDY_N,
      TX_DST_RDY_N  => TX_DST_RDY_N
   );

--   TX_DATA       <= RX_DATA;
--   TX_REM        <= RX_REM;
--   TX_SOF_N      <= RX_SOF_N;
--   TX_SOP_N      <= RX_SOP_N;
--   TX_EOP_N      <= RX_EOP_N;
--   TX_EOF_N      <= RX_EOF_N;
--   TX_SRC_RDY_N  <= RX_SRC_RDY_N;
--   RX_DST_RDY_N  <= TX_DST_RDY_N;


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
