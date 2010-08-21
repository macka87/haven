-- verification_core.vhd: Architecture of verification core
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

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

begin

   -- ------------------------------------------------------------------------
   --                              Frame Meter
   -- ------------------------------------------------------------------------
   frame_meter_i: entity work.FL_FRAME_METER
   generic map(
      -- frame data width in bits
      DATA_WIDTH     => DATA_WIDTH,
      -- block size in Bytes. Should be power of 2. Has to be greater than MTU!
      BLOCK_SIZE     => 4096,
      -- number of parts in frame (header, payload)
      FRAME_PARTS    => 1
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
