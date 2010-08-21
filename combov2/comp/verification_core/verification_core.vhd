-- verification_core.vhd: 
-- Copyright (C) 2010 CESNET
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
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
 
      TX_DATA       <= RX_DATA;
      TX_REM        <= RX_REM;
      TX_SOF_N      <= RX_SOF_N;
      TX_SOP_N      <= RX_SOP_N;
      TX_EOP_N      <= RX_EOP_N;
      TX_EOF_N      <= RX_EOF_N;
      TX_SRC_RDY_N  <= RX_SRC_RDY_N;
      RX_DST_RDY_N  <= TX_DST_RDY_N;


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
