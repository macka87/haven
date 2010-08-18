-- sequencer_empty.vhd: FrameLink Sequencer empty architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture empty of FL_SEQUENCER is

   -- ------------------ Signals declaration ----------------------------------
   signal empty_sig : std_logic_vector(3 + 5*INPUT_COUNT + 
   INPUT_COUNT*INPUT_WIDTH + INPUT_COUNT*log2(INPUT_WIDTH/8)-1 downto 0);

begin
   
   empty_sig <= CLK              & -- 1
                RESET            & -- 1
                RX_SOF_N         & -- INPUT_COUNT
                RX_SOP_N         & -- INPUT_COUNT
                RX_EOP_N         & -- INPUT_COUNT
                RX_EOF_N         & -- INPUT_COUNT
                RX_SRC_RDY_N     & -- INPUT_COUNT
                RX_DATA          & -- INPUT_COUNT*INPUT_WIDTH
                RX_REM           & -- INPUT_COUNT*log2(INPUT_WIDTH/8)
                TX_DST_RDY_N;      -- 1 
                -- --------------------------------------------
                -- 3 + 5*INPUT_COUNT + INPUT_COUNT*INPUT_WIDTH + 
                -- + INPUT_COUNT*log2(INPUT_WIDTH/8)

   
   -- output signals
   RX_DST_RDY_N   <= (others => '0');
   TX_SOF_N       <= '1';
   TX_SOP_N       <= '1';
   TX_EOP_N       <= '1';
   TX_EOF_N       <= '1';
   TX_SRC_RDY_N   <= '1';
   TX_DATA        <= (others => '0');
   TX_REM         <= (others => '0');

end architecture empty;
