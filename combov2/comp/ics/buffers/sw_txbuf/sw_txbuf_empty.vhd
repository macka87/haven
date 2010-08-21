-- sw_txbuf_empty.vhd: SW_TXBUF empty architecture
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
architecture empty of SW_TXBUF is

   -- ------------------ Signals declaration ----------------------------------
   signal empty_sig : std_logic_vector(200 - 1 downto 0);

begin
   empty_sig <= CLK              & -- 1
                RESET            & -- 1
                DST_RDY_N        & -- 1
                WR_ADDR          & -- 32
                WR_DATA          & -- 64
                WR_BE            & -- 8
                WR_REQ           & -- 1
                WR_LENGTH        & -- 12
                WR_SOF           & -- 1
                WR_EOF           & -- 1
                RD_ADDR          & -- 32
                RD_BE            & -- 8
                RD_REQ           & -- 1
                RD_SOF_IN        & -- 1
                RD_EOF_IN        & -- 1
                RD_DST_RDY       & -- 1
                ACK              & -- 1
                CTRL_OFFSET      & -- 20
                CTRL_LENGTH      & -- 12
                CTRL_WRITE;
                -- ---------------------------------------
                -- 200
                
   -- output signals
   SOF_N       <= '1';
   SOP_N       <= '1';
   EOP_N       <= '1';
   EOF_N       <= '1';
   SRC_RDY_N   <= '1';
   DATA_OUT    <= (others => '0');
   REM_OUT     <= (others => '0');
   WR_RDY      <= '0';
   RD_ARDY     <= '0';
   RD_DATA     <= (others => '0');
   RD_SRC_RDY  <= '0';
   DIFF        <= (others => '0');
   READY       <= '0';
   CTRL_READY  <= '0';

end architecture empty;
