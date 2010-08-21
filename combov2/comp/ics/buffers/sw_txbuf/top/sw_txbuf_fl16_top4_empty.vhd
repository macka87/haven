-- sw_txbuf_fl16_top4_empty.vhd: Empty SW TXBuffer cover for 4 SW_TXBUFs
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
architecture empty of SW_TXBUF_FL16_TOP4 is
   -- ------------------ Signals declaration ----------------------------------
   signal empty_sig      : std_logic_vector(192 - 1 downto 0);
begin

   empty_sig <= CLK              & -- 1
                RESET            & -- 1
                TX0.DST_RDY_N    & -- 1
                TX1.DST_RDY_N    & -- 1
                TX2.DST_RDY_N    & -- 1
                TX3.DST_RDY_N    & -- 1
                WR.ADDR          & -- 32
                WR.DATA          & -- 64
                WR.BE            & -- 8
                WR.REQ           & -- 1
                WR.LENGTH        & -- 12
                WR.SOF           & -- 1
                WR.EOF           & -- 1
                RD.ADDR          & -- 32
                RD.BE            & -- 8
                RD.REQ           & -- 1
                RD.SOF_IN        & -- 1
                RD.EOF_IN        & -- 1
                RD.DST_RDY       & -- 1
                UPS_FL.DST_RDY_N & -- 1
                DNS_FL.DATA      & -- 16
                DNS_FL.SOP_N     & -- 1
                DNS_FL.EOP_N     & -- 1
                DNS_FL.SOF_N     & -- 1
                DNS_FL.EOF_N     & -- 1
                DNS_FL.DREM      & -- 1
                DNS_FL.SRC_RDY_N;  -- 1
                -- ---------------------------------------
                -- 189


   -- output signals
   TX0.SOF_N      <= '1';
   TX0.SOP_N      <= '1';
   TX0.EOP_N      <= '1';
   TX0.EOF_N      <= '1';
   TX0.SRC_RDY_N  <= '1';
   TX0.DATA       <= (others => '0');
   TX0.DREM       <= (others => '0');
   TX1.SOF_N      <= '1';
   TX1.SOP_N      <= '1';
   TX1.EOP_N      <= '1';
   TX1.EOF_N      <= '1';
   TX1.SRC_RDY_N  <= '1';
   TX1.DATA       <= (others => '0');
   TX1.DREM       <= (others => '0');
   TX2.SOF_N      <= '1';
   TX2.SOP_N      <= '1';
   TX2.EOP_N      <= '1';
   TX2.EOF_N      <= '1';
   TX2.SRC_RDY_N  <= '1';
   TX2.DATA       <= (others => '0');
   TX2.DREM       <= (others => '0');
   TX3.SOF_N      <= '1';
   TX3.SOP_N      <= '1';
   TX3.EOP_N      <= '1';
   TX3.EOF_N      <= '1';
   TX3.SRC_RDY_N  <= '1';
   TX3.DATA       <= (others => '0');
   TX3.DREM       <= (others => '0');

   WR.RDY         <= '0';
   RD.ARDY        <= '0';
   RD.DATA        <= (others => '0');
   RD.SRC_RDY     <= '0';
   UPS_FL.DATA    <= (others => '0');
   UPS_FL.DREM    <= (others => '1');
   UPS_FL.SOP_N   <= '0';
   UPS_FL.EOP_N   <= '0';
   UPS_FL.SOF_N   <= '0';
   UPS_FL.EOF_N   <= '0';
   UPS_FL.SRC_RDY_N <= '0';
   DNS_FL.DST_RDY_N <= '1';

end architecture empty;

