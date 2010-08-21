-- ibuf_xgmii_empty.vhd: XGMII IBUF empty architecture
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
use work.lb_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture empty of ibuf_xgmii is

   -- ------------------ Signals declaration ----------------------------------
   signal empty_sig : std_logic_vector(117+FL_WIDTH_TX+log2(FL_WIDTH_TX/8)-1 downto 0);

begin
   empty_sig <= RESET            & -- 1
                XGMII_RXCLK      & -- 1
                XGMII_RXD        & -- 32
                XGMII_RXC        & -- 4

                SAU_ACCEPT       & -- 1
                SAU_DV           & -- 1
   
                CTRL_DATA        & -- FL_WIDTH_TX
                CTRL_REM         & -- log2(FL_WIDTH_TX/8)
                CTRL_SRC_RDY_N   & -- 1
                CTRL_SOP_N       & -- 1
                CTRL_EOP_N       & -- 1
                CTRL_RDY         & -- 1
   
                TX_DST_RDY_N     & -- 1
                FL_CLK           & -- 1

                MI.DWR           & -- 32
                MI.ADDR          & -- 32
                MI.RD            & -- 1
                MI.WR            & -- 1
                MI.BE            & -- 4
                MI_CLK;            -- 1
                -- --------------------
                -- 117 + FL_WIDTH_TX + log2(FL_WIDTH_TX/8)

   INT_CLK           <= '0';

   SAU_REQ           <= '0';

   CTRL_DST_RDY_N    <= '1';
   CTRL_REQ          <= '0';
   CTRL_SEND         <= '0';
   CTRL_RELEASE      <= '0';

   STAT.PAYLOAD_LEN        <= (others => '0');
   STAT.MAC_CHECK_FAILED   <= '0';
   STAT.LEN_BELOW_MIN      <= '0';
   STAT.LEN_OVER_MTU       <= '0';
   STAT.FRAME_ERROR        <= '0';
   STAT.CRC_CHECK_FAILED   <= '0';
   STAT_VLD                <= '0';

   TX_SOF_N          <= '1';
   TX_SOP_N          <= '1';
   TX_EOP_N          <= '1';
   TX_EOF_N          <= '1';
   TX_SRC_RDY_N      <= '1';
   TX_DATA           <= (others => '0');
   TX_REM            <= (others => '0');

   MI.DRD            <= (others => '0');
   MI.DRDY           <= '0';
   MI.ARDY           <= '0';

end architecture empty;
