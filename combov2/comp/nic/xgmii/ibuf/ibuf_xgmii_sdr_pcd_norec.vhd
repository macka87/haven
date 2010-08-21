-- ibuf_xgmii_sdr_pcd_norec.vhd: Input Buffer with unified PACODAG interface
-- Copyright (C) 2009 CESNET
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
--

library IEEE;
use IEEE.std_logic_1164.all;
use work.math_pack.all;
use work.ibuf_general_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_xgmii_sdr_pcd_norec is

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- IBUF instantination ---------------------------------------------------
   IBUF_U : entity work.ibuf_xgmii_sdr_norec
      generic map(
         DFIFO_SIZE     => DFIFO_SIZE,
         HFIFO_SIZE     => HFIFO_SIZE,
         HFIFO_MEMTYPE  => HFIFO_MEMTYPE,
         CTRL_HDR_EN    => CTRL_HDR_EN,
         CTRL_FTR_EN    => CTRL_FTR_EN,
         MACS           => MACS,
         INBANDFCS      => INBANDFCS,
         CNT_ERROR_SIZE => CNT_ERROR_SIZE,
         FL_WIDTH_TX    => FL_WIDTH_TX,
         FL_RELAY       => FL_RELAY
      )
      port map (
         RESET          => RESET,

         -- XGMII RX interface
         CLK_INT        => RXCLK,
         XGMII_SDR_RXD  => RXD,
         XGMII_SDR_RXC  => RXC,

         -- Sampling unit interface
         SAU_CLK        => SAU_CLK,
         SAU_RESET      => SAU_RESET,
         SAU_REQ        => SAU_REQ,
         SAU_ACCEPT     => SAU_ACCEPT,
         SAU_DV         => SAU_DV,

         -- PACODAG interface
         CTRL_CLK       => CTRL_CLK,
         CTRL_RESET     => CTRL_RESET,
         CTRL_DATA      => CTRL_DATA,
         CTRL_REM       => CTRL_REM,
         CTRL_SRC_RDY_N => CTRL_SRC_RDY_N,
         CTRL_SOP_N     => CTRL_SOP_N,
         CTRL_EOP_N     => CTRL_EOP_N,
         CTRL_DST_RDY_N => CTRL_DST_RDY_N,
         CTRL_REQ       => CTRL_SOP,
         CTRL_SEND      => STAT_DV,
         CTRL_RELEASE   => open,
         CTRL_RDY       => CTRL_RDY,

         -- IBUF status interface
         STAT           => STAT,
         STAT_VLD       => open, -- Active when CTRL_SEND = '1'
         FRAME_RECEIVED => FRAME_RECEIVED,
         FRAME_DISCARDED=> FRAME_DISCARDED,
         BUFFER_OVF     => BUFFER_OVF,

         LINK_UP        => LINK_UP,
         INCOMING_PCKT  => INCOMING_PCKT,

         -- FrameLink interface
         FL_CLK         => FL_CLK,
         TX_DATA        => TX_DATA,
         TX_REM         => TX_REM,
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         TX_SOF_N       => TX_SOF_N,
         TX_SOP_N       => TX_SOP_N,
         TX_EOF_N       => TX_EOF_N,
         TX_EOP_N       => TX_EOP_N,
         TX_DST_RDY_N   => TX_DST_RDY_N,

         -- Address decoder interface
         MI_CLK   => MI_CLK,
         MI_DWR   => MI_DWR,
         MI_ADDR  => MI_ADDR,
         MI_RD    => MI_RD,
         MI_WR    => MI_WR,
         MI_BE    => MI_BE,
         MI_DRD   => MI_DRD,
         MI_ARDY  => MI_ARDY,
         MI_DRDY  => MI_DRDY
      );

end architecture full;
