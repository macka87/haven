-- ibuf_xgmii.vhd: XGMII Input Buffer
-- Copyright (C) 2007 CESNET
-- Author(s): Polcak Libor <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.lb_pkg.all;
use work.ibuf_pkg.all;
use work.fifo_pkg.all;
use work.ibuf_general_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ibuf_xgmii_arch of ibuf_xgmii is

begin

	-- IBUF_XGMII_norec instantion
	IBUF_XGMII_NORECi : entity work.ibuf_xgmii_norec
	   generic map(
	      DFIFO_SIZE        => DFIFO_SIZE,
	      HFIFO_SIZE        => HFIFO_SIZE,
	      HFIFO_MEMTYPE     => HFIFO_MEMTYPE,
	      CTRL_HDR_EN       => CTRL_HDR_EN,
	      CTRL_FTR_EN       => CTRL_FTR_EN,
	      MACS              => MACS,
	      INBANDFCS         => INBANDFCS,
         CNT_ERROR_SIZE => CNT_ERROR_SIZE,
	      FL_WIDTH_TX       => FL_WIDTH_TX,
	      FL_RELAY          => FL_RELAY
		)
		port map(
	      RESET             => RESET,

	      XGMII_RXCLK       => XGMII_RXCLK,
	      XGMII_RXD         => XGMII_RXD,
	      XGMII_RXC         => XGMII_RXC,

	      INT_CLK           => INT_CLK,
	      INT_RESET         => INT_RESET,

	      SAU_REQ           => SAU_REQ,
	      SAU_ACCEPT        => SAU_ACCEPT,
	      SAU_DV            => SAU_DV,

	      CTRL_CLK          => CTRL_CLK,
	      CTRL_RESET        => CTRL_RESET,
	      CTRL_DATA         => CTRL_DATA,
	      CTRL_REM          => CTRL_REM,
	      CTRL_SRC_RDY_N    => CTRL_SRC_RDY_N,
	      CTRL_SOP_N        => CTRL_SOP_N,
	      CTRL_EOP_N        => CTRL_EOP_N,
	      CTRL_DST_RDY_N    => CTRL_DST_RDY_N,
	      CTRL_REQ          => CTRL_REQ,
	      CTRL_SEND         => CTRL_SEND,
	      CTRL_RELEASE      => CTRL_RELEASE,
	      CTRL_RDY          => CTRL_RDY,

	      STAT              => STAT,
	      STAT_VLD          => STAT_VLD,

         LINK_UP           => LINK_UP,
         INCOMING_PCKT     => INCOMING_PCKT,

	      TX_SOF_N          => TX_SOF_N,
	      TX_SOP_N          => TX_SOP_N,
	      TX_EOP_N          => TX_EOP_N,
	      TX_EOF_N          => TX_EOF_N,
	      TX_SRC_RDY_N      => TX_SRC_RDY_N,
	      TX_DST_RDY_N      => TX_DST_RDY_N,
	      TX_DATA           => TX_DATA,
	      TX_REM            => TX_REM,
	      FL_CLK            => FL_CLK,

	      MI_DWR      		=> MI.DWR,
	      MI_ADDR     		=> MI.ADDR,
	      MI_RD       		=> MI.RD,
	      MI_WR       		=> MI.WR,
	      MI_BE       		=> MI.BE,
	      MI_DRD      		=> MI.DRD,
	      MI_ARDY     		=> MI.ARDY,
	      MI_DRDY     		=> MI.DRDY,
	      MI_CLK            => MI_CLK
		);

end architecture ibuf_xgmii_arch;
-- ----------------------------------------------------------------------------

