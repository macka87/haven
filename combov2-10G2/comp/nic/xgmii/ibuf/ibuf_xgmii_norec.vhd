-- ibuf_xgmii_norec.vhd: XGMII Input Buffer (without inout records)
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
--                       Architecture declaration
-- ----------------------------------------------------------------------------
architecture ibuf_xgmii_norec_arch of ibuf_xgmii_norec is

   -- internal signals
   signal clk_int          : std_logic;
   signal reset_int        : std_logic;
   signal rxdcm_lock       : std_logic;

   -- SDR XGMII protocol
   signal rxd_int          : std_logic_vector(63 downto 0);
   signal rxc_int          : std_logic_vector(7 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                           IBUF Interface
   -- -------------------------------------------------------------------------

   -- IBUF core clock for external components
   INT_CLK     <= clk_int;
   INT_RESET   <= reset_int;

   -- -------------------------------------------------------------------------
   --                              RX Part
   -- -------------------------------------------------------------------------

   -- XGMII_RX instantion
   XGMII_RECEIVERi: entity work.xgmii_rx
   port map(
      XGMII_RX_CLK         => XGMII_RXCLK,
      XGMII_RXD            => XGMII_RXD,
      XGMII_RXC            => XGMII_RXC,
      RESET                => reset_int,
      RX_CLK_INT           => clk_int,
      RXD_INT              => rxd_int,
      RXC_INT              => rxc_int,
      RX_DCM_LOCK          => rxdcm_lock,
      RX_DCM_RESET       	=> RESET
   );

   reset_int <= not rxdcm_lock;

   -- -------------------------------------------------------------------------
   --                SDR XGMII IBUF (without inout records)
   -- -------------------------------------------------------------------------
   IBUF_XGMII_SDR_NORECi: entity work.ibuf_xgmii_sdr_norec
      generic map (
         DFIFO_SIZE        => DFIFO_SIZE,
         HFIFO_SIZE        => HFIFO_SIZE,
         HFIFO_MEMTYPE     => HFIFO_MEMTYPE,
         CTRL_HDR_EN       => CTRL_HDR_EN,
         CTRL_FTR_EN       => CTRL_FTR_EN,
         MACS              => MACS,
         INBANDFCS         => INBANDFCS,
         CNT_ERROR_SIZE    => CNT_ERROR_SIZE,
         FL_WIDTH_TX       => FL_WIDTH_TX,
         FL_RELAY          => FL_RELAY
      )
      port map (
         RESET             => reset_int,

         CLK_INT           => clk_int,
         XGMII_SDR_RXD     => rxd_int,
         XGMII_SDR_RXC     => rxc_int,

         SAU_CLK           => open,
         SAU_RESET         => open,
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

         MI_DWR      		=> MI_DWR,
      	MI_ADDR     		=> MI_ADDR,
      	MI_RD       		=> MI_RD,
      	MI_WR             => MI_WR,
      	MI_BE       		=> MI_BE,
      	MI_DRD      		=> MI_DRD,
      	MI_ARDY     		=> MI_ARDY,
      	MI_DRDY     		=> MI_DRDY,
         MI_CLK            => MI_CLK
      );


end architecture ibuf_xgmii_norec_arch;
-- ----------------------------------------------------------------------------

