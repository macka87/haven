--
-- obuf_xgmii.vhd: XGMII Output Buffer
-- Copyright (C) 2008 CESNET
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
-- TODO: use appropriate reset for every clock domain
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.xgmii_obuf_pkg.all;
use work.lb_pkg.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture obuf_xgmii_sdr_arch of obuf_xgmii_sdr is

begin

   -- -----------------------------------------------------------------
   --                           NOREC OBUF
   -- -----------------------------------------------------------------

   sdrobufi: entity work.obuf_xgmii_sdr_norec
   generic map(
      CTRL_CMD          => CTRL_CMD,
      FL_WIDTH_RX       => FL_WIDTH_RX,
      DFIFO_SIZE        => DFIFO_SIZE,
      HFIFO_SIZE        => HFIFO_SIZE,
      HFIFO_MEMTYPE     => HFIFO_MEMTYPE
   )
   port map(
      CLK_INT           => CLK_INT,
      RESET_XGMII       => RESET_XGMII,
      XGMII_SDR_TXD     => XGMII_SDR_TXD,
      XGMII_SDR_TXC     => XGMII_SDR_TXC,

      RX_SOF_N          => RX_SOF_N,
      RX_SOP_N          => RX_SOP_N,
      RX_EOP_N          => RX_EOP_N,
      RX_EOF_N          => RX_EOF_N,
      RX_SRC_RDY_N      => RX_SRC_RDY_N,
      RX_DST_RDY_N      => RX_DST_RDY_N,
      RX_DATA           => RX_DATA,
      RX_REM            => RX_REM,
      FL_CLK            => FL_CLK,
      RESET_FL          => RESET_FL,

      OUTGOING_PCKT     => OUTGOING_PCKT,

      MI_DWR      	   => MI.DWR,
      MI_ADDR     	   => MI.ADDR,
      MI_RD       	   => MI.RD,
      MI_WR       	   => MI.WR,
      MI_BE       	   => MI.BE,
      MI_DRD      	   => MI.DRD,
      MI_ARDY     	   => MI.ARDY,
      MI_DRDY     	   => MI.DRDY,
      MI_CLK            => MI_CLK,
      RESET_MI          => RESET_MI
   );

end architecture obuf_xgmii_sdr_arch;
-- ----------------------------------------------------------------------------
