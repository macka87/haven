-- fl.vhd: Architecture of FL part of XGMII OBUF
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.xgmii_obuf_pkg.all;
use work.math_pack.all;

architecture obuf_xgmii_fl_arch of obuf_xgmii_fl is

begin

   -- Output signals
   TX_DATA     <= RX_DATA;
   TX_SOP_N    <= RX_SOP_N;
   TX_EOP_N    <= RX_EOP_N;
   TX_EOP_POS  <= RX_REM;

   fsmi: entity work.obuf_xgmii_fl_fsm
   generic map(
      CTRL_CMD    => CTRL_CMD
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      SOP_N       => RX_SOP_N,
      EOP_N       => RX_EOP_N,
      DFIFO_OVF   => TX_DFIFO_OVF,
      DFIFO_FULL  => TX_DFIFO_FULL,
      HFIFO_FULL  => TX_HFIFO_FULL,
      SRC_RDY_N   => RX_SRC_RDY_N,
      DST_RDY_N   => RX_DST_RDY_N,
      DFIFO_MARK  => TX_MARK,
      DFIFO_WR    => TX_WR,
      HFIFO_WR    => TX_HFIFO_WR
   );

   -- HDATA connection
   hdata_ctrl_cmd_true_gen: if CTRL_CMD = true generate
      TX_HDATA <= RX_DATA(C_FTR_MAX_BIT downto 0);
   end generate hdata_ctrl_cmd_true_gen;
   hdata_ctrl_cmd_false_gen: if CTRL_CMD = false generate
      TX_HDATA(C_FRAME_VLD_POS) <= '1';
      TX_HDATA(C_RPLC_SRC_MAC_POS) <= '0';
   end generate hdata_ctrl_cmd_false_gen;

end architecture;
