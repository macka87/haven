-- obuf_top2_fl16.vhd: 2 OBUFs, top level with records
-- Copyright (C) 2007 CESNET
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

use work.math_pack.ALL;
use work.fl_pkg.ALL;
use work.lb_pkg.ALL;
use work.emac_pkg.ALL;


-- -------------------------------------------------------------
--       Entity
-- -------------------------------------------------------------

entity obuf_emac_top2_fl16 is
   generic(
      DFIFO_SIZE     : integer;
      SFIFO_SIZE     : integer;
      CTRL_CMD       : boolean;
      EMAC0_USECLKEN : boolean;
      EMAC1_USECLKEN : boolean
   );
   port(

      -- ---------------- Control signal -----------------
      RESET         : in  std_logic;
      WRCLK         : in  std_logic;

      -- ------------- FrameLink interface ---------------
      OBUF0_RX         : inout t_fl16;
      OBUF1_RX         : inout t_fl16;

      -- -------------- TX interface -----------------
      -- Interface 0
      OBUF0_EMAC_CLK   : in std_logic;
      OBUF0_EMAC_CE    : in std_logic;
      OBUF0_TX_EMAC    : inout t_emac_tx;
      -- Interface 1
      OBUF1_EMAC_CLK   : in std_logic;
      OBUF1_EMAC_CE    : in std_logic;
      OBUF1_TX_EMAC    : inout t_emac_tx;

      -- ---------- Internal bus signals ----------------
      MI               : inout t_mi32
   );
end entity obuf_emac_top2_fl16;


-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of obuf_emac_top2_fl16 is
begin

   OBUF_EMAC_TOP2_MI32_I: entity work.obuf_emac_top2_mi32
      generic map(
         DATA_PATHS     => 2,
         DFIFO_SIZE     => DFIFO_SIZE,
         SFIFO_SIZE     => SFIFO_SIZE,
         CTRL_CMD       => CTRL_CMD,
         EMAC0_USECLKEN => EMAC0_USECLKEN,
         EMAC1_USECLKEN => EMAC1_USECLKEN
      )
      port map(
   
         -- ---------------- Control signal -----------------
         RESET         => RESET,
         WRCLK         => WRCLK,
   
         -- -------------- Buffer interface -----------------
         -- Interface 0
         OBUF0_DATA       => OBUF0_RX.DATA,
         OBUF0_DREM       => OBUF0_RX.DREM,
         OBUF0_SRC_RDY_N  => OBUF0_RX.SRC_RDY_N,
         OBUF0_SOF_N      => OBUF0_RX.SOF_N,
         OBUF0_SOP_N      => OBUF0_RX.SOP_N,
         OBUF0_EOF_N      => OBUF0_RX.EOF_N,
         OBUF0_EOP_N      => OBUF0_RX.EOP_N,
         OBUF0_DST_RDY_N  => OBUF0_RX.DST_RDY_N,
         -- Interface 1 
         OBUF1_DATA       => OBUF1_RX.DATA,
         OBUF1_DREM       => OBUF1_RX.DREM,
         OBUF1_SRC_RDY_N  => OBUF1_RX.SRC_RDY_N,
         OBUF1_SOF_N      => OBUF1_RX.SOF_N,
         OBUF1_SOP_N      => OBUF1_RX.SOP_N,
         OBUF1_EOF_N      => OBUF1_RX.EOF_N,
         OBUF1_EOP_N      => OBUF1_RX.EOP_N,
         OBUF1_DST_RDY_N  => OBUF1_RX.DST_RDY_N,
   
         -- -------------- TX interface -----------------
         -- Interface 0
         OBUF0_EMAC_CLK   => OBUF0_EMAC_CLK,
         OBUF0_EMAC_CE    => OBUF0_EMAC_CE,
         OBUF0_TX_EMAC    => OBUF0_TX_EMAC,
         -- Interface 1
         OBUF1_EMAC_CLK   => OBUF1_EMAC_CLK,
         OBUF1_EMAC_CE    => OBUF1_EMAC_CE,
         OBUF1_TX_EMAC    => OBUF1_TX_EMAC,
   
         -- ---------- MI_32 bus signals ----------------
         MI               => MI
      );

end architecture behavioral;
