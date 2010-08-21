-- obuf_top4_fl64.vhd: 4 OBUFs, top level with records
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jiri Tobola <tobola@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity obuf_top4_fl64 is
   generic(
      DFIFO_SIZE  : integer := 511;
      SFIFO_SIZE  : integer := 32;
      CTRL_CMD    : boolean := false;
      INBANDFCS   : boolean := false;
      SKIP_FCS    : boolean := false
   );
   port(

      -- ---------------- Control signal -----------------
      RESET         : in  std_logic;
      WRCLK         : in  std_logic;
      REFCLK        : in  std_logic;

      -- ------------- FrameLink interface ---------------
      OBUF0_TX         : inout t_fl64;
      OBUF1_TX         : inout t_fl64;
      OBUF2_TX         : inout t_fl64;
      OBUF3_TX         : inout t_fl64;

      -- -------------- GMII/MII interface ---------------
      -- Interface 0
      OBUF0_TXCLK       : out  std_logic;
      OBUF0_TXD         : out  std_logic_vector(7 downto 0);
      OBUF0_TXEN        : out  std_logic;
      OBUF0_TXER        : out  std_logic;
      -- Interface 1
      OBUF1_TXCLK      : out  std_logic;
      OBUF1_TXD        : out  std_logic_vector(7 downto 0);
      OBUF1_TXEN       : out  std_logic;
      OBUF1_TXER       : out  std_logic;
      -- Interface 2
      OBUF2_TXCLK      : out  std_logic;
      OBUF2_TXD        : out  std_logic_vector(7 downto 0);
      OBUF2_TXEN       : out  std_logic;
      OBUF2_TXER       : out  std_logic;
      -- Interface 3
      OBUF3_TXCLK      : out  std_logic;
      OBUF3_TXD        : out  std_logic_vector(7 downto 0);
      OBUF3_TXEN       : out  std_logic;
      OBUF3_TXER       : out  std_logic;

      -- ---------- Internal bus signals ----------------
      MI               : inout t_mi32
   ); 
end obuf_top4_fl64;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of obuf_top4_fl64 is
begin

   OBUF_GMII_TOP4_MI32_I: entity work.obuf_gmii_top4_mi32
   generic map(
      DATA_PATHS  => 8,
      DFIFO_SIZE  => DFIFO_SIZE,
      SFIFO_SIZE  => SFIFO_SIZE,
      CTRL_CMD    => CTRL_CMD,
      INBANDFCS   => INBANDFCS,
      SKIP_FCS    => SKIP_FCS
   )
   port map(
      -- ---------------- Control signal -----------------
      RESET         => RESET,
      WRCLK         => WRCLK,
      REFCLK        => REFCLK,

      -- FrameLink interface
      OBUF0_DATA       => OBUF0_TX.DATA,
      OBUF0_DREM       => OBUF0_TX.DREM,
      OBUF0_SRC_RDY_N  => OBUF0_TX.SRC_RDY_N,
      OBUF0_SOF_N      => OBUF0_TX.SOF_N,
      OBUF0_SOP_N      => OBUF0_TX.SOP_N,
      OBUF0_EOF_N      => OBUF0_TX.EOF_N,
      OBUF0_EOP_N      => OBUF0_TX.EOP_N,
      OBUF0_DST_RDY_N  => OBUF0_TX.DST_RDY_N,

      OBUF1_DATA       => OBUF1_TX.DATA,
      OBUF1_DREM       => OBUF1_TX.DREM,
      OBUF1_SRC_RDY_N  => OBUF1_TX.SRC_RDY_N,
      OBUF1_SOF_N      => OBUF1_TX.SOF_N,
      OBUF1_SOP_N      => OBUF1_TX.SOP_N,
      OBUF1_EOF_N      => OBUF1_TX.EOF_N,
      OBUF1_EOP_N      => OBUF1_TX.EOP_N,
      OBUF1_DST_RDY_N  => OBUF1_TX.DST_RDY_N,

      OBUF2_DATA       => OBUF2_TX.DATA,
      OBUF2_DREM       => OBUF2_TX.DREM,
      OBUF2_SRC_RDY_N  => OBUF2_TX.SRC_RDY_N,
      OBUF2_SOF_N      => OBUF2_TX.SOF_N,
      OBUF2_SOP_N      => OBUF2_TX.SOP_N,
      OBUF2_EOF_N      => OBUF2_TX.EOF_N,
      OBUF2_EOP_N      => OBUF2_TX.EOP_N,
      OBUF2_DST_RDY_N  => OBUF2_TX.DST_RDY_N,

      OBUF3_DATA       => OBUF3_TX.DATA,
      OBUF3_DREM       => OBUF3_TX.DREM,
      OBUF3_SRC_RDY_N  => OBUF3_TX.SRC_RDY_N,
      OBUF3_SOF_N      => OBUF3_TX.SOF_N,
      OBUF3_SOP_N      => OBUF3_TX.SOP_N,
      OBUF3_EOF_N      => OBUF3_TX.EOF_N,
      OBUF3_EOP_N      => OBUF3_TX.EOP_N,
      OBUF3_DST_RDY_N  => OBUF3_TX.DST_RDY_N,

      -- -------------- GMII/MII interface ---------------
      -- Interface 0
      OBUF0_TXCLK      => OBUF0_TXCLK,
      OBUF0_TXD        => OBUF0_TXD,
      OBUF0_TXEN       => OBUF0_TXEN,
      OBUF0_TXER       => OBUF0_TXER,
      -- Interface 1
      OBUF1_TXCLK      => OBUF1_TXCLK,
      OBUF1_TXD        => OBUF1_TXD,
      OBUF1_TXEN       => OBUF1_TXEN,
      OBUF1_TXER       => OBUF1_TXER,
      -- Interface 2
      OBUF2_TXCLK      => OBUF2_TXCLK,
      OBUF2_TXD        => OBUF2_TXD,
      OBUF2_TXEN       => OBUF2_TXEN,
      OBUF2_TXER       => OBUF2_TXER,
      -- Interface 3
      OBUF3_TXCLK      => OBUF3_TXCLK,
      OBUF3_TXD        => OBUF3_TXD,
      OBUF3_TXEN       => OBUF3_TXEN,
      OBUF3_TXER       => OBUF3_TXER,

      -- ---------- Internal bus signals ----------------
      MI	              => MI
   ); 

end behavioral;

