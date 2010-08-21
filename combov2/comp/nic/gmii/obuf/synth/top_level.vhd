
-- top_level.vhd: blah blah 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
use work.math_pack.all;
use work.fl_pkg.ALL;
use work.ibuf_pkg.ALL;
use work.lb_pkg.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity top_level is
   generic(
      DFIFO_SIZE  : integer := 4095;
      SFIFO_SIZE  : integer := 10;
      CTRL_CMD    : boolean := true
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
end top_level;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of top_level is

component obuf_top4_fl64 is
   generic(
      DFIFO_SIZE  : integer;
      SFIFO_SIZE  : integer;
      CTRL_CMD    : boolean
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
end component obuf_top4_fl64;


begin

obuf_u: obuf_top4_fl64
   generic map(
      DFIFO_SIZE  => dfifo_size,
      SFIFO_SIZE  => sfifo_size,
      CTRL_CMD    => ctrl_cmd
   )
   port map(

      -- ---------------- Control signal -----------------
      RESET         => reset,
      WRCLK         => wrclk,
      REFCLK        => refclk,

      -- ------------- FrameLink interface ---------------
      OBUF0_TX         => obuf0_tx,
      OBUF1_TX         => obuf1_tx,
      OBUF2_TX         => obuf2_tx,
      OBUF3_TX         => obuf3_tx,

      -- -------------- GMII/MII interface ---------------
      -- Interface 0
      OBUF0_TXCLK       => obuf0_txclk,
      OBUF0_TXD         => obuf0_txd,
      OBUF0_TXEN        => obuf0_txen,
      OBUF0_TXER        => obuf0_txer,
      -- Interface 1
      OBUF1_TXCLK      => obuf1_txclk,
      OBUF1_TXD        => obuf1_txd,
      OBUF1_TXEN       => obuf1_txen,
      OBUF1_TXER       => obuf1_txer,
      -- Interface 2
      OBUF2_TXCLK      => obuf2_txclk,
      OBUF2_TXD        => obuf2_txd,
      OBUF2_TXEN       => obuf2_txen,
      OBUF2_TXER       => obuf2_txer,
      -- Interface 3
      OBUF3_TXCLK      => obuf3_txclk,
      OBUF3_TXD        => obuf3_txd,
      OBUF3_TXEN       => obuf3_txen,
      OBUF3_TXER       => obuf3_txer,

      -- ---------- Internal bus signals ----------------
      MI               => mi
   ); 

end behavioral;

