
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
      DFIFO_SIZE  : integer := 8191;     -- Packet data fifo size
      HFIFO_SIZE  : integer := 1023;     -- Control fifo size
      MACS        : integer := 16-- Number of MAC addresses (up to 16)
   );
   port(

      -- Common signal
      RESET           : in  std_logic;
      IBUF_CLK        : in std_logic;

      -- GMII RX interfaces
      IBUF0_RXCLK     : in  std_logic;
      IBUF0_RXD       : in  std_logic_vector(7 downto 0);
      IBUF0_RXDV      : in  std_logic;
      IBUF0_RXER      : in  std_logic;

      IBUF1_RXCLK     : in  std_logic;
      IBUF1_RXD       : in  std_logic_vector(7 downto 0);
      IBUF1_RXDV      : in  std_logic;
      IBUF1_RXER      : in  std_logic;

      IBUF2_RXCLK     : in  std_logic;
      IBUF2_RXD       : in  std_logic_vector(7 downto 0);
      IBUF2_RXDV      : in  std_logic;
      IBUF2_RXER      : in  std_logic;

      IBUF3_RXCLK     : in  std_logic;
      IBUF3_RXD       : in  std_logic_vector(7 downto 0);
      IBUF3_RXDV      : in  std_logic;
      IBUF3_RXER      : in  std_logic;

      -- PACODAG
      IBUF0_PCD       : inout t_pacodag16;
      IBUF1_PCD       : inout t_pacodag16;
      IBUF2_PCD       : inout t_pacodag16;
      IBUF3_PCD       : inout t_pacodag16;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT : in std_logic;
      IBUF0_SAU_DV     : in std_logic;
      IBUF1_SAU_ACCEPT : in std_logic;
      IBUF1_SAU_DV     : in std_logic;
      IBUF2_SAU_ACCEPT : in std_logic;
      IBUF2_SAU_DV     : in std_logic;
      IBUF3_SAU_ACCEPT : in std_logic;
      IBUF3_SAU_DV     : in std_logic;

      -- FrameLink interface
      IBUF0_TX         : inout t_fl16;
      IBUF1_TX         : inout t_fl16;
      IBUF2_TX         : inout t_fl16;
      IBUF3_TX         : inout t_fl16;

      -- Internal bus signals ----------------
      MI               : inout t_mi32
   );
end top_level;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of top_level is

component ibuf_top4_fl16 is
   generic(
      DFIFO_SIZE  : integer;     -- Packet data fifo size
      HFIFO_SIZE  : integer;     -- Control fifo size
      MACS        : integer := 16-- Number of MAC addresses (up to 16)
   );
   port(

      -- Common signal
      RESET           : in  std_logic;
      IBUF_CLK        : in std_logic;

      -- GMII RX interfaces
      IBUF0_RXCLK     : in  std_logic;
      IBUF0_RXD       : in  std_logic_vector(7 downto 0);
      IBUF0_RXDV      : in  std_logic;
      IBUF0_RXER      : in  std_logic;

      IBUF1_RXCLK     : in  std_logic;
      IBUF1_RXD       : in  std_logic_vector(7 downto 0);
      IBUF1_RXDV      : in  std_logic;
      IBUF1_RXER      : in  std_logic;

      IBUF2_RXCLK     : in  std_logic;
      IBUF2_RXD       : in  std_logic_vector(7 downto 0);
      IBUF2_RXDV      : in  std_logic;
      IBUF2_RXER      : in  std_logic;

      IBUF3_RXCLK     : in  std_logic;
      IBUF3_RXD       : in  std_logic_vector(7 downto 0);
      IBUF3_RXDV      : in  std_logic;
      IBUF3_RXER      : in  std_logic;

      -- PACODAG
      IBUF0_PCD       : inout t_pacodag16;
      IBUF1_PCD       : inout t_pacodag16;
      IBUF2_PCD       : inout t_pacodag16;
      IBUF3_PCD       : inout t_pacodag16;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT : in std_logic;
      IBUF0_SAU_DV     : in std_logic;
      IBUF1_SAU_ACCEPT : in std_logic;
      IBUF1_SAU_DV     : in std_logic;
      IBUF2_SAU_ACCEPT : in std_logic;
      IBUF2_SAU_DV     : in std_logic;
      IBUF3_SAU_ACCEPT : in std_logic;
      IBUF3_SAU_DV     : in std_logic;

      -- FrameLink interface
      IBUF0_TX         : inout t_fl16;
      IBUF1_TX         : inout t_fl16;
      IBUF2_TX         : inout t_fl16;
      IBUF3_TX         : inout t_fl16;

      -- Internal bus signals ----------------
      MI               : inout t_mi32
   );
end component;

begin

ibuf_u: ibuf_top4_fl16
   generic map(
      DFIFO_SIZE  => dfifo_size,
      HFIFO_SIZE  => hfifo_size,
      MACS        => macs
   )
   port map(

      -- Common signal
      RESET           => reset,
      IBUF_CLK        => ibuf_clk,

      -- GMII RX interfaces
      IBUF0_RXCLK     => ibuf0_rxclk,
      IBUF0_RXD       => ibuf0_rxd,
      IBUF0_RXDV      => ibuf0_rxdv,
      IBUF0_RXER      => ibuf0_rxer,

      IBUF1_RXCLK     => ibuf1_rxclk,
      IBUF1_RXD       => ibuf1_rxd,
      IBUF1_RXDV      => ibuf1_rxdv,
      IBUF1_RXER      => ibuf1_rxer,

      IBUF2_RXCLK     => ibuf2_rxclk,
      IBUF2_RXD       => ibuf2_rxd,
      IBUF2_RXDV      => ibuf2_rxdv,
      IBUF2_RXER      => ibuf2_rxer,

      IBUF3_RXCLK     => ibuf3_rxclk,
      IBUF3_RXD       => ibuf3_rxd,
      IBUF3_RXDV      => ibuf3_rxdv,
      IBUF3_RXER      => ibuf3_rxer,

      -- PACODAG
      IBUF0_PCD       => ibuf0_pcd,
      IBUF1_PCD       => ibuf1_pcd,
      IBUF2_PCD       => ibuf2_pcd,
      IBUF3_PCD       => ibuf3_pcd,

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT => ibuf0_sau_accept,
      IBUF0_SAU_DV     => ibuf0_sau_dv,
      IBUF1_SAU_ACCEPT => ibuf1_sau_accept,
      IBUF1_SAU_DV     => ibuf1_sau_dv,
      IBUF2_SAU_ACCEPT => ibuf2_sau_accept,
      IBUF2_SAU_DV     => ibuf2_sau_dv,
      IBUF3_SAU_ACCEPT => ibuf3_sau_accept,
      IBUF3_SAU_DV     => ibuf3_sau_dv,

      -- FrameLink interface
      IBUF0_TX         => ibuf0_tx,
      IBUF1_TX         => ibuf1_tx,
      IBUF2_TX         => ibuf2_tx,
      IBUF3_TX         => ibuf3_tx,

      -- Internal bus signals ----------------
      MI               => mi
   );

end behavioral;

