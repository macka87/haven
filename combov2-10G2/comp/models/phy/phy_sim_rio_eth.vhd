--
-- phy_sim_rop_eth.vhd: PHY - simulation component for RocketIO - Ethernet
-- Copyright (C) 2005 CESNET
-- Author(s): Stepan Friedl <friedl@liberouter.org>
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
-- NOTE:

library IEEE;
use IEEE.std_logic_1164.all;

use work.phy_oper.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity phy_sim_rio_eth is
   generic(
      INTER_FRAME   : integer := 12; -- 96 bit times, see IEEE 802.3
      FILE_NAME_RCV : string  := "";
      MAX_UNTAGGED_FRAME_SIZE : integer := 1518;
      DEBUG_REPORT  : boolean := false
   );
   port(
      -- Global signals
      RESET : in  std_logic;
      -- RocketIO interface
      RXP   :  in std_logic;
      RXN   :  in std_logic;
      TXP   : out std_logic;
      TXN   : out std_logic;
      -- Simulation interface ----------------------------------------------
      OPER   : in  t_phy_oper;
      PARAMS : in  t_phy_params;
      STROBE : in  std_logic;
      BUSY   : out std_logic := '0'
   );
end entity phy_sim_rio_eth;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of phy_sim_rio_eth is

signal rio_dclk  : std_logic := '0';  
signal gmii_clk  : std_logic;
signal gmii_rxd  : std_logic_vector(7 downto 0);
signal gmii_rxdv : std_logic;
signal gmii_rxer : std_logic;
signal gmii_txd  : std_logic_vector(7 downto 0);
signal gmii_txen : std_logic;
signal gmii_txer : std_logic;

begin

RIO_DCLK_DIV: process(gmii_clk)
begin
   if gmii_clk'event and gmii_clk = '1' then
      rio_dclk <= not rio_dclk;
   end if;
end process;

RIO_GMII_U: entity work.rio_gmii
port map (
   RIO_RCLK   => gmii_clk,
   RIO_DCLK   => rio_dclk,
   RESET      => RESET,
   -- GMII interface
   GMII_CLK   => gmii_clk,
   GMII_RXD   => gmii_rxd,
   GMII_RXDV  => gmii_rxdv,
   GMII_RXER  => gmii_rxer,
   GMII_TXD   => gmii_txd,
   GMII_TXEN  => gmii_txen,
   GMII_TXER  => gmii_txer,
   -- MGT (RocketIO) interface
   RXN        => RXN,
   RXP        => RXP,
   TXN        => TXN,
   TXP        => TXP,
   -- Status and service interface
   RXPOLARITY => '1',
   TXPOLARITY => '1',
   LOOPBACK   => "00",
   RXSYNCLOSS => open
);

-- phy sim gmii component instantion
PHY_SIM_GMII : entity work.phy_sim_gmii
generic map(
   INTER_FRAME             => INTER_FRAME,
   FILE_NAME_RCV           => FILE_NAME_RCV,
   MAX_UNTAGGED_FRAME_SIZE => MAX_UNTAGGED_FRAME_SIZE,
   DEBUG_REPORT            => DEBUG_REPORT
)
port map(
  -- TX interface -------------------------------------------------------
   TX_CLK => gmii_clk,
   TXD    => gmii_txd,
   TX_DV  => gmii_txen,
   TX_ER  => gmii_txer,
   -- RX interface ------------------------------------------------------
   RX_CLK => gmii_clk,
   RXD    => gmii_rxd,
   RX_EN  => gmii_rxdv,
   RX_ER  => gmii_rxer,
   -- Simulation interface
   OPER   => OPER,
   PARAMS => PARAMS,
   STROBE => STROBE,
   BUSY   => BUSY
);

end architecture behavioral;

