--
-- phy_sim_sfp.vhd: PHY - simulation component for SFP
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
--    - INTERFRAME waiting is blocking (during it there cannot be started
--      another operation of both types (RX, TX))
--    - INTERFRAME between packets sended in one operation is ok, but between
--      two operation there is an extra clkper/2 of idle commands (4 octets)
--    - when receiving packet, it checks only bad pramble (TODO check all errors)
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.phy_oper.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity phy_sim_sfp is
   generic(
      INTER_FRAME   : integer := 12; -- 96 bit times, see IEEE 802.3
      FILE_NAME_RCV : string  := "";
      -- default value from standard, but for testing frame_toolong check use larger value
      MAX_UNTAGGED_FRAME_SIZE : integer := 1518;
      DEBUG_REPORT  : boolean := false
   );
   port(
      -- Global signals
      RESET    : in  std_logic;

      -- 8/10 interface
      --RX_LOST  : in  std_logic;
      RX_CLK   : in  std_logic;
      RX_D10   : in  std_logic_vector(9 downto 0);
      TX_CLK   : out std_logic;
      TX_D10   : out std_logic_vector(9 downto 0);

      -- Simulation interface ----------------------------------------------
      OPER         : in  t_phy_oper;
      PARAMS       : in  t_phy_params;
      STROBE       : in  std_logic;
      BUSY         : out std_logic := '0'

   );
end entity phy_sim_sfp;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of phy_sim_sfp is
   signal tx_clk_i : std_logic;
   signal txd      : std_logic_vector(7 downto 0);
   signal tx_dv    : std_logic;
   signal tx_er    : std_logic;

   signal rxd      : std_logic_vector(7 downto 0);
   signal rx_dv    : std_logic;
   signal rx_er    : std_logic;
begin

-- pcs component instantion
PCSMX_U : entity work.pcs_mx
port map(
   -- Global signals
   RESET    => RESET,

   -- 8/10 interface
   RX_LOST  => '0',
   RX_D10   => RX_D10,
   RX_LSTAT => open,
   TX_D10   => TX_D10,

   -- GMII interface
   RX_CLK   => RX_CLK,
   RX_D     => rxd,
   RX_DV    => rx_dv,
   RX_ER    => rx_er,

   TX_CLK   => tx_clk_i,
   TX_D     => txd,
   TX_EN    => tx_dv,
   TX_ER    => tx_er
);

-- phy sim gmii component instantion
PHY_SIM_GMII : entity work.phy_sim_gmii
generic map(
   INTER_FRAME    => INTER_FRAME,
   FILE_NAME_RCV  => FILE_NAME_RCV,
   DEBUG_REPORT   => DEBUG_REPORT
)
port map(
  -- TX interface -------------------------------------------------------
  TX_CLK => tx_clk_i,
  TXD    => txd,
  TX_DV  => tx_dv,
  TX_ER  => tx_er,
  -- RX interface -------------------------------------------------------
  RX_CLK => RX_CLK,
  RXD    => rxd,
  RX_EN  => rx_dv,
  RX_ER  => rx_er,

   -- Simulation interface
   OPER        => OPER,
   PARAMS      => PARAMS,
   STROBE      => STROBE,
   BUSY        => BUSY
);

TX_CLK <= tx_clk_i;

end architecture behavioral;

