-- phy_sim_xgmii_sdr.vhd: PHY - simulation component for XGMII SDR
--                        Generates XGMII traffic. (wrapper for phy_sim_xgmii)
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use ieee.std_logic_textio.all;
use std.textio.all;

use work.phy_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity phy_sim_xgmii_sdr is
   generic(
      INTER_FRAME   : integer := 12; -- 96 bit times, see IEEE 802.3
      FILE_NAME_RCV : string  := "";
      -- default value from standard, but for testing frame_toolong check use larger value
      MAX_UNTAGGED_FRAME_SIZE : integer := 1518;
      DEBUG_REPORT  : boolean := false
   );
   port(
      CLK          : in std_logic;
      RESET        : in std_logic;

      -- TX interface 
      TXD          : out std_logic_vector(63 downto 0) := X"0707070707070707";
      TXC          : out std_logic_vector(7 downto 0)  := "11111111";

      -- Simulation interface -
      OPER         : in    t_phy_oper;
      PARAMS       : in    t_phy_params;
      STROBE       : in    std_logic;
      BUSY         : out   std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture wrapper of phy_sim_xgmii_sdr is
   
   signal ddr_txclk : std_logic;  
   signal ddr_txd  : std_logic_vector(31 downto 0);
   signal ddr_txc  : std_logic_vector( 3 downto 0);

   signal rep_rxclk : std_logic;  
   signal rep_rxd  : std_logic_vector(63 downto 0);
   signal rep_rxc  : std_logic_vector( 7 downto 0);

begin

solve_clk_domain: entity work.xgmii_rep_2port
port map (
   RESET      => RESET,
   -- Port 0 ---------------------------------------------------------------
   EN0        => '1',
   OVERFLOW0  => open,
   UNDERFLOW0 => open,
    -- XGMII interface 0
   RX_CLK0    => CLK,
   RX_D0      => X"0707070707070707",
   RX_C0      => "11111111",
   TX_CLK0    => CLK,
   TX_D0      => TXD, 
   TX_C0      => TXC,
   ---
   -- Port 1 ---------------------------------------------------------------
   EN1        => '1',
   OVERFLOW1  => open,
   UNDERFLOW1 => open,
    -- XGMII interface 1
   RX_CLK1    => rep_rxclk,
   RX_D1      => rep_rxd,
   RX_C1      => rep_rxc,
   TX_CLK1    => rep_rxclk,
   TX_D1      => open,
   TX_C1      => open
);



---
-- Double data rate to single data rate
---
ddr2sdr : entity work.xgmii_rx
port map (
   XGMII_RX_CLK   => ddr_txclk,
   XGMII_RXD      => ddr_txd,
   XGMII_RXC      => ddr_txc,
   RESET          => reset,

   RX_CLK_INT     => rep_rxclk,
   RXD_INT        => rep_rxd,
   RXC_INT        => rep_rxc,

   RX_DCM_LOCK    => open,
   RX_DCM_RESET   => RESET
);


---
-- Original unit that work with DDR
---
orig_sim_unit : entity work.phy_sim_xgmii
generic map (
      INTER_FRAME    => INTER_FRAME,
      FILE_NAME_RCV  => FILE_NAME_RCV,
      MAX_UNTAGGED_FRAME_SIZE => MAX_UNTAGGED_FRAME_SIZE,
      DEBUG_REPORT   => DEBUG_REPORT
)
port map (
      -- TX interface 
      TX_CLK   => ddr_txclk,    
      TXD      => ddr_txd,
      TXC      => ddr_txc,
      -- RX interface 
      RX_CLK   => '0',
      RXD      => X"07070707",
      RXC      => "1111",
      -- Simulation interface 
      OPER     => OPER,
      PARAMS   => PARAMS,
      STROBE   => STROBE,
      BUSY     => BUSY
);

end architecture;
