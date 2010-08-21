--
-- rep_2port.vhd: Two port asynchronous XGMII repeater (packet forwarder)
--                Packets incoming to RX port 0 are forwarded to TX port 1,
--                packets incoming to RX port 1 are forwarded to TX port 0
--                RX and TX clocks can be independend, but their frequency
--                must be close
--
-- Copyright (C) 2008 CESNET
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
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

entity xgmii_rep_2port is
   generic (
      FIFO_SIZE  : integer := 512 -- FIFO size 
   );
   port (
      RESET      : in  std_logic;   -- Asynchronous Reset
      -- Port 0 ---------------------------------------------------------------
      EN0        : in  std_logic;   -- Port0 packet forwarding enable
      OVERFLOW0  : out std_logic;   -- FIFO overflow indicator (RX packet lost)
      UNDERFLOW0 : out std_logic;   -- FIFO underflow indicator (TX packet lost)
       -- XGMII interface 0
      RX_CLK0    : in  std_logic;   -- XGMII RX clock (from DCM)
      RX_D0      : in  std_logic_vector(63 downto 0); -- XGMII RX data
      RX_C0      : in  std_logic_vector( 7 downto 0); -- XGMII RX command
      TX_CLK0    : in  std_logic;   -- XGMII TX clock input
      TX_D0      : out std_logic_vector(63 downto 0); -- XGMII TX data forwarded from port 1
      TX_C0      : out std_logic_vector( 7 downto 0); -- XGMII TX command forwarded from port 1
      -- Port 1 ---------------------------------------------------------------
      EN1        : in  std_logic;   -- Port1 packet forwarding enable
      OVERFLOW1  : out std_logic;   -- FIFO overflow indicator (RX packet lost)
      UNDERFLOW1 : out std_logic;   -- FIFO underflow indicator (TX packet lost)
       -- XGMII interface 1
      RX_CLK1    : in  std_logic;   -- XGMII RX clock (from DCM)
      RX_D1      : in  std_logic_vector(63 downto 0); -- XGMII RX data
      RX_C1      : in  std_logic_vector( 7 downto 0); -- XGMII RX command
      TX_CLK1    : in  std_logic;   -- XGMII TX clock input
      TX_D1      : out std_logic_vector(63 downto 0); -- XGMII TX data forwarded from port 0
      TX_C1      : out std_logic_vector( 7 downto 0)  -- XGMII TX command forwarded from port 0
   );
end xgmii_rep_2port;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture structural of xgmii_rep_2port is

begin

FWD_RX0_TX1 : entity work.xgmii_pckt_fwd
generic map (
   FIFO_SIZE     => FIFO_SIZE
)
port map (
   RESET     => RESET,
   EN        => EN0,
   -- GMII RX interface
   RX_CLK    => RX_CLK0,
   RX_D      => RX_D0,
   RX_C      => RX_C0,
   OVERFLOW  => OVERFLOW0,
   -- GMII TX interface
   TX_CLK    => TX_CLK1,
   TX_D      => TX_D1,
   TX_C      => TX_C1,
   UNDERFLOW => UNDERFLOW1
);

FWD_RX1_TX0 : entity work.xgmii_pckt_fwd
generic map (
   FIFO_SIZE     => FIFO_SIZE
)
port map (
   RESET     => RESET,
   EN        => EN1,
   -- GMII RX interface
   RX_CLK    => RX_CLK1,
   RX_D      => RX_D1,
   RX_C      => RX_C1,
   OVERFLOW  => OVERFLOW1,
   -- GMII TX interface
   TX_CLK    => TX_CLK0,
   TX_D      => TX_D0,
   TX_C      => TX_C0,
   UNDERFLOW => UNDERFLOW0
);

end architecture structural;
-- -----------------------------------------------------------------------------
