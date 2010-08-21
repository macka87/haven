
-- aurvc_core_ent.vhd: aurvc_core component entity. 
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

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity aurvc_core is
   generic (
      LANES                : integer;     -- Number of lanes 
      DATA_PATHS           : integer;     -- Number of data paths
      TX_CHANNELS          : integer;     -- Number of TX channels
      RX_CHANNELS          : integer;     -- Number of RX channels
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   );
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      BUFFER_CLK     : out std_logic;     -- Clock to clock TX and RX buffers
      
      -- TX Buffers Interface
      TX_BUFFER_DATA       : in std_logic_vector((TX_CHANNELS*DATA_PATHS*8)-1 downto 0);
      TX_BUFFER_REM        : in std_logic_vector((TX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
      TX_BUFFER_EOP        : in std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_BUFFER_DV         : in std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_BUFFER_READ       : out std_logic_vector(TX_CHANNELS-1 downto 0);
      TX_BUFFER_EMPTY      : in std_logic_vector(TX_CHANNELS-1 downto 0);
      BYTE_QUOTA_MET       : in std_logic_vector(TX_CHANNELS-1 downto 0);
      BYTE_QUOTA_RST       : out std_logic_vector(TX_CHANNELS-1 downto 0);

      -- RX Buffers Interface
      RX_BUFFER_DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      RX_BUFFER_REM        : out std_logic_vector((log2(DATA_PATHS))-1 downto 0);
      RX_BUFFER_EOP        : out std_logic;
      RX_BUFFER_WRITE      : out std_logic_vector(RX_CHANNELS-1 downto 0);
      RX_BUFFER_ALMOST_FULL: in  std_logic_vector(RX_CHANNELS-1 downto 0);

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : out std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : out std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                          -- asserted for a single clock).
      FRAME_ERROR    : out std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                          -- and is asserted for a single clock.
      -- Status Interface
      CHANNEL_UP     : out std_logic;

      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0)
   );
end aurvc_core;

