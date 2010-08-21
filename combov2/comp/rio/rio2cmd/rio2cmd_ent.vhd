
-- rio2cmd_ent.vhd: Command Protocol Transceiver via RocketIO (entity)
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

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity rio2cmd is
   generic (
      LOOPBACK   : std_logic_vector := "00"; -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      TX_LOGIC   : boolean := true;    -- Enables TX logic instantion (in simplex mode for receivers set 'false')
      RX_LOGIC   : boolean := true    -- Enables RX logic instantion (in simplex mode for transmitters set 'false')
      );
   port (
      -- Common Interface
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock command protocol interface

      -- Command Protocol TX Interface
      DI             : in std_logic_vector(31 downto 0);    -- Data
      DI_CMD         : in std_logic_vector(3 downto 0);     -- Byte-mapped command flag
      DI_DV          : in std_logic;                        -- DI valid flag
      DI_FULL        : out std_logic;                       -- Transmit buffer full flag

      -- Command Protocol RX Interface
      DO             : out std_logic_vector(31 downto 0);   -- Data
      DO_CMD         : out std_logic_vector(3 downto 0);    -- Byte-mapped command flag
      DO_DV          : out std_logic;                       -- DO valid flag
      DO_FULL        : in std_logic;                        -- Stop Receiving

      -- Status inteface
      STATUS   : out std_logic_vector(7 downto 0);          -- 0: signals crc error, 1: signals recv buffer overflow
      STATUS_DV: out std_logic;                             -- STATUS is valid

      -- MGT Interface
      RXN            : in  std_logic;
      RXP            : in  std_logic;
      TXN            : out std_logic;
      TXP            : out std_logic
   );
end rio2cmd;


