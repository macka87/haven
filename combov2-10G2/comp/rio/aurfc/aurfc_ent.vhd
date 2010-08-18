
-- aurfc_ent.vhd: Aurora with flow control 
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

entity aurfc is
   generic (
      LANES             : integer;                 -- Number of lanes 
      DATA_PATHS        : integer;                 -- Number of data paths
      DISCARD_BAD_PACKETS : boolean := false;

      RX_IS_HEADER      : boolean := true;
      RX_IS_FOOTER      : boolean := true;
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      TX_STATUS_WIDTH   : integer := 3;
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   : integer := 3;
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   );
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no DCMs, insert BUFG buffer!)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock FrameLink interface 
      
      -- LocalLink TX Interface
      TX_D             : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      TX_REM           : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      TX_SRC_RDY_N     : in std_logic;
      TX_SOF_N         : in std_logic;
      TX_SOP_N         : in std_logic;
      TX_EOF_N         : in std_logic;
      TX_EOP_N         : in std_logic;
      TX_DST_RDY_N     : out std_logic;

      -- LocalLink RX Interface
      RX_D             : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      RX_REM           : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      RX_SRC_RDY_N     : out std_logic;
      RX_SOF_N         : out std_logic;
      RX_SOP_N         : out std_logic;
      RX_EOF_N         : out std_logic;
      RX_EOP_N         : out std_logic;
      RX_DST_RDY_N     : in std_logic;

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : out std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : out std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                          -- asserted for a single clock).
      FRAME_ERROR    : out std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                          -- and is asserted for a single clock.
      -- Status Interface
      TX_STATUS      : out std_logic_vector(TX_STATUS_WIDTH-1 downto 0);   -- TX fifo status
      RX_STATUS      : out std_logic_vector(RX_STATUS_WIDTH-1 downto 0);   -- RX fifo status
      CHANNEL_UP     : out std_logic;                                      -- Aurora Channel Status (0: channel down, 1: channel up)

      -- Debug
      D_STATE        : out std_logic_vector(1 downto 0);
      D_CNT_XON   : out std_logic_vector(31 downto 0);
      D_CNT_XOFF  : out std_logic_vector(31 downto 0);
      D_RX_FULL      : out std_logic_vector(15 downto 0);

      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0)
   );
end aurfc;






