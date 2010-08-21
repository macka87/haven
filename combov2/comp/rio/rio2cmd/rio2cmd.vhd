
-- rio2cmd.vhd: Command Protocol Transceiver via RocketIO (architecture) 
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
use work.rio_codes.ALL;
use work.commands.ALL;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of rio2cmd is

component rio_ctrl
   port (
      -- Clock, reset
      REFCLK         : in std_logic;                        -- RocketIO clock
      USRCLK         : in std_logic;                        -- FPGA Fabric Clock
      USRCLK2        : in std_logic;                        -- FPGA Fabric Clock
      RESET          : in std_logic;                        -- Reset Signal

      -- TX
      TXDATA         : in std_logic_vector(31 downto 0);    -- Input Data
      TXCHARISK      : in std_logic_vector(3 downto 0);     -- Signal Comma
      TXRUNDISP      : out std_logic_vector(3 downto 0);    -- Running Disparity of Currently Encoded Data

      -- RX
      RXDATA         : out std_logic_vector(31 downto 0);   -- Output Data
      RXCHARISK      : out std_logic_vector(3 downto 0);    -- Signal Comma
      RXSYNCLOSS     : out std_logic_vector (1 downto 0);   -- State of Sync Logic
      RXCLKCORCNT    : out std_logic_vector(2 downto 0);    -- State of Clock Correction Logic
      RXBUFSTATUS    : out std_logic_vector(1 downto 0);    -- State of Recieve Buffer
      RXCHECKINGCRC  : out std_logic;                       -- This signal indicates if the RXCRCERR is valid
      RXCRCERR       : out std_logic;                       -- CRC Check Error
      RXREALIGN      : out std_logic;                       -- Signals whenever, the serial data is realigned from a comma character
      RXCOMMADET     : out std_logic;                       -- This signal indicates if a comma character has been detected in the serial data.
      RXCHARISCOMMA  : out std_logic_vector(3 downto 0);    -- Signals that a specific byte of RXDATA is a comma character
      RXDISPERR      : out std_logic_vector (3 downto 0);   -- This signal indicates if a diparity error occured


      -- MGT interface
      RXN            : in  std_logic;
      RXP            : in  std_logic;
      TXN            : out std_logic;
      TXP            : out std_logic;
      
      -- Control and status interface
      RXPOLARITY     : in std_logic;                        -- Interchange the RX Polarity
      TXPOLARITY     : in std_logic;                        -- Interchange the TX Polarity
      LOOPBACK       : in std_logic_vector(1 downto 0)      -- Switch Loopback(1) or Normal(0) Mode
   );
end component;

component transmitter 
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Command protocol interface
      DI       : in std_logic_vector(31 downto 0);
      DI_CMD   : in std_logic_vector(3 downto 0);
      DI_DV    : in std_logic;
      FULL     : out std_logic;

      -- RocketIO controller interface
      TXDATA   : out std_logic_vector(31 downto 0);
      TXCHARISK: out std_logic_vector(3 downto 0)
   );
end component;

component receiver is
   port (
      -- Common Input
      USRCLK2  : in std_logic;
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Command protocol interface
      DO       : out std_logic_vector(31 downto 0);
      DO_CMD   : out std_logic_vector(3 downto 0);
      DO_DV    : out std_logic;
      FULL     : in std_logic;

      -- Status inteface
      STATUS   : out std_logic_vector(7 downto 0);
      STATUS_DV: out std_logic;

      -- RocketIO controller interface
      RXDATA         : in std_logic_vector(31 downto 0);
      RXCHARISK      : in std_logic_vector(3 downto 0);
      RXREALIGN      : in std_logic;
      RXCOMMADET     : in std_logic;
      RXCHECKINGCRC  : in std_logic;
      RXCRCERR       : in std_logic
   );
end component;

signal gnd        : std_logic;
signal pwr        : std_logic;

-- TX
signal txdata        : std_logic_vector(31 downto 0);
signal txcharisk     : std_logic_vector(3 downto 0);
signal txrundisp     : std_logic_vector(3 downto 0);

-- RX
signal rxdata        : std_logic_vector(31 downto 0);
signal rxcharisk     : std_logic_vector(3 downto 0);
signal rxsyncloss    : std_logic_vector(1 downto 0);
signal rxclkcorcnt   : std_logic_vector(2 downto 0);
signal rxbufstatus   : std_logic_vector(1 downto 0);
signal rxcheckingcrc : std_logic;
signal rxcrcerr      : std_logic;
signal rxrealign     : std_logic;
signal rxcommadet    : std_logic;
signal rxchariscomma : std_logic_vector(3 downto 0);
signal rxdisperr     : std_logic_vector(3 downto 0);

begin

gnd <= '0';
pwr <= '1';

rio_ctrl_u: rio_ctrl
   port map (
      -- Clock, reset
      REFCLK         => REFCLK,
      USRCLK         => USRCLK,
      USRCLK2        => USRCLK2,
      RESET          => RESET,

      -- TX
      TXDATA         => txdata,
      TXCHARISK      => txcharisk,
      TXRUNDISP      => txrundisp,

      -- RX
      RXDATA         => rxdata,
      RXCHARISK      => rxcharisk,
      RXSYNCLOSS     => rxsyncloss,
      RXCLKCORCNT    => rxclkcorcnt,
      RXBUFSTATUS    => rxbufstatus,
      RXCHECKINGCRC  => rxcheckingcrc,
      RXCRCERR       => rxcrcerr,
      RXREALIGN      => rxrealign,
      RXCOMMADET     => rxcommadet,
      RXCHARISCOMMA  => rxchariscomma,
      RXDISPERR      => rxdisperr,


      -- MGT interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP,
      
      -- Control and status interface
      RXPOLARITY     => gnd,
      TXPOLARITY     => gnd,
      LOOPBACK       => LOOPBACK
   );

tx_gener: if (TX_LOGIC = true) generate
transmitter_u: transmitter
   port map (
      -- Common Input
      USRCLK2  => USRCLK2,
      CMDCLK   => CMDCLK,
      RESET    => RESET,
      
      -- Command protocol interface
      DI       => DI,
      DI_CMD   => DI_CMD,
      DI_DV    => DI_DV,
      FULL     => DI_FULL,

      -- RocketIO controller interface
      TXDATA   => txdata,
      TXCHARISK=> txcharisk
   );
end generate tx_gener;

tx_ngener: if (TX_LOGIC = false) generate
      txdata    <= IDLE_PRES & IDLE_PRES;
      txcharisk <= "1010";
end generate tx_ngener;

rx_gener: if (RX_LOGIC = true) generate
receiver_u: receiver
   port map (
      -- Common Input
      USRCLK2  => USRCLK2,
      CMDCLK   => CMDCLK,
      RESET    => RESET,
      
      -- Command protocol interface
      DO       => DO,
      DO_CMD   => DO_CMD,
      DO_DV    => DO_DV,
      FULL     => DO_FULL,

      -- Status inteface
      STATUS   => STATUS,
      STATUS_DV=> STATUS_DV,

      -- RocketIO controller interface
      RXDATA         => rxdata,
      RXCHARISK      => rxcharisk,
      RXCOMMADET     => rxcommadet,
      RXREALIGN      => rxrealign,
      RXCHECKINGCRC  => rxcheckingcrc,
      RXCRCERR       => rxcrcerr
   );
end generate rx_gener;

rx_ngener: if (RX_LOGIC = false) generate
   DO <= C_CMD_IDLE & C_CMD_IDLE & C_CMD_IDLE & C_CMD_IDLE;
   DO_CMD <= X"F";
   DO_DV <= '0';
   STATUS <= X"00";
   STATUS_DV <= '0';
end generate rx_ngener;
   
end behavioral;


