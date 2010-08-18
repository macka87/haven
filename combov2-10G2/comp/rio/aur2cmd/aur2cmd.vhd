
-- aur2cmd.vhd: Architecture of aur2cmd entity 
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
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of aur2cmd is

component transmitter is
   generic (
      DATA_WIDTH        : integer
   );
   port (
      -- Common Input
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Command protocol interface
      DI       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      DI_CMD   : in std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      DI_DV    : in std_logic;

      -- Aurora LocalLink TX interface
      TX_D             : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM           : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N     : out std_logic;
      TX_SOF_N         : out std_logic;
      TX_EOF_N         : out std_logic;
      TX_DST_RDY_N     : in std_logic
      );
end component;

component receiver is
   generic (
      DATA_WIDTH        : integer
   );
   port (
      -- Common Input
      CMDCLK   : in std_logic;
      RESET    : in std_logic;
      
      -- Aurora LocalLink RX interface
      RX_D             : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM           : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SRC_RDY_N     : in std_logic;
      RX_SOF_N         : in std_logic;
      RX_EOF_N         : in std_logic;
      RX_DST_RDY_N     : out std_logic;

      -- Command protocol interface
      DO       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DO_CMD   : out std_logic_vector((DATA_WIDTH/8)-1 downto 0);
      DO_DV    : out std_logic;
      FULL     : in std_logic
   );
end component;

component aurfc is
   generic (
      LANES             : integer;                 -- Number of lanes 
      DATA_PATHS        : integer;                 -- Number of data paths
      DISCARD_BAD_PACKETS : boolean := false;

      RX_IS_HEADER      : boolean := true;
      RX_IS_FOOTER      : boolean := true;
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     : integer := 512;
      TX_STATUS_WIDTH   : integer := 6;
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     : integer := 512;
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   : integer := 6;
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110";

      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK   : std_logic_vector := "00"
   );
   port (
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock command protocol interface 
      
      -- LocalLink TX Interface
      TX_D             : in std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM           : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SRC_RDY_N     : in std_logic;
      TX_SOF_N         : in std_logic;
      TX_SOP_N         : in std_logic;
      TX_EOF_N         : in std_logic;
      TX_EOP_N         : in std_logic;
      TX_DST_RDY_N     : out std_logic;

      -- LocalLink RX Interface

      RX_D             : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM           : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
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

      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0)
   );
end component;

-- common signals
signal gnd     : std_logic;
signal pwr     : std_logic;

signal tx_d    :  std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_rem     :  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal tx_src_rdy_n     :  std_logic;
signal tx_sof_n      :  std_logic;
signal tx_eof_n      :  std_logic;
signal tx_dst_rdy_n     :  std_logic;
signal rx_d    :  std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_rem     :  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_src_rdy_n     :  std_logic;
signal rx_sof_n      :  std_logic;
signal rx_eof_n      :  std_logic;
signal rx_dst_rdy_n     :  std_logic;

signal ufc_tx_ack_n_i : std_logic;

signal rx_full    : std_logic;

begin

gnd <= '0';
pwr <= '1';

transmitter_u: transmitter
   generic map(
      DATA_WIDTH  => DATA_WIDTH
   )
   port map(
      -- Common Input
      CMDCLK   => CMDCLK,
      RESET    => RESET,
      
      -- Command protocol interface
      DI       => DATA_IN,
      DI_CMD   => CMD_IN,
      DI_DV    => SRC_RDY_IN,

      -- Aurora LocalLink TX interface
      TX_D             => tx_d,
      TX_REM           => tx_rem,
      TX_SRC_RDY_N     => tx_src_rdy_n,
      TX_SOF_N         => tx_sof_n,
      TX_EOF_N         => tx_eof_n,
      TX_DST_RDY_N     => tx_dst_rdy_n
   );
   DST_RDY_IN <= not tx_dst_rdy_n;

receiver_u: receiver
   generic map(
      DATA_WIDTH  => DATA_WIDTH
   )
   port map(
      -- Common Input
      CMDCLK   => CMDCLK,
      RESET    => RESET,
      
      -- Aurora LocalLink RX interface
      RX_D             => rx_d,
      RX_REM           => rx_rem,
      RX_SRC_RDY_N     => rx_src_rdy_n,
      RX_SOF_N         => rx_sof_n,
      RX_EOF_N         => rx_eof_n,
      RX_DST_RDY_N     => rx_dst_rdy_n,

      -- Command protocol interface
      DO       => DATA_OUT,
      DO_CMD   => CMD_OUT,
      DO_DV    => SRC_RDY_OUT,
      FULL     => rx_full
   );
   rx_full <= not DST_RDY_OUT;

aurfc_u: aurfc
   generic map(
      LANES             => LANES,
      DATA_PATHS        => DATA_WIDTH/8,
      DISCARD_BAD_PACKETS => true,

      RX_IS_HEADER      => true,
      RX_IS_FOOTER      => true,
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     => TX_FIFO_ITEMS,
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     => RX_FIFO_ITEMS,
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         => XON_LIMIT,
      XOFF_LIMIT        => XOFF_LIMIT,

      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK          => LOOPBACK
   )
    port map(
            -- Common Input
            RESET          => RESET,
            REFCLK         => REFCLK,
            USRCLK         => USRCLK,
            USRCLK2        => USRCLK2,
            CMDCLK         => CMDCLK,
      
            -- LocalLink TX Interface
            TX_D             => tx_d,
            TX_REM           => tx_rem,
            TX_SRC_RDY_N     => tx_src_rdy_n,
            TX_SOF_N         => '0',
            TX_SOP_N         => tx_sof_n,
            TX_EOF_N         => '0',
            TX_EOP_N         => tx_eof_n,
            TX_DST_RDY_N     => tx_dst_rdy_n,

            -- LocalLink RX Interface
            RX_D             => rx_d,
            RX_REM           => rx_rem,
            RX_SRC_RDY_N     => rx_src_rdy_n,
            RX_SOF_N         => open,
            RX_SOP_N         => rx_sof_n,
            RX_EOF_N         => open,
            RX_EOP_N         => rx_eof_n,
            RX_DST_RDY_N     => rx_dst_rdy_n,

            -- Error Detection Interface
            HARD_ERROR       => HARD_ERROR,
            SOFT_ERROR       => SOFT_ERROR,
            FRAME_ERROR      => FRAME_ERROR,

            -- MGT Serial I/O
            RXP              => RXP,
            RXN              => RXN,
            TXP              => TXP,
            TXN              => TXN

         );

end behavioral;




