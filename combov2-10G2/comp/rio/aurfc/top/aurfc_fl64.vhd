-- aurfc_fl64.vhd: FrameLink via RIO (aurora based)
-- Copyright (C) 2006 CESNET
-- Author(s): Jiri Tobola <tobola@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity aurfc_fl64 is
   generic(
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
   port(
   
      -- Common Input
      RESET          : in std_logic;      -- Design reset
      REFCLK         : in std_logic;      -- RocketIO clock (connected to xtal directly - no BUFGs or DCMs)
      USRCLK         : in std_logic;      -- Clock to clock transmit and receive logic
      USRCLK2        : in std_logic;      -- Clock to clock transmit and receive logic (USRCLK halfrated and shifted)
      CMDCLK         : in std_logic;      -- Clock to clock FrameLink interface 
      
      -- FrameLink Interface
      TX             : inout t_fl64;
      RX             : inout t_fl64;

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     : out std_logic;     -- Hard error detected. (Active-high, asserted until Aurora core resets).
      SOFT_ERROR     : out std_logic;     -- Soft error detected in the incoming serial stream. (Active-high, 
                                          -- asserted for a single clock).
      FRAME_ERROR    : out std_logic;     -- Channel frame/protocol error detected. This port is active-high 
                                          -- and is asserted for a single clock.
      -- Status Interface
      TX_STATUS      : out std_logic_vector(TX_STATUS_WIDTH-1 downto 0);   -- TX fifo status
      RX_STATUS      : out std_logic_vector(RX_STATUS_WIDTH-1 downto 0);   -- RX fifo status
      CHANNEL_UP     : out std_logic;
      
      -- Debug
      D_STATE        : out std_logic_vector(1 downto 0);
      D_CNT_XON   : out std_logic_vector(31 downto 0);
      D_CNT_XOFF  : out std_logic_vector(31 downto 0);
      D_RX_FULL      : out std_logic_vector(15 downto 0);

      -- MGT Interface
      RXN            : in  std_logic_vector(1 downto 0);
      RXP            : in  std_logic_vector(1 downto 0);
      TXN            : out std_logic_vector(1 downto 0);
      TXP            : out std_logic_vector(1 downto 0)

   );
end entity aurfc_fl64;

architecture full of aurfc_fl64 is

   constant DATA_WIDTH : integer := 64;
   signal rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

   -- process to remove X signals in simulations
   process(rx_data)
   begin
      RX.DATA <= rx_data;
      -- for simulations only:
      -- pragma translate_off 
      for aux in 0 to DATA_WIDTH-1 loop
         if (rx_data(aux) = 'X') then
            RX.DATA(aux) <= '0';
         else
            RX.DATA(aux) <= rx_data(aux);
         end if;
      end loop;
      -- pragma translate_on 
   end process; 

   AURFC_FL64_I: entity work.aurfc
   generic map(
      LANES             => 2,
      DATA_PATHS        => DATA_WIDTH/8,
      DISCARD_BAD_PACKETS => DISCARD_BAD_PACKETS,
      RX_IS_HEADER      => RX_IS_HEADER,
      RX_IS_FOOTER      => RX_IS_FOOTER,
      -- TX_FIFO_ITEMS = 2^n
      TX_FIFO_ITEMS     => TX_FIFO_ITEMS,
      TX_STATUS_WIDTH   => TX_STATUS_WIDTH,
      -- RX_FIFO_ITEMS = 2^n
      RX_FIFO_ITEMS     => RX_FIFO_ITEMS,
      -- RX_STATUS_WIDTH must be greater or equal 3!
      RX_STATUS_WIDTH   => RX_STATUS_WIDTH,
      -- FIFO status to match to generate XON/XOFF message
      XON_LIMIT         => XON_LIMIT,
      XOFF_LIMIT        => XOFF_LIMIT,
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK          => LOOPBACK
   )
   port map (
      -- Common Input
      RESET          => reset,
      REFCLK         => refclk,
      USRCLK         => usrclk,
      USRCLK2        => usrclk2,
      CMDCLK         => cmdclk,
      
      -- FrameLink TX Interface
      TX_D             => TX.DATA,
      TX_REM           => TX.DREM,
      TX_SRC_RDY_N     => TX.SRC_RDY_N,
      TX_SOF_N         => TX.SOF_N,
      TX_SOP_N         => TX.SOP_N,
      TX_EOF_N         => TX.EOF_N,
      TX_EOP_N         => TX.EOP_N,
      TX_DST_RDY_N     => TX.DST_RDY_N,

      -- FrameLink RX Interface
      RX_D             => rx_data,
      RX_REM           => RX.DREM,
      RX_SRC_RDY_N     => RX.SRC_RDY_N,
      RX_SOF_N         => RX.SOF_N,
      RX_SOP_N         => RX.SOP_N,
      RX_EOF_N         => RX.EOF_N,
      RX_EOP_N         => RX.EOP_N,
      RX_DST_RDY_N     => RX.DST_RDY_N,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => HARD_ERROR,
      SOFT_ERROR     => SOFT_ERROR,
      FRAME_ERROR    => FRAME_ERROR,

      -- Status Interface
      TX_STATUS      => TX_STATUS,
      RX_STATUS      => RX_STATUS,
      CHANNEL_UP     => CHANNEL_UP,

      -- Debug
      D_STATE        => D_STATE,
      D_CNT_XON   => D_CNT_XON,
      D_CNT_XOFF  => D_CNT_XOFF,
      D_RX_FULL   => D_RX_FULL,

      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );

end architecture full; 

