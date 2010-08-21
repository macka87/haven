
-- aurvc.vhd: Aurora with virtual channels 
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
use work.aurvc_pkg.all; 

architecture behavioral of aurvc is

component aurvc_core is
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
end component;

component tx_buffer is
   generic (
      DATA_PATHS           : integer;     -- Number of bytes of data port
      CHANNEL_SIZE         : integer;     -- Number of items in channel buffer
      BYTE_QUOTA           : integer      -- Byte quota for this channel (see documentation for more information)
   );
   port (
      -- Common Input
      RESET                : in std_logic;
      FLCLK                : in std_logic;   -- FrameLink Interface clock

      -- FrameLink TX Interface
      TX_D             : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      TX_REM           : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      TX_SRC_RDY_N     : in std_logic;
      TX_SOF_N         : in std_logic;
      TX_SOP_N         : in std_logic;
      TX_EOF_N         : in std_logic;
      TX_EOP_N         : in std_logic;
      TX_DST_RDY_N     : out std_logic;

      -- AURVC_Core Interface
      BUFFER_CLK        : in std_logic;
      BUFFER_DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      BUFFER_REM        : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      BUFFER_EOP        : out std_logic;
      BUFFER_DV         : out std_logic;
      BUFFER_READ       : in std_logic;
      BUFFER_EMPTY      : out std_logic;
      BYTE_QUOTA_MET    : out std_logic;
      BYTE_QUOTA_RST    : in std_logic

   );
end component;

component rx_buffer is
   generic (
      DATA_PATHS           : integer;     -- Number of bytes of data port
      CHANNEL_SIZE         : integer;     -- Number of items in channel buffer
      XON_LIMIT            : std_logic_vector(2 downto 0);  -- XON limit for this channel (see documentation for more information)
      XOFF_LIMIT           : std_logic_vector(2 downto 0);  -- XOFF limit for this channel (see documentation for more information)
      RX_IS_HEADER         : boolean;
      RX_IS_FOOTER         : boolean
   );
   port (
      -- Common Input
      RESET                : in std_logic;
      FLCLK                : in std_logic;   -- FrameLink Interface clock

      -- FrameLink RX Interface
      RX_D             : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      RX_REM           : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      RX_SRC_RDY_N     : out std_logic;
      RX_SOF_N         : out std_logic;
      RX_SOP_N         : out std_logic;
      RX_EOF_N         : out std_logic;
      RX_EOP_N         : out std_logic;
      RX_DST_RDY_N     : in std_logic;

      -- AURVC_Core Interface
      BUFFER_CLK        : in std_logic;
      BUFFER_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      BUFFER_REM        : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      BUFFER_EOP        : in std_logic;
      BUFFER_WRITE      : in std_logic;
      BUFFER_FULL       : out std_logic;
      BUFFER_ALMOST_FULL: out std_logic;
      BUFFER_STATUS_IFC : out std_logic_vector(2 downto 0)
   );
end component;


  -------------------------------------------------------------------
  --
  --  ILA core component declaration
  --
  -------------------------------------------------------------------
--   component ila_rio
--     port
--     (
--       control     : inout std_logic_vector(35 downto 0);
--       clk         : in    std_logic;
--       trig0       : in    std_logic_vector(0 downto 0);
--       trig1       : in    std_logic_vector(0 downto 0);
--       trig2       : in    std_logic_vector(0 downto 0);
--       trig3       : in    std_logic_vector(31 downto 0);
--       trig4       : in    std_logic_vector(2 downto 0)
--     );
--   end component;
--   attribute noopt : boolean;
--   attribute noopt of ila_rio : component is TRUE;
-- 

signal buffer_clk       : std_logic;

signal tx_buffer_data   : std_logic_vector((TX_CHANNELS*(DATA_PATHS*8))-1 downto 0);
signal tx_buffer_rem    : std_logic_vector((TX_CHANNELS*log2(DATA_PATHS))-1 downto 0);
signal tx_buffer_eop    : std_logic_vector(TX_CHANNELS-1 downto 0);
signal tx_buffer_dv     : std_logic_vector(TX_CHANNELS-1 downto 0);
signal tx_buffer_read   : std_logic_vector(TX_CHANNELS-1 downto 0);
signal tx_buffer_empty  : std_logic_vector(TX_CHANNELS-1 downto 0);
signal byte_quota_met   : std_logic_vector(TX_CHANNELS-1 downto 0);
signal byte_quota_rst   : std_logic_vector(TX_CHANNELS-1 downto 0);

signal rx_buffer_data : std_logic_vector((DATA_PATHS*8)-1 downto 0);
signal rx_buffer_rem : std_logic_vector((log2(DATA_PATHS))-1 downto 0);
signal rx_buffer_eop : std_logic;
signal rx_buffer_write : std_logic_vector(RX_CHANNELS-1 downto 0);
signal rx_buffer_full  : std_logic_vector(RX_CHANNELS-1 downto 0);
signal rx_buffer_almost_full : std_logic_vector(RX_CHANNELS-1 downto 0);
signal rx_buffer_status      : std_logic_vector(3*RX_CHANNELS-1 downto 0);

begin

aurvc_core_u: aurvc_core
   generic map(
      LANES                => LANES,
      DATA_PATHS           => DATA_PATHS,
      TX_CHANNELS          => TX_CHANNELS,
      RX_CHANNELS          => RX_CHANNELS,
      -- "00": no loopback, "01": parallel loopbach, "10": serial loopback
      LOOPBACK             => LOOPBACK
   )
   port map(
      -- Common Input
      RESET          => RESET,
      REFCLK         => REFCLK,
      USRCLK         => USRCLK,
      USRCLK2        => USRCLK2,
      BUFFER_CLK     => buffer_clk,
      
      -- TX Buffers Interface
      TX_BUFFER_DATA       => tx_buffer_data,
      TX_BUFFER_REM        => tx_buffer_rem,
      TX_BUFFER_EOP        => tx_buffer_eop,
      TX_BUFFER_DV         => tx_buffer_dv,
      TX_BUFFER_READ       => tx_buffer_read,
      TX_BUFFER_EMPTY      => tx_buffer_empty,
      BYTE_QUOTA_MET       => byte_quota_met,
      BYTE_QUOTA_RST       => byte_quota_rst,

      -- RX Buffers Interface
      RX_BUFFER_DATA       => rx_buffer_data,
      RX_BUFFER_REM        => rx_buffer_rem,
      RX_BUFFER_EOP        => rx_buffer_eop,
      RX_BUFFER_WRITE      => rx_buffer_write,
      RX_BUFFER_ALMOST_FULL=> rx_buffer_almost_full,

      -- Upper Layer Error Detection RX Interface
      HARD_ERROR     => HARD_ERROR,
      SOFT_ERROR     => SOFT_ERROR,
      FRAME_ERROR    => FRAME_ERROR,

      -- Status Interface
      CHANNEL_UP     => CHANNEL_UP,

      -- MGT Interface
      RXN            => RXN,
      RXP            => RXP,
      TXN            => TXN,
      TXP            => TXP
   );

tx_buf_gen: for i in 0 to TX_CHANNELS-1 generate
   norm_gen: if (BUFFERS_PARAM.TXBUF_PARAMS(i).CHANNEL_SIZE > 0) generate
   tx_buffer_u: tx_buffer
   generic map(
      DATA_PATHS           => DATA_PATHS,
      CHANNEL_SIZE         => BUFFERS_PARAM.TXBUF_PARAMS(i).CHANNEL_SIZE,
      BYTE_QUOTA           => BUFFERS_PARAM.TXBUF_PARAMS(i).BYTE_QUOTA
   )
   port map(
      -- Common Input
      RESET                => RESET,
      FLCLK                => FLCLK,

      -- FrameLink TX Interface
      TX_D             => TX_D(((i+1)*(DATA_PATHS*8))-1 downto i*(DATA_PATHS*8)),
      TX_REM           => TX_REM(((i+1)*log2(DATA_PATHS))-1 downto i*log2(DATA_PATHS)),
      TX_SRC_RDY_N     => TX_SRC_RDY_N(i),
      TX_SOF_N         => TX_SOF_N(i),
      TX_SOP_N         => TX_SOP_N(i),
      TX_EOF_N         => TX_EOF_N(i),
      TX_EOP_N         => TX_EOP_N(i),
      TX_DST_RDY_N     => TX_DST_RDY_N(i),

      -- AURVC_Core Interface
      BUFFER_CLK        => buffer_clk,
      BUFFER_DATA       => tx_buffer_data(((i+1)*(DATA_PATHS*8))-1 downto i*(DATA_PATHS*8)),
      BUFFER_REM        => tx_buffer_rem(((i+1)*log2(DATA_PATHS))-1 downto i*log2(DATA_PATHS)),
      BUFFER_EOP        => tx_buffer_eop(i),
      BUFFER_DV         => tx_buffer_dv(i),
      BUFFER_READ       => tx_buffer_read(i),
      BUFFER_EMPTY      => tx_buffer_empty(i),
      BYTE_QUOTA_MET    => byte_quota_met(i),
      BYTE_QUOTA_RST    => byte_quota_rst(i)
   );
   end generate;

   no_txlogic_gen: if (BUFFERS_PARAM.TXBUF_PARAMS(i).CHANNEL_SIZE = 0) generate
      TX_DST_RDY_N(i) <= '1';
      tx_buffer_data(((i+1)*(DATA_PATHS*8))-1 downto i*(DATA_PATHS*8)) <= (others => '0');
      tx_buffer_rem(((i+1)*log2(DATA_PATHS))-1 downto i*log2(DATA_PATHS)) <= (others => '0');
      tx_buffer_eop(i) <= '0';
      tx_buffer_dv(i) <= '0';
      tx_buffer_empty(i) <= '1';
      byte_quota_met(i) <= '0';
   end generate;

end generate;

rx_buf_gen: for i in 0 to RX_CHANNELS-1 generate
   norm_gen: if (BUFFERS_PARAM.RXBUF_PARAMS(i).CHANNEL_SIZE > 0) generate
   rx_buffer_u: rx_buffer
   generic map(
      DATA_PATHS           => DATA_PATHS,
      CHANNEL_SIZE         => BUFFERS_PARAM.RXBUF_PARAMS(i).CHANNEL_SIZE,
      XON_LIMIT            => BUFFERS_PARAM.RXBUF_PARAMS(i).XON_LIMIT,
      XOFF_LIMIT           => BUFFERS_PARAM.RXBUF_PARAMS(i).XOFF_LIMIT,
      RX_IS_HEADER         => BUFFERS_PARAM.RXBUF_PARAMS(i).RX_IS_HEADER,
      RX_IS_FOOTER         => BUFFERS_PARAM.RXBUF_PARAMS(i).RX_IS_FOOTER
   )
   port map(
      -- Common Input
      RESET                => RESET,
      FLCLK                => FLCLK,

      -- FrameLink RX Interface
      RX_D             => RX_D(((i+1)*(DATA_PATHS*8))-1 downto i*(DATA_PATHS*8)),
      RX_REM           => RX_REM(((i+1)*log2(DATA_PATHS))-1 downto i*log2(DATA_PATHS)),
      RX_SRC_RDY_N     => RX_SRC_RDY_N(i),
      RX_SOF_N         => RX_SOF_N(i),
      RX_SOP_N         => RX_SOP_N(i),
      RX_EOF_N         => RX_EOF_N(i),
      RX_EOP_N         => RX_EOP_N(i),
      RX_DST_RDY_N     => RX_DST_RDY_N(i),

      -- AURVC_Core Interface
      BUFFER_CLK        => buffer_clk,
      BUFFER_DATA       => rx_buffer_data,
      BUFFER_REM        => rx_buffer_rem,
      BUFFER_EOP        => rx_buffer_eop,
      BUFFER_WRITE      => rx_buffer_write(i),
      BUFFER_FULL       => rx_buffer_full(i),
      BUFFER_ALMOST_FULL=> rx_buffer_almost_full(i),
      BUFFER_STATUS_IFC => rx_buffer_status((i+1)*3 - 1 downto i*3)
   );
   end generate;


   no_rxlogic_gen: if (BUFFERS_PARAM.RXBUF_PARAMS(i).CHANNEL_SIZE = 0) generate
      RX_D(((i+1)*(DATA_PATHS*8))-1 downto i*(DATA_PATHS*8))         <= (others => '0');
      RX_REM(((i+1)*log2(DATA_PATHS))-1 downto i*log2(DATA_PATHS))   <= (others => '0');
      RX_SRC_RDY_N(i)   <= '1';
      RX_SOF_N(i)       <= '1';
      RX_SOP_N(i)       <= '1';
      RX_EOF_N(i)       <= '1';
      RX_EOP_N(i)       <= '1';
      rx_buffer_almost_full(i) <= '0';
   end generate;

end generate;

--       -------------------------------------------------------------------
--       --
--       --  ILA core instance
--       --
--       -------------------------------------------------------------------
--       i_ila_rio : ila_rio
--         port map
--         (
--           control   => ILA_CONTROL,
--           clk       => buffer_clk,
--           trig0(0)  => rx_buffer_write(0),
--           trig1(0)  => rx_buffer_almost_full(0),
--           trig2(0)  => rx_buffer_eop,
--           trig3     => rx_buffer_data(31 downto 0),
--           trig4     => rx_buffer_status(2 downto 0)
--         );
-- 

end behavioral;

