-- gmii_pckt_fwd.vhd: GMII to GMII asynchronous convertor (packet forwarder)
-- Copyright (C) 2005 CESNET
-- Author(s):  Stepan Friedl <friedl@liberouter.org>
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
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity gmii_pckt_fwd is
   generic (
      TX_DELAY      : integer := 8;
      TX_PACKET_GAP : integer := 4;
      FIFO_SIZE     : integer := 16
   );
   port (
      RESET     : in  std_logic;   -- Asynchronous Reset
      EN        : in  std_logic;   -- Packet forwarding enable
      -- GMII RX interface
      RX_CLK    : in  std_logic;   -- GMII RX clock
      RX_D      : in  std_logic_vector(7 downto 0); -- GMII RX data, RX_CLK sync
      RX_DV     : in  std_logic;   -- GMII RX data valid, RX_CLK sync
      RX_ER     : in  std_logic;   -- GMII RX error, RX_CLK sync
      -- GMII TX interface
      TX_CLK    : in  std_logic;   -- GMII TX clock input
      TX_D      : out std_logic_vector(7 downto 0); -- GMII TX data, TX_CLK sync
      TX_EN     : out std_logic;   -- GMII TX data valid, TX_CLK sync
      TX_ER     : out std_logic;   -- GMII TX error, TX_CLK sync
      --
      OVERFLOW  : out std_logic; -- FIFO overflow indicator (RX packet lost)
      UNDERFLOW : out std_logic  -- FIFO underflow indicator (TX packet lost)
   );
end gmii_pckt_fwd;

architecture behavioral of gmii_pckt_fwd is

constant CMD_EOP_BIT : integer := 0;
constant CMD_ERR_BIT : integer := 1;

signal fifo_full       : std_logic;
signal fifo_status     : std_logic_vector(1 downto 0);
signal fifo_empty      : std_logic;
signal fifo_dwr        : std_logic_vector(8 downto 0);
signal fifo_drd        : std_logic_vector(8 downto 0);
signal fifo_wr         : std_logic;
signal fifo_rd         : std_logic;

signal rx_dv_i         : std_logic;
signal rx_fsm_eop      : std_logic;
signal rx_fsm_err      : std_logic;
signal rx_cmd_flag     : std_logic;
signal rx_err_flag     : std_logic;
signal rx_cmd          : std_logic_vector(7 downto 0);

signal tx_fsm_en       : std_logic;
signal tx_fsm_err      : std_logic;
signal tx_delay_start  : std_logic;
signal tx_cntr_sel     : std_logic;
signal tx_delay_cntr   : std_logic_vector(5 downto 0);
signal tx_dly_cntr_value : std_logic_vector(5 downto 0);
signal tx_cmd_flag     : std_logic;
signal tx_d_cmd        : std_logic_vector(7 downto 0);
signal tx_start        : std_logic;
signal tx_eop          : std_logic;
signal tx_err          : std_logic;
signal reg_tx_er       : std_logic;
signal reg_tx_en       : std_logic;
signal reg_tx_d        : std_logic_vector(7 downto 0);

begin

rx_dv_i <= RX_DV and EN;

-- **************************************************************************
-- RX part
-- **************************************************************************
RX_FSM: entity work.rep_rx_fsm
port map (
   RESET     => RESET,
   CLK       => RX_CLK,
   -- Control inputs
   RX_DV     => rx_dv_i,
   RX_ERR    => RX_ER,
   FIFO_FULL => fifo_full,
   -- Outputs
   OVERFLOW  => OVERFLOW,
   FIFO_WR   => fifo_wr,
   EOP       => rx_fsm_eop,
   ERR       => rx_fsm_err
);

rx_cmd_flag <= rx_fsm_err or rx_fsm_eop or RX_ER;
rx_err_flag <= rx_fsm_err or RX_ER;
rx_cmd      <= (CMD_EOP_BIT=>rx_fsm_eop, CMD_ERR_BIT=>rx_err_flag, others=>'0');

fifo_dwr <= '0' & RX_D   when rx_cmd_flag = '0' else
            '1' & rx_cmd;

-- **************************************************************************
-- FIFO
-- **************************************************************************
WRFIFO: entity work.asfifo
generic map(
      DATA_WIDTH   => 9,
      ITEMS        => FIFO_SIZE,
      DISTMEM_TYPE => 16,
      STATUS_WIDTH => 2
)
port map(
   RESET  => RESET,
   -- Write interface
   CLK_WR => RX_CLK,
   DI     => fifo_dwr,
   WR     => fifo_wr,
   FULL   => fifo_full,
   -- Read interface
   CLK_RD => TX_CLK,
   DO     => fifo_drd,
   RD     => fifo_rd,
   EMPTY  => fifo_empty,
   STATUS => fifo_status
);

-- **************************************************************************
-- TX part
-- **************************************************************************
TX_REP_FSM : entity work.rep_tx_fsm
port map (
   RESET       => RESET,
   CLK         => TX_CLK,
   -- Control inputs
   FIFO_EMPTY  => fifo_empty,
   START       => tx_start,
   EOP         => tx_eop,
   -- Outputs
   UNDERFLOW   => UNDERFLOW,
   TX_EN       => tx_fsm_en,
   TX_ERR      => tx_fsm_err,
   FIFO_RD     => fifo_rd,
   TIMER_START => tx_delay_start,
   TIMER_SEL   => tx_cntr_sel
);

tx_cmd_flag <= fifo_drd(8);
tx_d_cmd    <= fifo_drd(7 downto 0);
tx_eop      <= (tx_cmd_flag and tx_d_cmd(CMD_EOP_BIT));
tx_err      <= (tx_cmd_flag and tx_d_cmd(CMD_ERR_BIT)) or tx_fsm_err;

tx_start    <= '1' when tx_delay_cntr = 0 else '0';
tx_dly_cntr_value <= conv_std_logic_vector(TX_DELAY,tx_delay_cntr'length) when
                        tx_cntr_sel = '0' else
                     conv_std_logic_vector(TX_PACKET_GAP,tx_delay_cntr'length);

DELAY_COUNTER: process(TX_CLK, RESET)
begin
   if TX_CLK'event and TX_CLK = '1' then
      if tx_delay_start = '1' then
         tx_delay_cntr <= tx_dly_cntr_value;
      elsif tx_start = '0' then
         tx_delay_cntr <= tx_delay_cntr - 1;
      end if;
   end if;
end process;

OUT_REGS: process(TX_CLK, RESET)
begin
   if RESET = '1' then
      reg_tx_er <= '0';
      reg_tx_en <= '0';
      reg_tx_d  <= (others => '0');
   elsif TX_CLK'event and TX_CLK = '1' then
      reg_tx_er <= tx_err;
      reg_tx_en <= tx_fsm_en;
      reg_tx_d  <= tx_d_cmd;
   end if;
end process;

TX_D  <= reg_tx_d;
TX_EN <= reg_tx_en;
TX_ER <= reg_tx_er;

end behavioral;
