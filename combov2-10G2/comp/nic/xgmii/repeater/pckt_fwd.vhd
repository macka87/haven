-- pckt_fwd.vhd: XGMII to XGMII asynchronous convertor (packet forwarder)
-- Copyright (C) 2008 CESNET
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

entity xgmii_pckt_fwd is
   generic (
      FIFO_SIZE : integer := 512
   );
   port (
      RESET     : in  std_logic;   -- Asynchronous Reset
      EN        : in  std_logic;   -- Packet forwarding enable
      -- GMII RX interface
      RX_CLK    : in  std_logic;   -- GMII RX clock
      RX_D      : in  std_logic_vector(63 downto 0); -- XGMII RX data, RX_CLK sync
      RX_C      : in  std_logic_vector( 7 downto 0); -- GMII RX command, RX_CLK sync
      -- GMII TX interface
      TX_CLK    : in  std_logic;   -- GMII TX clock input
      TX_D      : out std_logic_vector(63 downto 0); -- XGMII TX data, TX_CLK sync
      TX_C      : out std_logic_vector( 7 downto 0); -- XGMII TX command, TX_CLK sync
      --
      OVERFLOW  : out std_logic; -- FIFO overflow indicator (RX packet lost)
      UNDERFLOW : out std_logic  -- FIFO underflow indicator (TX packet lost)
   );
end xgmii_pckt_fwd;

architecture behavioral of xgmii_pckt_fwd is

constant C_SOP : std_logic_vector(7 downto 0) := X"FB";
constant C_EOP : std_logic_vector(7 downto 0) := X"FD";

signal rxd_shift       : std_logic := '0';
signal rx_drop_h       : std_logic;
signal fifo_drop       : std_logic;
signal reg_rxd         : std_logic_vector(63 downto 0);
signal reg_rxc         : std_logic_vector( 7 downto 0);
signal fifo_status     : std_logic_vector(1 downto 0);
signal fifo_dwr        : std_logic_vector(64+8-1 downto 0);
signal fifo_drd        : std_logic_vector(64+8-1 downto 0);
signal fifo_rd         : std_logic;
signal fifo_do_vld     : std_logic;
signal fifo_wr         : std_logic; 
signal reg_fifo_afull  : std_logic;
signal reg2_fifo_afull : std_logic;
signal reg_fifo_aempty : std_logic;
signal reg2_fifo_aempty: std_logic;
signal fifo_aempty     : std_logic; -- Fifo almost empty
signal fifo_afull      : std_logic; -- Fifo almost empty
signal fifo_empty      : std_logic;
signal fifo_full       : std_logic;
signal txd_i           : std_logic_vector(63 downto 0);
signal txc_i           : std_logic_vector( 7 downto 0);
signal tx_idle         : std_logic;
-- signal rx_idle_h       : std_logic;
signal rx_idle_l       : std_logic;
signal tx_d_reg        : std_logic_vector(63 downto 0);
signal tx_c_reg        : std_logic_vector( 7 downto 0);

begin

-- REPEATER FIFO --------------------------------------------------------

FIFO_IN_REGS : process(RX_CLK)
begin
   if RX_CLK'event and RX_CLK = '1' then
      reg_rxd  <= RX_D;
      reg_rxc  <= RX_C;
      if (rxd_shift = '1') then
         -- Realign High & Low words after the drop
         fifo_dwr <= RX_C(3 downto 0) & reg_rxc(7 downto 4) & RX_D(31 downto 0) & reg_rxd(63 downto 32);
      elsif (rxd_shift = '0') then
         -- Normal operation
         fifo_dwr <= RX_C & RX_D;
      end if;
      if (rx_drop_h = '1') then
         rxd_shift <= not rxd_shift;
      end if;
      fifo_wr <= not fifo_drop;
   end if;
end process;

GEN_RX_FLAGS: process(RX_D, RX_C, reg_rxd, reg_rxc)
begin
-- Detect 12 IDLE sequences on the FIFO input
--    if (((reg_rxd(15 downto  8) = X"07") and (reg_rxc(1) = '1')) and
--        ((RX_D( 7 downto  0) = X"07")    and (RX_C(0) = '1')))
--    then
--       rx_idle_h <= '1'; 
--    else
--       rx_idle_h <= '0';
--    end if;
   if (((RX_D(39 downto 32) = X"07")    and (RX_C(4) = '1')) and
       ((reg_rxd(47 downto 40) = X"07") and (reg_rxc(5) = '1'))) 
   then
      rx_idle_l <= '1';
   else
      rx_idle_l <= '0';
   end if;   
end process;

RX_DROP_CTRL: process(reg2_fifo_afull, rx_idle_l)
begin
   if (reg2_fifo_afull = '1') and (rx_idle_l = '1') then
      rx_drop_h <= '1';
   else
      rx_drop_h <= '0';
   end if;
end process;

fifo_drop <= rx_drop_h and (not rxd_shift);

XGMII_FIFO: entity work.asfifo_bram
generic map (
   DATA_WIDTH   => 64+8,      -- Data Width
   ITEMS        => FIFO_SIZE, -- Item in memory needed, one item size is DATA_WIDTH
--   DISTMEM_TYPE => 16,      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
   AUTO_PIPELINE => false,
   STATUS_WIDTH  => 2
)
port map (
   RESET    => RESET,
   -- Write interface -- 
   CLK_WR   => RX_CLK,
   DI       => fifo_dwr,
   WR       => fifo_wr,
   FULL     => fifo_full,
   STATUS   => fifo_status,
   -- Read interface
   CLK_RD   => TX_CLK,
   DO       => fifo_drd,
   DO_DV    => fifo_do_vld,
   RD       => fifo_rd,
   EMPTY    => fifo_empty
);

FIFO_AE_FLAG: process(fifo_status) -- Fifo allmost empty
begin
   if (fifo_status(fifo_status'high downto fifo_status'high-1) = "00") then
      fifo_aempty <= '1';
   else
      fifo_aempty <= '0';
   end if;
   --
   if (fifo_status(fifo_status'high downto fifo_status'high-1) = "11") then
      fifo_afull <= '1';
   else
      fifo_afull <= '0';
   end if;
end process;
   
-- Reclock FIFO STATUS signal to avoid metastability
FIFO_TXSTAT_RECLOCK: process(TX_CLK)
begin
   if TX_CLK'event and TX_CLK = '1' then
      reg_fifo_aempty  <= fifo_aempty;
      reg2_fifo_aempty <= reg_fifo_aempty;
   end if;
end process;

-- Reclock FIFO STATUS signal to avoid metastability
FIFO_RXSTAT_RECLOCK: process(RX_CLK)
begin
   if RX_CLK'event and RX_CLK = '1' then
      reg_fifo_afull  <= fifo_afull;
      reg2_fifo_afull <= reg_fifo_afull;
   end if;
end process;

-- XST-aware compare-mux
GEN_TX_FLAGS: process(fifo_drd)
begin
   -- Detect IDLE sequence on the FIFO output
   if ((fifo_drd(63 downto 56) = X"07") and (fifo_drd(71) = '1')) and 
      ((fifo_drd( 7 downto  0) = X"07") and (fifo_drd(64) = '1')) then
      tx_idle <= '1';
   else
      tx_idle <= '0';
   end if;
end process;

FIFO_RD_CTRL: process(reg2_fifo_aempty, tx_idle)
begin
   if (reg2_fifo_aempty = '1') and (tx_idle = '1') then
      fifo_rd <= '0';
   else
      fifo_rd <= '1';
   end if;
end process;

TX_MUX: process(fifo_drd, fifo_do_vld, EN)
begin
   if (fifo_do_vld = '1') and (EN = '1') then
      txd_i <= fifo_drd(63 downto 0);
      txc_i <= fifo_drd(63+8 downto 64);
   else
      txd_i <= X"0707070707070707"; -- Idle
      txc_i <= "11111111";
   end if;
end process;

OUT_REGS: process(TX_CLK)
begin
   if TX_CLK'event and TX_CLK = '1' then
      tx_d_reg <= txd_i;
      tx_c_reg <= txc_i;
   end if;
end process;

TX_D <= tx_d_reg;      
TX_C <= tx_c_reg;      

UNDERFLOW <= fifo_empty;
OVERFLOW  <= fifo_full;

end behavioral;
