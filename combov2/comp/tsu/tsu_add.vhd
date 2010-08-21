
-- tsu_add.vhd: Time stamp unit (Add-on card part)
-- Copyright (C) 2005 CESNET, Liberouter project
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

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
--       Entity :
-- -------------------------------------------------------------

entity TSU_ADD is
   port (
     -- Input from PTM
     REFCLK       : in std_logic; -- Reference clock
     PPFTS        : in std_logic; -- Pulse per fraction of Time Stamp
     TS_DV        : in std_logic; -- Data valid on TS
     TS           : in std_logic_vector (7 downto 0); -- Time stamp input
     -- Input from Add on Card
     RESET        : in std_logic; -- Reset form Add on
     CLK_ADD      : in std_logic; -- Clock from Add on
     TSADD_INIT   : in std_logic; -- TS init request from Add on Card
     TSADD_SHORT  : in std_logic; -- Short TS request from Add on Card
     -- Output to PTM
     TS_INIT      : out std_logic; -- Time stamp init request to PTM
     TS_SHORT     : out std_logic; -- Short time stamp request to PTM
     -- Output to Add on Card
     TSADD_DV     : out std_logic; -- Data valid on TS_ADD
     TS_ADD       : out std_logic_vector (63 downto 0) -- TS output
   );
end TSU_ADD;

-- -------------------------------------------------------------
--       Architecture :
-- -------------------------------------------------------------
architecture behavioral of TSU_ADD is

component BUFG
  port (
      I   : in std_logic;
      O   : out std_logic
   );
end component;

component IBUFG
  port (
      I   : in std_logic;
      O   : out std_logic
   );
end component;

component ASRQ2SYNC is
   port (
      -- Input
      ASY_PE   : in std_logic; -- pulse enable
      ASY_CLK  : in std_logic; -- clock from asynchronous signal
      SYNC_CLK : in std_logic; -- clock from synchrnous signal
      RESET    : in std_logic; -- main reset

      -- Output
      SYNC_PULS   : out std_logic -- output of pulse synchronous with sync clock
   );
end component ASRQ2SYNC;

component AD2SD is
   generic(
      DATA_WIDTH : integer
   );
   port (
      -- Input
      RESET          : in  std_logic;
      ASYNC_CLK      : in  std_logic;
      SYNC_CLK       : in  std_logic;
      ASYNC_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);

      -- Output
      SYNC_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end component;

component FDDRRSE
   port(
      Q       : out std_logic;
      D0      : in std_logic;
      D1      : in std_logic;
      C0      : in std_logic;
      C1      : in std_logic;
      CE      : in std_logic;
      R       : in std_logic;
      S       : in std_logic
   );
end component;

component tsuadd_fsm is
   port (
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- Input
      CNT_TS_MAX     : in std_logic;
      TSADD_INIT     : in std_logic;
      TSADD_SHORT    : in std_logic;
      TSPTM_DV       : in std_logic;

      -- Output
      TSADD_DV       : out std_logic;
      TS_WE_I        : out std_logic;
      CNT_PPFTS_RST  : out std_logic;
      TS_STORE       : out std_logic
   );
end component;

-- -------------------------------------------------------------
-- reg_ts signals
signal reg_ts        : std_logic_vector(63 downto 0);
signal reg_ts_load   : std_logic_vector(63 downto 8);
signal reg_ts_we     : std_logic_vector(7 downto 1);
signal reg_ts_we_i   : std_logic;
signal ts_reg_mx     : std_logic;

-- -------------------------------------------------------------
-- adder
signal adder_ts      : std_logic_vector(55 downto 0);

-- -------------------------------------------------------------
-- PTM interface registers
signal regiob_tsdv   : std_logic;
signal regiob_ts     : std_logic_vector(7 downto 0);
signal regiob_ppfts  : std_logic;
signal regiob_tsinit : std_logic;
signal regiob_tsshort: std_logic;

-- -------------------------------------------------------------
-- pipeline registers
signal reg_ppfts_pipe   : std_logic;
signal reg_ts_pipe      : std_logic_vector(7 downto 0);

-- -------------------------------------------------------------
-- cnt_ts signals
signal cnt_ts        : std_logic_vector(2 downto 0);
signal cnt_ts_ce     : std_logic;
signal cnt_ts_max    : std_logic;

-- -------------------------------------------------------------
-- dc_cnt_ts decoder signals
signal dc_en         : std_logic;
signal dc_out        : std_logic_vector(6 downto 0);

-- -------------------------------------------------------------
-- cnt_ppfts signals
signal cnt_ppfts     : std_logic_vector(3 downto 0);
signal cnt_ppfts_rst : std_logic;
signal cnt_ppfts_ce  : std_logic;
signal cnt_ppfts_ce_i: std_logic;

-- -------------------------------------------------------------
-- Add-on card interface signals
signal tsadd_dv_sync    : std_logic;
signal tsadd_init_sync  : std_logic;
signal tsadd_short_sync : std_logic;

-- -------------------------------------------------------------
-- TSUADD_FSM signals
signal ts_store         : std_logic;

-- -------------------------------------------------------------
-- clk signals
signal clk     : std_logic; -- refclk from ptm (80 MHz)
signal refclk_i: std_logic;

begin

-- -------------------------------------------------------------
-- reg_ts register and its interface

gen_reg_ts_we: for i in 7 downto 1 generate
   reg_ts_we(i) <= reg_ts_we_i or dc_out(7 - i);
end generate;

process (clk,RESET)
begin
   if (RESET = '1') then
      reg_ts <= (others => '0');
   elsif (clk'event and clk = '1') then
      for i in 8 downto 2 loop
         if (reg_ts_we(i-1) = '1') then
            reg_ts ((i*8)-1 downto (i-1)*8)
               <= reg_ts_load((i*8)-1 downto (i-1)*8);
         end if;
      end loop;
      reg_ts (7 downto 0) <= reg_ts_pipe;
   end if;
end process;

with ts_reg_mx select
reg_ts_load <= adder_ts when '0',
               reg_ts_pipe & reg_ts_pipe & reg_ts_pipe & reg_ts_pipe &
               reg_ts_pipe & reg_ts_pipe & reg_ts_pipe when '1',
               (others => '0') when others;

-- -------------------------------------------------------------
-- adder_ts
adder_ts <= X"0000000000000"&cnt_ppfts + reg_ts(63 downto 8) + reg_ppfts_pipe;

-- -------------------------------------------------------------
-- dc_cnt_ts decoder

process (dc_en,cnt_ts)
begin
   dc_out <= (others => '0');
   for i in 0 to 6 loop
      if (cnt_ts = (conv_std_logic_vector(i,3))) then
         dc_out(i) <= dc_en;
      end if;
   end loop;
end process;

-- -------------------------------------------------------------
-- Counters

with cnt_ts select
cnt_ts_max <= '1' when "111",
              '0' when others;

process (clk,RESET)
begin
   if (RESET = '1') then
      cnt_ts <= (others => '0');
   elsif (clk'event and clk = '1') then
      if (cnt_ts_ce = '1') then
         cnt_ts <= cnt_ts + 1;
      end if;
   end if;
end process;

cnt_ppfts_ce <= cnt_ppfts_ce_i and reg_ppfts_pipe;
process (clk,RESET,cnt_ppfts_rst)
begin -- sync reset
   if (RESET = '1') then
      cnt_ppfts <= (others => '0');
   elsif (clk'event and clk = '1') then
      if (cnt_ppfts_rst = '1') then
         cnt_ppfts <= (others => '0');
      elsif (cnt_ppfts_ce = '1') then
         cnt_ppfts <= cnt_ppfts + 1;
      end if;
   end if;
end process;

-- -------------------------------------------------------------
-- Pipeline registers

process (RESET,clk)
begin
   if (RESET = '1') then
      reg_ppfts_pipe <= '0';
   elsif (clk'event and clk = '1') then
      reg_ppfts_pipe <= regiob_ppfts;
   end if;
end process;

process (RESET,clk)
begin
   if (RESET = '1') then
      reg_ts_pipe <= (others => '0');
   elsif (clk'event and clk = '1') then
      reg_ts_pipe <= regiob_ts;
   end if;
end process;

-- -------------------------------------------------------------
-- regiob registers

process (RESET,clk)
begin
   if (RESET = '1') then
      regiob_tsdv <= '0';
   elsif (clk'event and clk = '1') then
      regiob_tsdv <= TS_DV;
   end if;
end process;

process (RESET,clk)
begin
   if (RESET = '1') then
      regiob_ts <= (others => '0');
   elsif (clk'event and clk = '1') then
      regiob_ts <= TS;
   end if;
end process;

process (RESET,clk)
begin
   if (RESET = '1') then
      regiob_ppfts <= '0';
   elsif (clk'event and clk = '1') then
      regiob_ppfts <= PPFTS;
   end if;
end process;

TS_INIT <= regiob_tsinit;
process (RESET,clk)
begin
   if (RESET = '1') then
      regiob_tsinit <= '0';
   elsif (clk'event and clk = '1') then
      regiob_tsinit <= tsadd_init_sync;
   end if;
end process;

TS_SHORT <= regiob_tsshort;
process (RESET,clk)
begin
   if (RESET = '1') then
      regiob_tsshort <= '0';
   elsif (clk'event and clk = '1') then
      regiob_tsshort <= tsadd_short_sync;
   end if;
end process;

-- -------------------------------------------------------------
-- TSUADD FSM

cnt_ppfts_ce_i <= ts_store;
cnt_ts_ce      <= ts_store;
ts_reg_mx      <= ts_store;
dc_en          <= ts_store;
u_tsadd_fsm: tsuadd_fsm
   port map(
      CLK      => clk,
      RESET    => RESET,

      CNT_TS_MAX  => cnt_ts_max,
      TSADD_INIT  => tsadd_init_sync,
      TSADD_SHORT => tsadd_short_sync,
      TSPTM_DV    => regiob_tsdv,

      TSADD_DV    => tsadd_dv_sync,
      TS_WE_I     => reg_ts_we_i,
      CNT_PPFTS_RST  => cnt_ppfts_rst,
      TS_STORE    => ts_store
   );
-- -------------------------------------------------------------
-- REFCLK clock recieve

U_IBUF_REFCLK: IBUFG
   port map(
      I => REFCLK,
      O => refclk_i
      );

U_BUFG_REFCLK: BUFG
   port map(
      I => refclk_i,
      O => clk
      );

-- -------------------------------------------------------------
-- Add-on card interface

u_tsadd_init: ASRQ2SYNC
   port map (
      RESET       => RESET,
      ASY_PE      => '1',
      ASY_CLK     => TSADD_INIT,
      SYNC_CLK    => clk,
      SYNC_PULS   => tsadd_init_sync
   );

u_tsadd_short: ASRQ2SYNC
   port map (
      RESET       => RESET,
      ASY_PE      => '1',
      ASY_CLK     => TSADD_SHORT,
      SYNC_CLK    => clk,
      SYNC_PULS   => tsadd_short_sync
   );

u_tsadd_dv: AD2SD
   generic map(
      DATA_WIDTH  => 1
   )
   port map (
      -- Input
      RESET       => RESET,
      ASYNC_CLK   => clk,
      SYNC_CLK    => CLK_ADD,
      ASYNC_DATA(0)  => tsadd_dv_sync,

      -- Output
      SYNC_DATA(0)   => TSADD_DV
   );

u_tsadd: AD2SD
   generic map(
      DATA_WIDTH  => 64
   )
   port map (
      -- Input
      RESET       => RESET,
      ASYNC_CLK   => clk,
      SYNC_CLK    => CLK_ADD,
      ASYNC_DATA  => reg_ts,

      -- Output
      SYNC_DATA   => TS_ADD
   );

end behavioral;

