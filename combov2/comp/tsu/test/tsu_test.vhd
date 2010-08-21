
-- tsu2pci.vhd: tsu connection to PCI for debuging purposes
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

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
-- Address space:
-- --------------
-- 0000: Read low TS register
-- 0004: Read high TS register
-- 0008: Request TS_INIT operation
-- 000C: Request TS_SHORT operation
-- 0010: Read low fast-timestamp
-- 0014: Read high fast-timestamp

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity tsu_test is
   generic(
      ADDR_BASE   : integer
   );
   port (
     -- Input from Add on Card
     RESET        : in std_logic; -- Reset form Add on
     CLK_ADD      : in std_logic; -- Clock from Add on
     -- Input from PTM card
     TS_DV        : in std_logic;
     -- Output to TSU_ADD
     TSADD_INIT   : out std_logic; -- TS init request from Add on Card
     TSADD_SHORT  : out std_logic; -- Short TS request from Add on Card
     -- Input from TSU_ADD
     TSADD_DV     : in std_logic; -- Data valid on TS_ADD
     TS_ADD       : in std_logic_vector (63 downto 0); -- TS output

     -- Internal bus signals
     LBCLK	     : in    std_logic;
     LBFRAME	  : in    std_logic;
     LBHOLDA	  : out   std_logic;
     LBAD	     : inout std_logic_vector(15 downto 0);
     LBAS	     : in    std_logic;
     LBRW	     : in    std_logic;
     LBRDY	     : out   std_logic;
     LBLAST	     : in    std_logic
   );
end tsu_test;

-- -------------------------------------------------------------
--       Architecture :
-- -------------------------------------------------------------
architecture behavioral of tsu_test is

component lbconn_mem is
   Generic ( BASE       : integer := 16#0010000#; -- Base address (28 bit)
             ADDR_WIDTH : integer := 24;          -- Width of address, max. 28
             USE_HIGH_LOGIC : boolean := FALSE    -- Set TRUE for Spartan3 only
           );
   Port (
      DATA_OUT : out std_logic_vector(15 downto 0);  -- Data output
      DATA_IN  : in std_logic_vector(15 downto 0);   -- Data input
      ADDR     : out std_logic_vector(ADDR_WIDTH-1 downto 0); -- Address output
      RW       : out std_logic;                      -- Write/Read#
      EN       : out std_logic;                      -- Data Enable
      SEL      : out std_logic;                      -- Select
      DRDY     : in std_logic;                       -- Data ready input
      ARDY     : in std_logic;                       -- Address Ready (ACK)
      -- local bus interconnection
      RESET   : IN std_logic;
      LBCLK   : IN std_logic;
      LBFRAME : IN std_logic;
      LBAS    : IN std_logic;
      LBRW    : IN std_logic;
      LBLAST  : IN std_logic;
      LBAD    : INOUT std_logic_vector(15 downto 0);
      LBHOLDA : OUT std_logic;
      LBRDY   : OUT std_logic
      );
end component lbconn_mem;

constant ADDR_WIDTH   : integer := 4;           -- range 0000...000f

-- registers
signal reg_ts        : std_logic_vector(63 downto 0); -- <= ts_add when ts_dv = '1'
signal reg_ts_f      : std_logic_vector(63 downto 0); -- <= ts_add
signal reg_tsinit    : std_logic;
signal reg_tsinit_we : std_logic;
signal reg_tsshort   : std_logic;
signal reg_tsshort_we: std_logic;

-- local bus signals
signal data_from_lb  : std_logic_vector(15 downto 0);
signal data_to_lb    : std_logic_vector(15 downto 0);
signal data_to_lb_mx : std_logic_vector(15 downto 0);
signal reg_data_to_lb: std_logic_vector(15 downto 0);
signal en_lb         : std_logic;
signal rw_lb         : std_logic;
signal addr_lb       : std_logic_vector(ADDR_WIDTH-1 downto 0);


begin

-- -------------------------------------------------------------
-- Registers to drive TSU_ADD component
process(CLK_ADD,RESET)
begin
   if (RESET = '1') then
      reg_ts <= (others => '0');
   elsif (CLK_ADD'event and CLK_ADD = '1') then
      if (TSADD_DV = '1') then
         reg_ts <= TS_ADD;
      end if;
   end if;
end process;

process(CLK_ADD,RESET)
begin -- clk_add & lbclk may be asynchronous -> reg_ts_f may be wrong!
   if (RESET = '1') then
      reg_ts_f <= (others => '0');
   elsif (CLK_ADD'event and CLK_ADD = '1') then
      if (en_lb = '0' or rw_lb = '1') then
         reg_ts_f <= TS_ADD;
      end if;
   end if;
end process;

TSADD_INIT <= reg_tsinit;
process(LBCLK,RESET,TS_DV)
begin
   if (RESET = '1') then
      reg_tsinit <= '0';
   elsif (LBCLK'event and LBCLK = '1') then
      if (TS_DV = '1') then
         reg_tsinit <= '0';
      elsif (reg_tsinit_we = '1') then
         reg_tsinit <= data_from_lb(0);
      end if;
   end if;
end process;

TSADD_SHORT <= reg_tsshort;
process(LBCLK,RESET,TS_DV)
begin
   if (RESET = '1') then
      reg_tsshort <= '0';
   elsif (LBCLK'event and LBCLK = '1') then
      if (TS_DV = '1') then
         reg_tsshort <= '0';
      elsif (reg_tsshort_we = '1') then
         reg_tsshort <= data_from_lb(0);
      end if;
   end if;
end process;

-- -------------------------------------------------------------
-- Local Bus Address Decoder
adclb: process (addr_lb,reg_ts,en_lb,rw_lb,reg_tsinit,reg_tsshort)
begin
   data_to_lb_mx <= (others => '0');
   reg_tsinit_we <= '0';
   reg_tsshort_we <= '0';

   case addr_lb is
   -- - - - - - - - - - - - - - - - - - - - -
   when X"0" =>
      data_to_lb_mx <= reg_ts(15 downto 0);
   -- - - - - - - - - - - - - - - - - - - - -
   when X"1" =>
      data_to_lb_mx <= reg_ts(31 downto 16);
   -- - - - - - - - - - - - - - - - - - - - -
   when X"2" =>
      data_to_lb_mx <= reg_ts(47 downto 32);
   -- - - - - - - - - - - - - - - - - - - - -
   when X"3" =>
      data_to_lb_mx <= reg_ts(63 downto 48);
   -- - - - - - - - - - - - - - - - - - - - -
   when X"4" =>
      reg_tsinit_we <= en_lb and rw_lb;
      data_to_lb_mx(0) <= reg_tsinit;
   -- - - - - - - - - - - - - - - - - - - - -
   when X"6" =>
      reg_tsshort_we <= en_lb and rw_lb;
      data_to_lb_mx(0) <= reg_tsshort;
   -- - - - - - - - - - - - - - - - - - - - -
   when X"8" =>
      data_to_lb_mx <= reg_ts_f(15 downto 0);
   -- - - - - - - - - - - - - - - - - - - - -
   when X"9" =>
      data_to_lb_mx <= reg_ts_f(31 downto 16);
   -- - - - - - - - - - - - - - - - - - - - -
   when X"A" =>
      data_to_lb_mx <= reg_ts_f(47 downto 32);
   -- - - - - - - - - - - - - - - - - - - - -
   when X"B" =>
      data_to_lb_mx <= reg_ts_f(63 downto 48);
   -- - - - - - - - - - - - - - - - - - - - -
--   when X"8" =>
--      data_to_lb_mx <= x"0123";
--   -- - - - - - - - - - - - - - - - - - - - -
--   when X"9" =>
--      data_to_lb_mx <= X"4567";
--   -- - - - - - - - - - - - - - - - - - - - -
--   when X"A" =>
--      data_to_lb_mx <= x"89ab";
--   -- - - - - - - - - - - - - - - - - - - - -
--   when X"B" =>
--      data_to_lb_mx <= x"cdef";
--   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   end case;
end process;

-- -------------------------------------------------------------
-- data_to_lb register

data_to_lb <= reg_data_to_lb;
process(LBCLK,RESET)
begin
   if (RESET = '1') then
      reg_data_to_lb <= (others => '0');
   elsif (LBCLK'event and LBCLK = '1') then
      reg_data_to_lb <= data_to_lb_mx;
   end if;
end process;

-- -------------------------------------------------------------
-- LBCONNMEM instantiation

u_lbconn : lbconn_mem
generic map(
   ADDR_WIDTH     => ADDR_WIDTH, -- address bus width
   BASE           => ADDR_BASE,  -- base address
   USE_HIGH_LOGIC => FALSE
)
port map(
   data_out => data_from_lb,
   data_in  => data_to_lb,
   addr     => addr_lb,
   en       => en_lb,
   rw       => rw_lb,
   sel      => open,
   drdy     => '1',
   ardy     => '1',
   reset    => RESET,
   LBCLK    => LBCLK,
   LBFRAME  => LBFRAME,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBLAST   => LBLAST,
   LBAD     => LBAD,
   LBHOLDA  => LBHOLDA,
   LBRDY    => LBRDY
);

end behavioral;


