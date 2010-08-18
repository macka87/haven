
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
--       Architecture :
-- -------------------------------------------------------------
architecture behavioral of FPGA is

component CLK_GEN is
   Port (
      -- Input
      CLK50_IN    : in  std_logic;     -- Input clock freqvency (50MHz)
      RESET       : in  std_logic;     -- Global reset signal
      -- Output
      CLK50_OUT   : out std_logic;  -- 50MHz  output clock
      CLK50_PH    : out std_logic;  -- 50MHz  output clock (shifted)
      CLK25       : out std_logic;  -- 25MHz  output clock
      CLK25_PH    : out std_logic;  -- 25MHz  output clock
      CLK100      : out std_logic;  -- 100MHz output clock
      CLK200      : out std_logic;  -- 200MHz output clock
      LOCK        : out std_logic
   );
end component;

component local_bus is
    Generic (
       USE_HIGH_LOGIC : boolean := FALSE
    );
    Port (
        -- PLX section
      LAD    : inout std_logic_vector(31 downto 0);-- PLX mux. Addr/Data
      ADS    : in    std_logic;               -- Address strobe, active low
      BLAST  : in    std_logic;               -- Last transfer, active: Low
      LHOLD  : in    std_logic;               -- PLX requests, active: High
      LHOLDA : out   std_logic;               -- Hold acknowledge, active: High
      LWR    : in    std_logic;               -- Read/write, active: read: Low
      READY  : out   std_logic;               -- Data is ready, active: Low
      RESET  : in    std_logic;               -- Local Reset, Active: High
      LCLKF  : in    std_logic;               -- Local Clock
      USERo  : in    std_logic;               -- USERo = '1': prog. CPLD

      -- Internal bus signals
      LBCLK   : in    std_logic;              -- Internal bus clock, up to 100 MHz
      LBFRAME : out   std_logic;              -- Frame
      LBHOLDA : in    std_logic;              -- Hold Ack (HOLDA), active LOW
      LBAD    : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS    : out   std_logic;              -- Adress strobe
      LBRW    : out   std_logic;              -- Direction (Read/Write,low : read)
      LBRDY   : in    std_logic;              -- Ready, active LOW
      LBLAST  : out   std_logic;              -- Last word in burst transfer
      -- special
      SWQ_REQ   : in std_logic                -- SW queue request
    );

end component local_bus;

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

constant BASE_ADDR    : integer := 16#0000000#; --
constant ADDR_WIDTH   : integer := 4;           -- range 0000...000f

-- -------------------------------------------------------------
-- clock signals
signal plxclk        : std_logic;
signal nlreset       : std_logic;
signal dcm_lock      : std_logic;

-- -------------------------------------------------------------
-- tsu_add signals
signal refclk        : std_logic;
signal ppfts         : std_logic;
signal ts_dv         : std_logic;
signal ts            : std_logic_vector(7 downto 0);
signal reset         : std_logic;
signal clk_add       : std_logic;
signal tsadd_init    : std_logic;
signal tsadd_short   : std_logic;
signal ts_init       : std_logic;
signal ts_short      : std_logic;
signal tsadd_dv      : std_logic;
signal ts_add        : std_logic_vector(63 downto 0);

-- -------------------------------------------------------------
-- tsu2pci registers
signal reg_ts        : std_logic_vector(63 downto 0); -- <= ts_add when ts_dv = '1'
signal reg_ts_f      : std_logic_vector(63 downto 0); -- <= ts_add
signal reg_tsinit    : std_logic;
signal reg_tsinit_we : std_logic;
signal reg_tsshort   : std_logic;
signal reg_tsshort_we: std_logic;

-- -------------------------------------------------------------
-- local bus signals
signal data_from_lb  : std_logic_vector(15 downto 0);
signal data_to_lb    : std_logic_vector(15 downto 0);
signal data_to_lb_mx : std_logic_vector(15 downto 0);
signal reg_data_to_lb: std_logic_vector(15 downto 0);
signal lbclk         : std_logic;
signal en_lb         : std_logic;
signal rw_lb         : std_logic;
signal addr_lb       : std_logic_vector(ADDR_WIDTH-1 downto 0);

-- -------------------------------------------------------------
-- Local bus internal signals
signal lbframe    : std_logic;
signal lbholda    : std_logic;
signal lbad       : std_logic_vector(15 downto 0);
signal lbas       : std_logic;
signal lbrw       : std_logic;
signal lbrdy      : std_logic;
signal lblast     : std_logic;
signal swq_req    : std_logic;


begin
nlreset <= not LRESET;
reset <= not dcm_lock;
clk_add <= lbclk; -- should be 156 MHz

U_TSU_ADD: entity work.TSU_ADD
port map (
     -- Input from PTM
     REFCLK	      => refclk,
     PPFTS	      => ppfts,
     TS_DV        => ts_dv,
     TS  	      => ts,
     -- Input from Add on Card
     RESET	      => reset,
     CLK_ADD	   => clk_add,
     TSADD_INIT	=> tsadd_init,
     TSADD_SHORT  => tsadd_short,
     -- Output to PTM
     TS_INIT   	=> ts_init,
     TS_SHORT	   => ts_short,
     -- Output to Add on Card
     TSADD_DV     => tsadd_dv,
     TS_ADD	      => ts_add
);

-- -------------------------------------------------------------
-- Registers to drive TSU_ADD component
process(clk_add,reset)
begin
   if (reset = '1') then
      reg_ts <= (others => '0');
   elsif (clk_add'event and clk_add = '1') then
      if (tsadd_dv = '1') then
         reg_ts <= ts_add;
      end if;
   end if;
end process;

process(clk_add,reset)
begin -- clk_add & lbclk may be asynchronous -> reg_ts_f may be wrong!
   if (reset = '1') then
      reg_ts_f <= (others => '0');
   elsif (clk_add'event and clk_add = '1') then
      if (en_lb = '0' or rw_lb = '1') then
         reg_ts_f <= ts_add;
      end if;
   end if;
end process;

tsadd_init <= reg_tsinit;
process(lbclk,reset,ts_dv)
begin
   if (reset = '1' or ts_dv = '1') then
      reg_tsinit <= '0';
   elsif (lbclk'event and lbclk = '1') then
      if (reg_tsinit_we = '1') then
         reg_tsinit <= data_from_lb(0);
      end if;
   end if;
end process;

tsadd_short <= reg_tsshort;
process(lbclk,reset,ts_dv)
begin
   if (reset = '1' or ts_dv = '1') then
      reg_tsshort <= '0';
   elsif (lbclk'event and lbclk = '1') then
      if (reg_tsshort_we = '1') then
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
   when others =>
      null;
   end case;
end process;

-- -------------------------------------------------------------
-- data_to_lb register

data_to_lb <= reg_data_to_lb;
process(lbclk,reset)
begin
   if (reset = '1') then
      reg_data_to_lb <= (others => '0');
   elsif (lbclk'event and lbclk = '1') then
      reg_data_to_lb <= data_to_lb_mx;
   end if;
end process;

-- -------------------------------------------------------------
-- Local bus instantiation

u_local_bus: local_bus
generic map (
     USE_HIGH_LOGIC => FALSE
   )
port map(
      lad     => LAD,
      ads     => ADS,
      blast   => BLAST,
      lhold   => LHOLD,
      lholda  => LHOLDA,
      lwr     => LWR,
      ready   => READY,
      reset   => reset,
      lclkf   => plxclk,
      usero   => USERO,
      lbclk   => lbclk,
      lbframe => lbframe,
      lbholda => lbholda,
      lbad    => lbad,
      lbas    => lbas,
      lbrw    => lbrw,
      lbrdy   => lbrdy,
      lblast  => lblast,
      swq_req => '0'
   );

-- -------------------------------------------------------------
-- LBCONNMEM instantiation

u_lbconn : lbconn_mem
generic map(
   ADDR_WIDTH     => ADDR_WIDTH, -- address bus width
   BASE           => BASE_ADDR,  -- base address
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
   reset    => reset,
   LBCLK    => lbclk,
   LBFRAME  => LBFRAME,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBLAST   => LBLAST,
   LBAD     => LBAD,
   LBHOLDA  => LBHOLDA,
   LBRDY    => LBRDY
);

-- -------------------------------------------------------------
-- CLK_GEN instantiation

U_CLK_GEN: CLK_GEN
   port map(
      -- Input
      CLK50_IN    => LCLKF,
      RESET       => nlreset,
      -- Output
      CLK50_OUT   => plxclk,
      CLK100      => lbclk,
      LOCK        => dcm_lock
   );

-- -------------------------------------------------------------
-- Port mapping

refclk <= IO(28);
IO(30) <= ts_init;
ts_dv  <= IO(31);
ts(0)  <= IO(32);
ts(2)  <= IO(33);
ts(4)  <= IO(34);
ts(6)  <= IO(35);
IO(36) <= ts_short;
ppfts  <= IO(38);
ts(1)  <= IO(40);
ts(3)  <= IO(41);
ts(5)  <= IO(42);
ts(7)  <= IO(43);

-- -------------------------------------------------------------
-- Unused ports connection to avoid NGDBuild error and ModelSIM U values

      -- CLK:
      LCLKF     <= 'Z';
      -- LED:
      XLED      <= (others => 'Z');
      -- PLX:
      LBE       <= (others => 'Z');
      ALE       <= 'Z';
      DP        <= (others => 'Z');
      DEN       <= 'Z';
      DTR       <= 'Z';
      CCS       <= 'Z';
      LHOLDA    <= 'Z';
      BREQI     <= 'Z';
      ADS       <= 'Z';
      BLAST     <= 'Z';
      LWR       <= 'Z';
      READY     <= 'Z';
      WAITIO    <= 'Z';
      LHOLD     <= 'Z';
      LINT      <= 'Z';
      LRESET    <= 'Z';
      USERI     <= 'Z';
      LSERR     <= 'Z';
      EOT       <= 'Z';
      BIGEND    <= 'Z';
      USERO     <= 'Z';
      BTERM     <= 'Z';
      BREQO     <= 'Z';
      L_ONOFF   <= 'Z';
      -- CAM:
      CD        <= (others => 'Z');
      COP       <= (others => 'Z');
      COPV      <= 'Z';
      CACK      <= 'Z';
      CEOT      <= 'Z';
      CMF       <= 'Z';
      CMM       <= 'Z';
      CMV       <= 'Z';
      CFF       <= 'Z';
      CPHASE    <= 'Z';
      CRST      <= 'Z';
      CSEN      <= (others => 'Z');
      CMCLK     <= 'Z';
      -- SRAM0:
      S0D       <= (others => 'Z');
      S0A       <= (others => 'Z');
      S0ADSP    <= 'Z';
      S0ADSC    <= 'Z';
      S0ADV     <= 'Z';
      S0CS1     <= 'Z';
      S0CS2     <= 'Z';
      S0GW      <= 'Z';
      S0BW      <= 'Z';
      S0WE      <= (others => 'Z');
      S0OE      <= 'Z';
      S0MODE    <= 'Z';
      SCLK0     <= 'Z';
      -- SRAM1:
      S1D       <= (others => 'Z');
      S1A       <= (others => 'Z');
      S1ADSP    <= 'Z';
      S1ADSC    <= 'Z';
      S1ADV     <= 'Z';
      S1CS1     <= 'Z';
      S1CS2     <= 'Z';
      S1GW      <= 'Z';
      S1BW      <= 'Z';
      S1WE      <= (others => 'Z');
      S1OE      <= 'Z';
      S1MODE    <= 'Z';
      SCLK1     <= 'Z';
      -- SRAM2:
      S2D       <= (others => 'Z');
      S2A       <= (others => 'Z');
      S2ADSP    <= 'Z';
      S2ADSC    <= 'Z';
      S2ADV     <= 'Z';
      S2CS1     <= 'Z';
      S2CS2     <= 'Z';
      S2GW      <= 'Z';
      S2BW      <= 'Z';
      S2WE      <= (others => 'Z');
      S2OE      <= 'Z';
      S2MODE    <= 'Z';
      SCLK2     <= 'Z';
      -- SDRAM:
      DD        <= (others => 'Z');
      DCB       <= (others => 'Z');
      DQS       <= (others => 'Z');
      DA        <= (others => 'Z');
      DBA       <= (others => 'Z');
      DCS       <= (others => 'Z');
      DCLKE     <= (others => 'Z');
      DCAS      <= 'Z';
      DRAS      <= 'Z';
      DWE       <= 'Z';
      DCLK      <= 'Z';
      NDCLK     <= 'Z';
      -- IO:
      IOS               <= (others => 'Z');
      IO(51 downto 44)  <= (others => 'Z');
      IO(43 downto 39)  <= (others => 'Z');
      IO(38 downto 37)  <= (others => 'Z');
      IO(35 downto 31)  <= (others => 'Z');
      IO(29)            <= 'Z';
      IO(28)            <= 'Z';
      IO(27 downto 0)   <= (others => 'Z');
      -- FPGA:
      FSINIT    <= 'Z';
      SD        <= (others => 'Z');
      FSBUSY    <= 'Z';
      FSCS      <= 'Z';
      FSWR      <= 'Z';
end behavioral;


