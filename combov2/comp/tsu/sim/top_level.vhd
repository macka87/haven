
-- top_level.vhd: TSU top level entity for func. simulation
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
--       Entity :
-- -------------------------------------------------------------

entity TSU is
   port (
      -- CLK:
      REFCLK         : inout std_logic;
      CLK_ADD        : inout std_logic;
      -- Add-on card
      TSADD_INIT     : in std_logic;
      TSADD_SHORT    : in std_logic;
      TSADD_DV       : out std_logic;
      TS_ADD         : out std_logic_vector(63 downto 0);
      -- PLX:
      LCLKF    : inout  std_logic; -- LB clock
      LAD      : inout std_logic_vector(31 downto 0);
      LHOLDA   : inout std_logic;
      ADS      : inout    std_logic;
      BLAST    : inout    std_logic;
      LWR      : inout    std_logic;
      READY    : inout std_logic;
      LHOLD    : inout    std_logic;
      LRESET   : inout    std_logic;
      USERO    : inout    std_logic;
      -- MCU:
      SD       : inout std_logic_vector(7 downto 0);
      MCU      : inout std_logic_vector(7 downto 0);
      -- GPS
      RXD_PPS  : inout std_logic;
      TXD_PPS  : inout std_logic
   );
end TSU;

-- -------------------------------------------------------------
--          Architecture :
-- -------------------------------------------------------------
architecture test of TSU is

   -- reset signal
   signal reset         : std_logic;

   -- TSU_ADD <-> TSU_PTM signals
   signal ptmclk        : std_logic;
   signal ts_dv         : std_logic;
   signal ts            : std_logic_vector(7 downto 0);
   signal ts_init       : std_logic;
   signal ts_short      : std_logic;
   signal ppfts         : std_logic;

   -- ior cable
   signal ior           : std_logic_vector(43 downto 28);

begin
reset <= not LRESET;

-- TSU_PTM
u_tsu_ptm: entity work.ptm
   port map (
      -- CLK:
      REFCLK  => REFCLK,
      -- PLX:
      LCLKF   => LCLKF,
      LAD     => LAD,
      LHOLDA  => LHOLDA,
      ADS     => ADS,
      BLAST   => BLAST,
      LWR     => LWR,
      READY   => READY,
      LHOLD   => LHOLD,
      LRESET  => LRESET,
      USERO   => USERO,
      -- SYS:
      SD      => SD,
      MCU     => MCU,
      -- IO: (connect tri-state buffer from the other side)
      IOR     => ior,
      -- GPS
      RXD_PPS => RXD_PPS,
      TXD_PPS => TXD_PPS
   );

-- TSU_ADD
u_tsu_add: entity work.tsu_add
  port map (
     -- Input from PTM
     REFCLK	     => ptmclk,
     PPFTS	     => ppfts,
     TS_DV       => ts_dv,
     TS  	     => ts,
     -- Input from Add on Card
     RESET	     => reset,
     CLK_ADD	  => CLK_ADD,
     TSADD_INIT  => TSADD_INIT,
     TSADD_SHORT => TSADD_SHORT,
     -- Output to PTM
     TS_INIT     => ts_init,
     TS_SHORT	  => ts_short,
     -- Output to Add on Card
     TSADD_DV    => TSADD_DV,
     TS_ADD	     => TS_ADD
   );

-- -------------------------------------------------------------
-- IOR port mapping
ptmclk <= ior(28);
ior(30) <= ts_init;
ts_dv <= ior(31);
ts(0) <= ior(32);
ts(2) <= ior(33);
ts(4) <= ior(34);
ts(6) <= ior(35);
ior(36) <= ts_short;
ppfts <= ior(38);
ts(1) <= ior(40);
ts(3) <= ior(41);
ts(5) <= ior(42);
ts(7) <= ior(43);

-- -------------------------------------------------------------
-- Unused ports connection to avoid ModelSIM U values

CLK_ADD <= 'Z';

end test;
