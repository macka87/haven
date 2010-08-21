-- c6x_top.vhd : Combo6X top level architecture
--
-- Copyright (C) 2006 CESNET
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
-- TODO list :
--
-- ---------------------------------------------------------------------------
--                          Entity declaration
-- ---------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.c6x_addr_space.all;
use work.c6x_constants.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on
use work.math_pack.all;


-- ------------------------------------------------------------------------
--                       Architecture declaration
-- ------------------------------------------------------------------------
architecture behavioral of fpga_u5 is

-- ------------------------ Constants definition --------------------------
-- Design identification
constant ID_SW_MAJOR     : std_logic_vector( 7 downto 0):=   X"00";
constant ID_SW_MINOR     : std_logic_vector( 7 downto 0):=   X"01";
constant ID_HW_MAJOR     : std_logic_vector(15 downto 0):= X"0001";
constant ID_HW_MINOR     : std_logic_vector(15 downto 0):= X"0000"; 

constant LANES       : integer := 2;
constant DATA_PATHS  : integer := 8;

component IBUFGDS is
      port (
		I  : in  std_logic;
		IB : in  std_logic;
		O  : out std_logic
      );
end component;

   component BUFG
      port ( I : in    std_logic; 
             O : out   std_logic);
   end component;
  
-- --------------------------- ID component -------------------------------
component ID_COMP_LB is
   generic (
      BASE           : integer := 0;
      USE_HIGH_LOGIC : boolean := false;
   
      PROJECT_ID     : std_logic_vector(15 downto 0):= X"0000";
      SW_MAJOR       : std_logic_vector( 7 downto 0):=   X"00";
      SW_MINOR       : std_logic_vector( 7 downto 0):=   X"00";
      HW_MAJOR       : std_logic_vector(15 downto 0):= X"0000";
      HW_MINOR       : std_logic_vector(15 downto 0):= X"0000";
      PROJECT_TEXT   : std_logic_vector(255 downto 0) :=
      X"0000000000000000000000000000000000000000000000000000000000000000"
   ); 
   port (
      RESET    : in std_logic;
      
      LBCLK     : in    std_logic;  -- internal bus clock, up to 100 MHz
      LBFRAME   : in    std_logic;  -- Frame
      LBHOLDA   : out   std_logic;  -- Hold Ack
      LBAD      : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS      : in    std_logic;  -- Adress strobe
      LBRW      : in    std_logic;  -- Direction (Read#/Write, low : read)
      LBRDY     : out   std_logic;  -- Ready
      LBLAST    : in    std_logic   -- Last word in transfer
);
end component ID_COMP_LB;

-- --------------------------- Clk generation -----------------------------
component CLK_GEN is
   Port (
      -- Input
      CLK         : in  std_logic;  -- Input clock frequency
      RESET       : in  std_logic;  -- Global reset signal
      -- Output
      CLK1X       : out std_logic;  -- 1X output clock
      CLK2X       : out std_logic;  -- 2X output clock
      LOCK        : out std_logic   -- Lock signal
   );
end component CLK_GEN;

component clkgen_rio
   port ( CLKIN          : in    std_logic;     -- Input clock (125 MHz)
          RESET          : in    std_logic; 
          USRCLK         : out   std_logic; 
          USRCLK2        : out   std_logic; 
          LOCKED         : out   std_logic
          );
end component;

-- ---------------------- Internal bus & address decoder -------------------

component LOCAL_BUS is
    Port (
        -- PLX section
      LAD    : inout std_logic_vector(31 downto 0);-- PLX mux. Addr/Data
      ADS    : in    std_logic;    -- Address strobe, active low
      BLAST  : in    std_logic;    -- Last transfer, active: Low
      LHOLD  : in    std_logic;    -- PLX requests, active: High
      LHOLDA : out   std_logic;    -- Hold acknowledge, active: High
      LWR    : in    std_logic;    -- Read/write, active: read: Low
      READY  : out   std_logic;    -- Data is ready, active: Low
      LRESET : in    std_logic;    -- Local Reset, Active: High
      LCLKF  : in    std_logic;    -- Local Clock
      USERo  : in    std_logic;    -- USERo = '1': prog. CPLD

      -- Internal bus signals
      LBCLK   : in    std_logic;   -- Internal bus clock, up to 100 MHz
      LBFRAME : out   std_logic;   -- Frame
      LBHOLDA : in    std_logic;   -- Hold Ack (HOLDA), active LOW
      LBAD    : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS    : out   std_logic;   -- Adress strobe
      LBRW    : out   std_logic;   -- Direction (Read/Write,low : read)
      LBRDY   : in    std_logic;   -- Ready, active LOW
      LBLAST  : out   std_logic;   -- Last word in burst transfer
      -- special
      SWQ_REQ   : in std_logic     -- SW queue request
    );

end component LOCAL_BUS;

-- -------------------------- LB_BRIDGE ---------------------------------
component LB_BRIDGE is
   Port (
      -- local bus interconnection
      RESET   : IN std_logic;
      LBCLK   : IN std_logic;

      -- Local bus input (to local_bus driver)
      LBFRAME_IN : IN std_logic;
      LBAS_IN    : IN std_logic;
      LBRW_IN    : IN std_logic;
      LBLAST_IN  : IN std_logic;
      LBAD_IN    : INOUT std_logic_vector(15 downto 0);
      LBHOLDA_IN : OUT std_logic;
      LBRDY_IN   : OUT std_logic;

      -- Local bus extendet output (to components)
      LBFRAME_OUT: OUT std_logic;
      LBAS_OUT   : OUT std_logic;
      LBRW_OUT   : OUT std_logic;
      LBLAST_OUT : OUT std_logic;
      LBAD_OUT   : INOUT std_logic_vector(15 downto 0);
      LBHOLDA_OUT: IN std_logic;
      LBRDY_OUT  : IN std_logic

      );
end component LB_BRIDGE;

-- -------------------------- AURFC_TEST ---------------------------------
component aurfc_test is
   generic (
      BASE_ADDR         : integer := 0;
      
      LANES             : integer;                 -- Number of lanes 
      DATA_PATHS        : integer;                 -- Number of data paths
      
      LOOPBACK : std_logic_vector := "00"
      );
   port (
      RESET    : in std_logic;
      REFCLK   : in std_logic;
      USRCLK  : in std_logic;
      USRCLK2 : in std_logic;
      CMDCLK   : in std_logic;
      
      -- MGT Interface
      RXN            : in  std_logic_vector(LANES-1 downto 0);
      RXP            : in  std_logic_vector(LANES-1 downto 0);
      TXN            : out std_logic_vector(LANES-1 downto 0);
      TXP            : out std_logic_vector(LANES-1 downto 0);
      
      -- Local Bus Interface
      LBCLK     : in    std_logic;  -- internal bus clock, up to 100 MHz
      LBFRAME   : in    std_logic;  -- Frame
      LBHOLDA   : out   std_logic;  -- Hold Ack
      LBAD      : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS      : in    std_logic;  -- Adress strobe
      LBRW      : in    std_logic;  -- Direction (Read#/Write, low : read)
      LBRDY     : out   std_logic;  -- Ready
      LBLAST    : in    std_logic   -- Last word in transfer
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
-- ------------------------------------------------------------------
--                      Signal declaration
-- ------------------------------------------------------------------

-- Resets
signal rst        : std_logic;
signal rst_n      : std_logic := '0';
signal reset      : std_logic;
signal cntr       : std_logic_vector(24 downto 0) := (others => '0');
signal refclk_bufg : std_logic;

-- Clocks
signal clk50      : std_logic;
signal clk100     : std_logic;
signal clk100_n   : std_logic;
signal rioclk     : std_logic;
signal rioclk2    : std_logic;
signal lock       : std_logic;
signal lock_100   : std_logic;
signal lock_rio   : std_logic;

-- Internal bus signals
signal lbframe    : std_logic;  -- Frame
signal lbholda    : std_logic;  -- Hold Ack
signal lbad       : std_logic_vector(15 downto 0); -- Address/Data
signal lbas       : std_logic;  -- Adress strobe
signal lbrw       : std_logic;  -- Direction (Read#/Write, low : read)
signal lbrdy      : std_logic;  -- Ready
signal lblast     : std_logic;  -- Last word in transfer

signal cnt_led    : std_logic_vector(29 downto 0); -- XLED counter 

-- one register must have name regiob/regnoiob to pass the simulation
signal regiob_dummy   : std_logic;
signal regnoiob_dummy : std_logic;

-- PLX signal names aliases
alias LAD0   : std_logic_vector(26 downto  0) is X(26 downto  0);
alias LAD1   : std_logic_vector(31 downto 27) is X(32 downto 28);
alias LHOLD  : std_logic                      is X(34);
alias LWR    : std_logic                      is X(35);
alias READY  : std_logic                      is X(36);
alias BLAST  : std_logic                      is X(37);
alias ADS    : std_logic                      is X(38);

-- ------------------------------------------------------------------
--                       Architecture body
-- ------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   -- We don't have any RESET signal on Combo6X card, so we use this counter to
   -- generate one. Assume flip-flops have '0' value after FPGA boot by default.
   -- -------------------------------------------------------------------------
   GEN_RESET: process(LCLKF)
   begin
      if LCLKF = '1' and LCLKF'event then
         cntr <= cntr + 1;
         if (rst_n = '0') and (cntr(5)) = '1' then
            rst_n <= '1';
         end if;
      end if;
   end process;
   rst   <= not rst_n;
   reset <= rst or (not lock);

-- -------------------------------------------------------------------------
-- Generate clocks - local bus clock LBCLK and system clock CLK.
-- -------------------------------------------------------------------------
CLK_GEN_U : CLK_GEN
port map (
   -- Input
   CLK      => LCLKF,  -- Input clock frequency (50MHz)
   RESET    => rst,    -- Global reset signal
   -- Output
   CLK1X    => clk50,  -- 50MHz  output clock
   CLK2X    => clk100, -- 100MHz output clock
   LOCK     => lock_100   -- Lock signal
);

CLK_GEN_RIO_U: clkgen_rio
port map( 
   CLKIN           => CLKF,   -- 125MHz input clock
   RESET           => rst,
   USRCLK          => rioclk, 
   USRCLK2         => rioclk2,
   LOCKED          => lock_rio
);

lock <= lock_100 and lock_rio;

-- ----------------------- RIO clock buffer ------------------------------------
--IBUF_ETHCLK: IBUFGDS
--port map (
--   I  => LVDSFP,  -- P-Channel input to LVDS buffer
--   IB => LVDSFN,  -- N-Channel input to LVDS buffer
--   O  => rioclk   -- Output of LVDS buffer (input to FPGA fabric)= DDR data_in
--);

-- ----------------------- Internal bus ------------------------------------
LOCAL_BUS_U: entity work.LOCAL_BUS
port map (
   -- PLX interface
   LAD(31 downto 27) => LAD1,
   LAD(26 downto 0)  => LAD0,
   ADS          => ADS,       -- Address strobe
   BLAST        => BLAST,     -- Last transfer in the bus, active: Low
   LHOLD        => LHOLD,     -- PLX requests Local Bus, active: High
   LHOLDA       => open,      -- Hold acknowledge, active: High
   LWR          => LWR,       -- Local bus read/write, active: read: Low
   READY        => READY,     -- Data is ready, active: Low
   RESET        => reset,     -- Local Reset
   LCLKF        => clk50,     -- Local Clock
   USERo        => '0',     -- USERo = '1': used for prog. CPLD

   -- Internal bus signals
   LBCLK        => clk100,     -- internal bus clock, up to 100 MHz
   LBFRAME      => lbframe,   -- Frame
   LBHOLDA      => lbholda,   -- Hold Ack
   LBAD         => lbad,      -- Address/Data
   LBAS         => lbas,      -- Adress strobe
   LBRW         => lbrw,      -- Direction (Read#/Write, low : read)
   LBRDY        => lbrdy,     -- Ready
   LBLAST       => lblast,    -- Last word in transfer

   -- special
   SWQ_REQ      => '0'        -- SW queue request
);

---- --------------- Local Bus Bridge External (IOS)  ------------------------
IOS_LB_BRIDGE : LB_BRIDGE
port map (
   RESET       => reset,
   LBCLK       => clk100,

   LBFRAME_OUT => IOS(76),
   LBAS_OUT    => IOS(77),
   LBRW_OUT    => IOS(78),
   LBLAST_OUT  => IOS(80),
   LBAD_OUT(15 downto 13) => IOS(102 downto 100),
   LBAD_OUT(12 downto  4) => IOS(98 downto 90),
   LBAD_OUT( 3 downto  1) => IOS(88 downto 86),
   LBAD_OUT(0)            => IOS(84),
   LBHOLDA_OUT => IOS(82),
   LBRDY_OUT   => IOS(81),

   LBFRAME_IN  => lbframe,
   LBAS_IN     => lbas,
   LBRW_IN     => lbrw,
   LBLAST_IN   => lblast,
   LBAD_IN     => lbad,
   LBHOLDA_IN  => lbholda,
   LBRDY_IN    => lbrdy
);

-- --------------------------- ID component -------------------------------
ID_COMP_LB_U: ID_COMP_LB
   generic map (
      BASE         => ID_BASE_ADDR,
      PROJECT_ID   => ID_C6X_TEST, 
      SW_MAJOR     => ID_SW_MAJOR,
      SW_MINOR     => ID_SW_MINOR,
      HW_MAJOR     => ID_HW_MAJOR,
      HW_MINOR     => ID_HW_MINOR,
      PROJECT_TEXT => ID_C6X_TEST_TEXT 
   )
   port map (
      RESET    => reset,
      
      LBCLK    => clk100,  -- internal bus clock, up to 100 MHz
      LBFRAME  => lbframe, -- Frame
      LBHOLDA  => lbholda, -- Hold Ack
      LBAD     => lbad,    -- Address/Data
      LBAS     => lbas,    -- Adress strobe
      LBRW     => lbrw,    -- Direction (Read#/Write, low : read)
      LBRDY    => lbrdy,   -- Ready
      LBLAST   => lblast   -- Last word in transfer
); 

-- --------------------------- AURFC_test component -------------------------------
REFCLK_IBUFG_INST : BUFG
   port map (I=>CLKF,
             O=>refclk_bufg);
   
lanes1_gen: if (LANES = 1) generate
aurfc_test_u: aurfc_test
   generic map(
      BASE_ADDR         => AURFC_TEST_BASE_ADDR,
      LANES             => LANES,
      DATA_PATHS        => DATA_PATHS,
      LOOPBACK          => "00"
      )
   port map(
      RESET    => reset,
      REFCLK   => refclk_bufg,
      USRCLK   => rioclk,
      USRCLK2  => rioclk2,
      CMDCLK   => rioclk,
      
      -- MGT Interface
      RXN(0)            => RXN0,
      RXP(0)            => RXP0,
      TXN(0)            => TXN0,
      TXP(0)            => TXP0,
      
      -- Local Bus Interface
      LBCLK     => clk100,
      LBFRAME   => lbframe,
      LBHOLDA   => lbholda,
      LBAD      => lbad,
      LBAS      => lbas,
      LBRW      => lbrw,
      LBRDY     => lbrdy,
      LBLAST    => lblast
   );
end generate;

lanes2_gen: if (LANES = 2) generate
aurfc_test_u: aurfc_test
   generic map(
      BASE_ADDR         => AURFC_TEST_BASE_ADDR,
      LANES             => LANES,
      DATA_PATHS        => DATA_PATHS,
      LOOPBACK          => "00"
      )
   port map(
      RESET    => reset,
      REFCLK   => refclk_bufg,
      USRCLK   => rioclk,
      USRCLK2  => rioclk2,
      CMDCLK   => rioclk,
      
      -- MGT Interface
      RXN(0)            => RXN0,
      RXN(1)            => RXN1,
      RXP(0)            => RXP0,
      RXP(1)            => RXP1,
      TXN(0)            => TXN0,
      TXN(1)            => TXN1,
      TXP(0)            => TXP0,
      TXP(1)            => TXP1,
      
      -- Local Bus Interface
      LBCLK     => clk100,
      LBFRAME   => lbframe,
      LBHOLDA   => lbholda,
      LBAD      => lbad,
      LBAS      => lbas,
      LBRW      => lbrw,
      LBRDY     => lbrdy,
      LBLAST    => lblast
   );
end generate;

-- Local bus clock output to interface card

   clk100_n <= not clk100;
   LBCLK_OUT : FDDRRSE
   port map (
   -- clocks
      Q => IOS(79),
      D0 => '1',
      D1 => '0',
      C0 => clk100,
      C1 => clk100_n,
      CE => '1',
      R => '0',
      S => '0'
   );


-- ----------------------------------------------------------------------------
-- Fake solution : we need to have at least one *regiob* register in design
-- to pass compilation of design (IOB attributes settings). 
regiob_dummyp: process(clk50)
begin
   if (clk50'event AND clk50 = '1') then
      regiob_dummy   <= lock;
      regnoiob_dummy <= not lock;
   end if;
end process;
-- ----------------------------------------------------------------------------
IOS(20) <= reset;

-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
end architecture behavioral;

