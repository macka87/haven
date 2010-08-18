-- top_level.vhd: Top Level for SFPRO card
-- Copyright (C) 2003 CESNET
-- Author(s): Tomas Filip  <flipflop@liberouter.org>
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--pragma translate_off
library unisim;
use unisim.vcomponents.all;
--pragma translate_on

use work.ifc_addr_space.all;
use work.ifc_constants.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture sfp_arch of sfpro is

constant ID_SW_MAJOR     : std_logic_vector( 7 downto 0):=   X"00";
constant ID_SW_MINOR     : std_logic_vector( 7 downto 0):=   X"01";
constant ID_HW_MAJOR     : std_logic_vector(15 downto 0):= X"0001";
constant ID_HW_MINOR     : std_logic_vector(15 downto 0):= X"0000"; 

constant LANES       : integer := 2;
constant DATA_PATHS  : integer := 8;

-- --------------------------- Clk generation -----------------------------
   component BUFG
      port ( I : in    std_logic; 
             O : out   std_logic);
   end component;
  
component IBUFGDS is
      port (
		I  : in  std_logic;
		IB : in  std_logic;
		O  : out std_logic
      );
end component;

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

-- -------------------- Local bus  - interface ----------------------
component LB_BRIDGE is
   Generic (
      IN_TRISTATES : boolean := true -- always leave TRUE for on-chip use
      -- when FALSE, doesn't use tristate drivers for LBHOLDA_IN and LBRDY_IN
   );
   Port (
      -- local bus interconnection
      RESET      : IN std_logic;
      LBCLK      : IN std_logic;

      -- Local bus input (to card interface - IOS bus)
      LBFRAME_IN : IN std_logic;
      LBAS_IN    : IN std_logic;
      LBRW_IN    : IN std_logic;
      LBLAST_IN  : IN std_logic;
      LBAD_IN    : INOUT std_logic_vector(15 downto 0);
      LBHOLDA_IN : OUT std_logic;
      LBRDY_IN   : OUT std_logic;
      -- Local bus output (to another card)
      LBFRAME_OUT: OUT std_logic;
      LBAS_OUT   : OUT std_logic;
      LBRW_OUT   : OUT std_logic;
      LBLAST_OUT : OUT std_logic;
      LBAD_OUT   : INOUT std_logic_vector(15 downto 0);
      LBHOLDA_OUT: IN std_logic;
      LBRDY_OUT  : IN std_logic
   );
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

-- -------------------------- AURFC_TEST ---------------------------------
component aurvc_test is
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


-- *****************************   End of Components parts   *******************************************
-- *****************************************************************************************************

 -- Global Signals....

   signal ios_lbclk           : std_logic;
   signal ios_reset           : std_logic;
   signal reset               : std_logic;
   signal clk50               : std_logic;
   signal rioclk              : std_logic;
   signal rioclk2             : std_logic;

--   signal clk_base            : std_logic;
--   signal clk_dv              : std_logic;
--   signal clk_dv_ph           : std_logic;
   signal clkgen_lock            : std_logic;
   signal lock_rio              : std_logic;
   signal lock_lb                : std_logic;


 -- Local bus
   signal lbframe             : std_logic;
   signal lbas                : std_logic;
   signal lbrw                : std_logic;
   signal lblast              : std_logic;
   signal lbad                : std_logic_vector(15 downto 0);
   signal lbholda             : std_logic;
   signal lbrdy               : std_logic;
   signal lbclk               : std_logic;

   signal regiob_dummy_xled : std_logic_vector(3 downto 0);

   signal refclk_bufg : std_logic;

begin

-- ----------------------- Clk gen. component -------------------------
CLK_GEN_U : CLK_GEN
port map (
      -- Input
   CLK               => ios_lbclk,
   RESET             => ios_reset,
      -- Output
   CLK2X             => open,
   CLK1X             => lbclk,
   LOCK              => lock_lb
);


CLK_GEN_RIO_U: clkgen_rio
port map( 
   CLKIN           => FCLK,   -- 125MHz input clock
   RESET           => ios_reset,
   USRCLK          => rioclk, 
   USRCLK2         => rioclk2,
   LOCKED          => lock_rio
);

clkgen_lock <= lock_lb and lock_rio;
-- ----------------------- RIO clock buffer ------------------------------------
--IBUF_ETHCLK: IBUFGDS
--port map (
--   I  => ETHCLKP,  -- P-Channel input to LVDS buffer
--   IB => ETHCLKN,  -- N-Channel input to LVDS buffer
--   O  => rioclk   -- Output of LVDS buffer (input to FPGA fabric)= DDR data_in
--);

-- ---------------------- Local bus interface -----------------------------
IOS_TO_LB : LB_BRIDGE
generic map (
   IN_TRISTATES => false  -- Disable tristates on LBRDY_IN and LBHOLDA_IN
)
 port map (
    RESET       => reset,
    LBCLK       => lbclk,
    -- Local bus input (to local_bus driver)
   LBFRAME_IN => IOS(76),
   LBAS_IN    => IOS(77),
   LBRW_IN    => IOS(78),
   LBLAST_IN  => IOS(80),
   LBAD_IN(15 downto 13) => IOS(102 downto 100),
   LBAD_IN(12 downto  4) => IOS(98 downto 90),
   LBAD_IN( 3 downto  1) => IOS(88 downto 86),
   LBAD_IN(0)            => IOS(84),
   LBHOLDA_IN => IOS(82),
   LBRDY_IN   => IOS(81),
    -- Local bus extendet output (to components)
    LBFRAME_OUT => lbframe,
    LBAS_OUT    => lbas,
    LBRW_OUT    => lbrw,
    LBLAST_OUT  => lblast,
    LBAD_OUT    => lbad,
    LBHOLDA_OUT => lbholda,
    LBRDY_OUT   => lbrdy
);

-- --------------------------- ID component -------------------------------
ID_COMP_LB_U: ID_COMP_LB
   generic map (
      BASE         => ID_BASE_ADDR,
      PROJECT_ID   => ID_XFP_TEST, 
      SW_MAJOR     => ID_SW_MAJOR,
      SW_MINOR     => ID_SW_MINOR,
      HW_MAJOR     => ID_HW_MAJOR,
      HW_MINOR     => ID_HW_MINOR,
      PROJECT_TEXT => ID_XFP_TEST_TEXT 
   )
   port map (
      RESET    => reset,
      
      LBCLK    => lbclk,  -- internal bus clock, up to 100 MHz
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
   port map (I=>FCLK,
             O=>refclk_bufg);
   
lanes1_gen: if (LANES = 1) generate
aurvc_test_u: aurvc_test
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
      CMDCLK   => lbclk,
      
      -- MGT Interface
      RXN(0)            => RXN0,
      RXP(0)            => RXP0,
      TXN(0)            => TXN0,
      TXP(0)            => TXP0,
      
      -- Local Bus Interface
      LBCLK     => lbclk,
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
aurvc_test_u: aurvc_test
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
      CMDCLK   => lbclk,
      
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
      LBCLK     => lbclk,
      LBFRAME   => lbframe,
      LBHOLDA   => lbholda,
      LBAD      => lbad,
      LBAS      => lbas,
      LBRW      => lbrw,
      LBRDY     => lbrdy,
      LBLAST    => lblast
   );
end generate;

-- ----------------------------------------------------------------------------
-- Fake solution : we need to have at least one *regiob* register in design
-- to pass compilation of design (IOB attributes settings). LED outputs are
-- used for this purpose. LRESET signal and clkgen_lock signal are used as
-- inputs for LEDs.
-- Solution by Tomas Pecenka,thanks
regiob_dummy_xledp: process(clk50)
begin
   if (clk50'event AND clk50 = '1') then
      regiob_dummy_xled <= reset & clkgen_lock & reset & clkgen_lock;
   end if;
end process;
-- ----------------------------------------------------------------------------

ios_lbclk    <= IOS(79);
ios_reset    <= IOS(20);

reset       <= not clkgen_lock or ios_reset;

end architecture sfp_arch;
