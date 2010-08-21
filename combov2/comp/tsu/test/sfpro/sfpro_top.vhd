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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture sfp_arch of SFPRO is

constant ID_SW_MAJOR     : std_logic_vector( 7 downto 0):=   X"00";
constant ID_SW_MINOR     : std_logic_vector( 7 downto 0):=   X"01";
constant ID_HW_MAJOR     : std_logic_vector(15 downto 0):= X"0001";
constant ID_HW_MINOR     : std_logic_vector(15 downto 0):= X"0000"; 

-- --------------------------- Clk generation -----------------------------
-- Clock Buffer
component BUFG is
      port (
         I : in  std_logic;
         O : out std_logic
      );
end component;

component IBUFGDS is
      port (
		I  : in  std_logic;
		IB : in  std_logic;
		O  : out std_logic
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

-- --------------------------- TSU_ADD component -------------------------------
component TSU_ADD is
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
end component;

-- --------------------------- TSU_TEST component -------------------------------
component TSU_TEST is
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
     LBFRAME	     : in    std_logic;
     LBHOLDA	     : out   std_logic;
     LBAD	     : inout std_logic_vector(15 downto 0);
     LBAS	     : in    std_logic;
     LBRW	     : in    std_logic;
     LBRDY	     : out   std_logic;
     LBLAST	     : in    std_logic
   );
end component;

-- -------------------------- DCM ---------------------------------
component DCM
   -- pragma translate_off
   generic (
      DFS_FREQUENCY_MODE : string := "LOW";
      DLL_FREQUENCY_MODE : string := "LOW";
      DUTY_CYCLE_CORRECTION : boolean := TRUE;
      CLKFX_DIVIDE : integer := 1;
      CLKFX_MULTIPLY : integer := 4 ;
      STARTUP_WAIT : boolean := FALSE;
      CLKDV_DIVIDE : real := 2.0
   );
   -- pragma translate_on
port (
      CLKIN     : in  std_logic;
      CLKFB     : in  std_logic;
      RST       : in  std_logic;
      CLK0      : out std_logic;
      CLK90     : out std_logic;
      CLK180    : out std_logic;
      CLK2X     : out std_logic;
      CLK2X180  : out std_logic;
      CLKDV     : out std_logic;
      CLKFX     : out std_logic;
      CLKFX180  : out std_logic;
      LOCKED    : out std_logic;
      PSDONE    : out std_logic;
      STATUS    : out std_logic_vector(7 downto 0)
   );
end component;


 -- Global Signals....

   constant DATA_PATHS        : integer := 2;
   
   signal ios_lbclk           : std_logic;
   signal ios_reset           : std_logic;
   signal reset               : std_logic;
   signal clk50               : std_logic;
   signal ethclk              : std_logic;
   signal fclk0               : std_logic;
   signal fclk0_bufg          : std_logic;
   signal usr_clk             : std_logic;
   signal usr_clk_bufg        : std_logic;
   signal usr_clk2            : std_logic;
   signal usr_clk2_n          : std_logic;
   signal usr_clk2_bufg       : std_logic;

   signal clkgen_lock            : std_logic;
   signal lock_rio              : std_logic;
   signal lock_lb                : std_logic;

   -- TSU
   signal refclk        : std_logic;
   signal clk_add       : std_logic;
   signal ppfts         : std_logic;
   signal ts_dv         : std_logic;
   signal ts            : std_logic_vector(7 downto 0);
   signal tsadd_init    : std_logic;
   signal tsadd_short   : std_logic;
   signal ts_init       : std_logic;
   signal ts_short      : std_logic;
   signal tsadd_dv      : std_logic;
   signal ts_add        : std_logic_vector(63 downto 0);

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


clkgen_lock <= lock_lb and lock_rio;
IBUF_ETHCLK: IBUFGDS
port map (
   I  => ETHCLKP, -- P-Channel input to LVDS buffer
   IB => ETHCLKN, -- N-Channel input to LVDS buffer
   O  => ethclk   -- Output of LVDS buffer (input to FPGA fabric)= DDR data_in
);


-- DCM for RocketIO clocking
RIO_DCM : DCM
-- pragma translate_off
generic map (
   DLL_FREQUENCY_MODE    => "LOW",
   DUTY_CYCLE_CORRECTION => TRUE,
   STARTUP_WAIT          => FALSE,
   CLKDV_DIVIDE          => 2.0
)
-- pragma translate_on
port map (
   CLKIN     => ethclk, --FCLK,
   CLKFB     => fclk0,
   RST       => ios_reset,
   CLK0      => fclk0_bufg,
   CLK180    => usr_clk2_bufg,
   CLKDV     => usr_clk_bufg,
   LOCKED    => lock_rio
);

FCLK0_BUFG_INST   : BUFG port map (I => fclk0_bufg,    O => fclk0);
USRCLK_BUFG_INST  : BUFG port map (I => usr_clk_bufg,  O => usr_clk);
-- USRCLK2_BUFG_INST : BUFG port map (I => usr_clk2_bufg, O => usr_clk2);

-- usr_clk  <= fclk0;
usr_clk2 <= usr_clk;
usr_clk2_n  <= not fclk0;

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

-- --------------------------- TSU_ADD component -------------------------------
TSU_ADD_u: TSU_ADD
   port map(
     -- Input from PTM
     REFCLK       => refclk,
     PPFTS        => ppfts,
     TS_DV        => ts_dv,
     TS           => ts,
     -- Input from Add on Card
     RESET        => reset,
     CLK_ADD      => lbclk,
     TSADD_INIT   => tsadd_init,
     TSADD_SHORT  => tsadd_short,
     -- Output to PTM
     TS_INIT      => ts_init,
     TS_SHORT     => ts_short,
     -- Output to Add on Card
     TSADD_DV     => tsadd_dv,
     TS_ADD       => ts_add
   );

-- --------------------------- TSU_TEST component -------------------------------
tsu_test_u: tsu_test
   generic map(
      ADDR_BASE   => IFC_TEST1_BASE_ADDR
      )
   port map(
     -- Input from Add on Card
     RESET        => reset,
     CLK_ADD      => lbclk,
     -- Input from PTM card
     TS_DV        => ts_dv,
     -- Output to TSU_ADD
     TSADD_INIT   => tsadd_init,
     TSADD_SHORT  => tsadd_short,
     -- Input from TSU_ADD
     TSADD_DV     => tsadd_dv,
     TS_ADD       => ts_add,

     -- Internal bus signals
     LBCLK	     => lbclk,
     LBFRAME	     => lbframe,
     LBHOLDA	     => lbholda,
     LBAD	     => lbad,
     LBAS	     => lbas,
     LBRW	     => lbrw,
     LBRDY	     => lbrdy,
     LBLAST	     => lblast
   );

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

ios_lbclk    <= IOS(79);
ios_reset    <= IOS(20);

reset       <= not clkgen_lock or ios_reset;

-- -----------------------------------------------------------------------------
--                             Other interfaces
-- -----------------------------------------------------------------------------

TXDISA    <= '0';
MODDEFA   <= "ZZZ";
RSA       <= '0';

TXDISB    <= '0';
MODDEFB   <= "ZZZ";
RSB       <= '0';

TXDISC    <= '0';
MODDEFC   <= "ZZZ";
RSC       <= '0';

TXDISD    <= '0';
MODDEFD   <= "ZZZ";
RSD       <= '0';

end architecture sfp_arch;
