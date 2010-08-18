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

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture sfp_arch of sfpro is

constant ID_SW_MAJOR     : std_logic_vector( 7 downto 0):=   X"00";
constant ID_SW_MINOR     : std_logic_vector( 7 downto 0):=   X"01";
constant ID_HW_MAJOR     : std_logic_vector(15 downto 0):= X"0001";
constant ID_HW_MINOR     : std_logic_vector(15 downto 0):= X"0000"; 

-- --------------------------- Clk generation -----------------------------
component CLK_GEN is
  Port ( 
      -- Input
      CLK         : in  std_logic;  -- Input clock frequency
      RESET       : in  std_logic;  -- Global reset signal
      -- Output
      CLK1X       : out std_logic;  -- 1X output clock
      CLK2X       : out std_logic;  -- 2X output clock
      CLKDV       : out std_logic;  -- 1/2x output clock
      LOCK        : out std_logic   -- Lock signal
   );
end component CLK_GEN;

-- -------------------- Local bus  - interface ----------------------
component LB_BRIDGE is
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

-- *****************************   End of Components parts   *******************************************
-- *****************************************************************************************************

 -- Global Signals....

   signal ios_lbclk           : std_logic;
   signal ios_reset           : std_logic;
   signal reset               : std_logic;
   signal clk50               : std_logic;

   signal clkgen_lock         : std_logic;

 -- Local bus
   signal lbframe             : std_logic;
   signal lbas                : std_logic;
   signal lbrw                : std_logic;
   signal lblast              : std_logic;
   signal lbad                : std_logic_vector(15 downto 0);
   signal lbholda             : std_logic;
   signal lbrdy               : std_logic;
   signal lbclk               : std_logic;
   signal sda_m               : std_logic_vector(3 downto 0);
   signal scl_m               : std_logic_vector(3 downto 0);
   signal sda_i               : std_logic_vector(3 downto 0);
   signal scl_i               : std_logic_vector(3 downto 0);

   signal regiob_dummy_xled : std_logic_vector(3 downto 0);

   constant ID_BASE_ADDR     : integer := 16#0100000#; --
   constant I2C_BASE_ADDR0   : integer := 16#0200000#;
   constant I2C_BASE_ADDR1   : integer := 16#0200010#;
   constant I2C_BASE_ADDR2   : integer := 16#0200020#;
   constant I2C_BASE_ADDR3   : integer := 16#0200030#;

    -- SFPpro test
   constant ID_TEST      : std_logic_vector( 15 downto 0) := X"7880";
   constant ID_TEST_TEXT : std_logic_vector(255 downto 0) :=
        X"53465070726F5F74657374696e675F64657369676e0000000000000000000000"; 
      --  S F P p r o _ t e s t i n g _ d e s i g n
begin

-- ----------------------- Clk gen. component -------------------------

CLK_GEN_U: CLK_GEN
port map(
      -- Input
      CLK          => ios_lbclk,   -- Input clock frequency
      RESET        => ios_reset,   -- Global reset signal
      -- Output
      CLK1X        => lbclk,       -- 1X output clock
      CLK2X        => open,        -- 2X output clock
      CLKDV        => clk50,       -- 1/2x output clock
      LOCK         => clkgen_lock  -- Lock signal
   );

-- ---------------------- Local bus interface -----------------------------
IOS_TO_LB : LB_BRIDGE
 port map (
    RESET       => reset,
    LBCLK       => lbclk,
     -- Local bus input (to local_bus driver)
    LBFRAME_IN  => IOS(26),
    LBAS_IN     => IOS(25),
    LBRW_IN     => IOS(24),
    LBLAST_IN   => IOS(23),
    LBAD_IN     => IOS(19 downto 4),
    LBHOLDA_IN  => IOS(22),
    LBRDY_IN    => IOS(21),
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
      PROJECT_ID   => ID_TEST, 
      SW_MAJOR     => ID_SW_MAJOR,
      SW_MINOR     => ID_SW_MINOR,
      HW_MAJOR     => ID_HW_MAJOR,
      HW_MINOR     => ID_HW_MINOR,
      PROJECT_TEXT => ID_TEST_TEXT 
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
IOS(103 downto 100) <= regiob_dummy_xled;

ios_lbclk    <= IOS(2);
ios_reset    <= IOS(20);

reset       <= not clkgen_lock or ios_reset;

-- I2C connection -------------------------------------------------------------
I2C0_U : entity work.i2c
generic map (
   BASE_ADDR  => I2C_BASE_ADDR0--,
   --ADDR_WIDTH => 3--,
   --FREQUENCY  => "100MHz"
)
port map (
   RESET    => RESET,
   CLK      => lbclk,

   LBCLK    => LBCLK,      
   LBFRAME  => LBFRAME,
   LBHOLDA  => LBHOLDA,
   LBAD     => LBAD,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBRDY    => LBRDY,
   LBLAST   => LBLAST,

   -- I2C interface
   SCL_O   => scl_m(0),
   SCL_I   => scl_i(0),
   SDA_O   => sda_m(0),
   SDA_I   => sda_i(0)
);

I2C1_U : entity work.i2c
generic map (
   BASE_ADDR  => I2C_BASE_ADDR1--,
   --ADDR_WIDTH => 3--,
   --FREQUENCY  => "100MHz"
)
port map (
   RESET    => RESET,
   CLK      => lbclk,

   LBCLK    => LBCLK,      
   LBFRAME  => LBFRAME,
   LBHOLDA  => LBHOLDA,
   LBAD     => LBAD,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBRDY    => LBRDY,
   LBLAST   => LBLAST,

   -- I2C interface
   SCL_O   => scl_m(1),
   SCL_I   => scl_i(1),
   SDA_O   => sda_m(1),
   SDA_I   => sda_i(1)
);

I2C2_U : entity work.i2c
generic map (
   BASE_ADDR  => I2C_BASE_ADDR2--,
   --ADDR_WIDTH => 3--,
   --FREQUENCY  => "100MHz"
)
port map (
   RESET    => RESET,
   CLK      => lbclk,

   LBCLK    => LBCLK,      
   LBFRAME  => LBFRAME,
   LBHOLDA  => LBHOLDA,
   LBAD     => LBAD,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBRDY    => LBRDY,
   LBLAST   => LBLAST,

   -- I2C interface
   SCL_O   => scl_m(2),
   SCL_I   => scl_i(2),
   SDA_O   => sda_m(2),
   SDA_I   => sda_i(2)
);

I2C3_U : entity work.i2c
generic map (
   BASE_ADDR  => I2C_BASE_ADDR3--,
   --ADDR_WIDTH => 3--,
   --FREQUENCY  => "100MHz"
)
port map (
   RESET    => RESET,
   CLK      => lbclk,

   LBCLK    => LBCLK,      
   LBFRAME  => LBFRAME,
   LBHOLDA  => LBHOLDA,
   LBAD     => LBAD,
   LBAS     => LBAS,
   LBRW     => LBRW,
   LBRDY    => LBRDY,
   LBLAST   => LBLAST,

   -- I2C interface
   SCL_O   => scl_m(3),
   SCL_I   => scl_i(3),
   SDA_O   => sda_m(3),
   SDA_I   => sda_i(3)
);



MODDEFA(2) <= 'Z' when (sda_m(0)='1') else sda_m(0);
MODDEFA(1) <= 'Z' when (scl_m(0)='1') else scl_m(0);

MODDEFB(2) <= 'Z' when (sda_m(1)='1') else sda_m(1);
MODDEFB(1) <= 'Z' when (scl_m(1)='1') else scl_m(1);

MODDEFC(2) <= 'Z' when (sda_m(2)='1') else sda_m(2);
MODDEFC(1) <= 'Z' when (scl_m(2)='1') else scl_m(2);

MODDEFD(2) <= 'Z' when (sda_m(3)='1') else sda_m(3);
MODDEFD(1) <= 'Z' when (scl_m(3)='1') else scl_m(3);

sda_i(0) <= MODDEFA(2);
scl_i(0) <= MODDEFA(1);

sda_i(1) <= MODDEFB(2);
scl_i(1) <= MODDEFB(1);

sda_i(2) <= MODDEFC(2);
scl_i(2) <= MODDEFC(1);

sda_i(3) <= MODDEFD(2);
scl_i(3) <= MODDEFD(1);
end architecture sfp_arch;
