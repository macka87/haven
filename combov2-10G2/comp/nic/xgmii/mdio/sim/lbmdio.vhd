LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

ENTITY LbMDIO IS
Port (
      --MDIO---
      CLK    : in std_logic; --clock
      RESET  : in std_logic;
	 PHYDATA: inout std_logic;
	 --lb
	 LAD    : inout std_logic_vector(31 downto 0);-- PLX mux. Addr/Data
      ADS    : in std_logic;                 -- Address strobe, active low
      BLAST  : in std_logic;                 -- Last transfer, active: Low
      LHOLD  : in std_logic;                 -- PLX requests, active: High
      LHOLDA : out std_logic;                -- Hold acknowledge, active: High
      LWR    : in std_logic;                 -- Read/write, active: read: Low
      READY  : out std_logic;                -- Data is ready, active: Low
      LRESET : in std_logic;                 -- Local Reset
      LCLKF  : in std_logic;                 -- Local Clock
      USERo  : in std_logic;                 -- USERo = '1': prog. CPLD
	 SWQ_REQ: in std_logic

);
END LbMDIO;


architecture beh of LbMDIO is
signal  LBCLK   : std_logic;
signal  LBFRAME : std_logic;
signal  LBAS    : std_logic;
signal  LBRW    : std_logic;
signal  LBLAST  : std_logic;
signal  LBAD    : std_logic_vector(15 downto 0);
signal  LBHOLDA : std_logic;
signal  LBRDY   : std_logic;


-------------------------MDIO+LBCONMEM---------------------
component MDIO is
 port (
  -------------- hodiny a reset ----------------
  CLK: in std_logic; --hodiny
  RESET   : IN std_logic;
  ---rozhrani Lbconn_mem
  LBCLK   : IN std_logic;
  LBFRAME : IN std_logic;
  LBAS    : IN std_logic;
  LBRW    : IN std_logic;
  LBLAST  : IN std_logic;
  LBAD    : INOUT std_logic_vector(15 downto 0);
  LBHOLDA : OUT std_logic;
  LBRDY   : OUT std_logic;

  ----------vstup/vystup do/z phyteru ------------------
  PHYDATA: inout std_logic
);
end component MDIO;
---------------------------------------------------------------------
----------------------------------------------------------------------

component local_bus is
    Port (
        -- PLX section
      LAD    : inout std_logic_vector(31 downto 0);-- PLX mux. Addr/Data
      ADS    : in std_logic;                 -- Address strobe, active low
      BLAST  : in std_logic;                 -- Last transfer, active: Low
      LHOLD  : in std_logic;                 -- PLX requests, active: High
      LHOLDA : out std_logic;                -- Hold acknowledge, active: High
      LWR    : in std_logic;                 -- Read/write, active: read: Low
      READY  : out std_logic;                -- Data is ready, active: Low
      LRESET : in std_logic;                 -- Local Reset
      LCLKF  : in std_logic;                 -- Local Clock
      USERo  : in std_logic;                 -- USERo = '1': prog. CPLD

      -- Internal bus signals
      LBCLK   : out std_logic;              -- Internal bus clock, up to 100 MHz
      LBFRAME : out std_logic;              -- Frame
      LBHOLDA : in std_logic;               -- Hold Ack (HOLDA), active LOW
      LBAD    : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS    : out std_logic;              -- Adress strobe
      LBRW    : out std_logic;              -- Direction (Read/Write,low : read)
      LBRDY   : in std_logic;               -- Ready, active LOW
      LBLAST  : out std_logic;              -- Last word in burst transfer
      -- special
      SWQ_REQ   : in std_logic              -- SW queue request
    );

end component local_bus;


begin
LB1: local_bus
port map (
LBCLK=>LBCLK, LBFRAME=>LBFRAME, LBHOLDA=>LBHOLDA, LBAD=>LBAD,
LBAS=>LBAS, LBRW=>LBRW, LBRDY=>LBRDY,LBLAST=>LBLAST, LAD=>LAD,
ADS=>ADS, BLAST=>BLAST, LHOLD=>LHOLD, LHOLDA=>LHOLDA, LWR=>LWR,
READY=>READY, LRESET=> LRESET, LCLKF=>LCLKF, USERo=>USERo,SWQ_REQ=>SWQ_REQ
);

MDIO1 : MDIO
port map (
CLK => CLK, RESET => RESET,
LBCLK => LBCLK, LBFRAME => LBFRAME, LBAS=>LBAS,
LBRW => LBRW, LBLAST => LBLAST, LBAD => LBAD, LBHOLDA => LBHOLDA,
LBRDY => LBRDY,PHYDATA=>PHYDATA
);
end beh;
