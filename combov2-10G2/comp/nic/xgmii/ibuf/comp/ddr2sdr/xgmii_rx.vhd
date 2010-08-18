-- Title      : XGMII Rx component
-- Project    : XGMII Reference Design
-------------------------------------------------------------------------------
-- File       : xgmii_rx.vhd
-- Author     : Xilinx Inc.
-------------------------------------------------------------------------------
-- Description:  This performs the XGMII Receiver Clock Production and Data Reception
--               as described in the Application Note.
--
--              II. Module I/O
--
--              Inputs: XGMII_RX_CLK, XGMII_RXD, XGMII_RXC, RESET, RX_DCM_RESET
--              Outputs: RX_CLK_INT, RXD_INT, RXC_INT, RX_DCM_LOCK
--



library IEEE;
use IEEE.std_logic_1164.all;

-- pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
-- pragma translate_on


entity XGMII_RX is
   port(
      XGMII_RX_CLK           : in std_logic;                       -- XGMII RX_CLK.
      XGMII_RXD              : in std_logic_vector(31 downto 0);   -- XGMII RXD (Data receieved from XGMII).
      XGMII_RXC              : in std_logic_vector(3 downto 0);    -- XGMII RXC (Data Delimiters received from XGMII).
      RESET                  : in std_logic;                       -- Global Asynchronous Reset.
      RX_CLK_INT             : out std_logic;                      -- Internal RX_CLK (use for Rx synchronous logic).
      RXD_INT                : out std_logic_vector(63 downto 0);  -- Internal RXD at Single Data Rate.
      RXC_INT                : out std_logic_vector(7 downto 0);   -- Internal RXC at Single Data Rate.
      RX_DCM_LOCK            : out std_logic;                      -- The Locked signal from the RX DCM.
      RX_DCM_RESET           : in std_logic                        -- Manual reset of Rx DCM.
   );
end XGMII_RX;



architecture RTL of XGMII_RX is



-------------------------------------------------------------
--  Xilinx Primitives used in this entity                  --
-------------------------------------------------------------

component FF_PAIR
    port(
        CLK                    : in std_logic;    -- flip-flop's clock.
        RST                    : in std_logic;    -- Global Asynchronous Reset.
        CLKEN                  : in std_logic;    -- Clock Enable.
        I                      : in std_logic;    -- Input Data Bit.
        O_REG                  : out std_logic    -- Output Data Bit.
        );
end component;


component BUFG
   port(
      O                      :	out   STD_ULOGIC;
      I                      :	in    STD_ULOGIC);
end component;


component IBUFG
   port(
      O                      :	out   STD_ULOGIC;
      I                      :	in    STD_ULOGIC);
end component;


component IBUF
   port(
      O                      :	out   STD_ULOGIC;
      I                      :	in    STD_ULOGIC);
end component;


component DCM
   port (
      CLKIN                  : in  std_ulogic := '0';
      CLKFB                  : in  std_ulogic := '0';
      DSSEN                  : in  std_ulogic := '0';
      PSINCDEC               : in  std_ulogic := '0';
      PSEN                   : in  std_ulogic := '0';
      PSCLK                  : in  std_ulogic := '0';
      RST                    : in  std_ulogic := '0';
      CLK0                   : out std_ulogic := '0';
      CLK90                  : out std_ulogic := '0';
      CLK180                 : out std_ulogic := '0';
      CLK270                 : out std_ulogic := '0';
      CLK2X                  : out std_ulogic := '0';
      CLK2X180               : out std_ulogic := '0';
      CLKDV                  : out std_ulogic := '0';
      CLKFX                  : out std_ulogic := '0';
      CLKFX180               : out std_ulogic := '0';
      LOCKED                 : out std_ulogic := '0';
      PSDONE                 : out std_ulogic := '0';
      STATUS                 : out std_logic_vector(7 downto 0) := "00000000");
end component;

-------------------------------------------------------------

   signal VCC                : std_logic;
   signal GND                : std_logic;

   signal XGMII_RX_CLK_INT   : std_logic;                          -- XGMII_RX_CLK after Input HSTL buffer.
   signal CLK0               : std_logic;                          -- 90 degree phase clock from DCM to BUFG.
   signal RX_CLK0            : std_logic;                          -- In-phase clock after BUFG (on global routing).

   signal XGMII_RXD_INT      : std_logic_vector(31 downto 0);      -- XGMII_TXD after Input HSTL buffers.
   signal XGMII_RXC_INT      : std_logic_vector(3 downto 0);       -- XGMII_TXC after Input HSTL buffers.
   signal RXD_SDR            : std_logic_vector(63 downto 0)
                             := (others => '0');                   -- SDR Data received from XGMII.
   signal RXC_SDR            : std_logic_vector(7 downto 0)
                             := (others => '0');                   -- SDR Control received from XGMII.


begin

   VCC <= '1';
   GND <= '0';

------------------------------------------------------------
--  XGMII Receiver Clock Production                       --
------------------------------------------------------------

-- Receive XGMII_RX_CLK on external PAD using HSTL_I SelectIO
   RECEIVE_XGMII_RX_CLK: IBUFG
   port map(
      I               => XGMII_RX_CLK,
      O               => XGMII_RX_CLK_INT
   );

-- Instantiate and wire up DCM
   DIG_CLK_MANAGEMENT : DCM
   port map (
      CLKIN           => XGMII_RX_CLK_INT,
      CLKFB           => RX_CLK0,
      RST             => RX_DCM_RESET,
      DSSEN           => GND,
      PSINCDEC        => GND,
      PSEN            => GND,
      PSCLK           => GND,
      CLK0            => CLK0,
      CLK90           => OPEN,
      CLK180          => OPEN,
      CLK270          => OPEN,
      CLK2X           => OPEN,
      CLK2X180        => OPEN,
      CLKDV           => OPEN,
      CLKFX           => OPEN,
      CLKFX180        => OPEN,
      LOCKED          => RX_DCM_LOCK,
      STATUS          => OPEN,
      PSDONE          => OPEN
   );



-- Route in-phase clock onto a Global Routing Network
   BUFG0 : BUFG
   port map(
      I               => CLK0,
      O               => RX_CLK0
   );

-- connect together RX_CLK_INT and TX_CLK0
   RX_CLK_INT          <= RX_CLK0;

------------------------------------------------------------
--  XGMII Data Reception                                  --
------------------------------------------------------------

-- Receive XGMII_RXD on external PADs using HSTL_I SelectIO
   RECEIVE_XGMII_RXD_BUS:
   for I in 0 to 31 generate
      RECEIVE_XGMII_RXD_BITS: IBUF
      port map(
         I               => XGMII_RXD(I),
         O               => XGMII_RXD_INT(I)
      );
   end generate;

-- Receive XGMII_RXC on external PADs using HSTL_I SelectIO
   RECEIVE_XGMII_RXC_BUS:
   for I in 0 to 3 generate
      RECEIVE_XGMII_RXB_BITS: IBUF
      port map(
         I               => XGMII_RXC(I),
         O               => XGMII_RXC_INT(I)
      );
   end generate;

-- purpose: Infere IOB input DDR registers on rising clock edge.
-- type   : sequential
   IOB_DDR_RISING: process (RESET, RX_CLK0)
   begin
      if RESET = '1' then
         RXD_SDR(63 downto 32) <= (others => '0');
         RXC_SDR(7 downto 4)   <= (others => '0');

      elsif RX_CLK0'event and RX_CLK0 = '1' then
         RXD_SDR(63 downto 32) <= XGMII_RXD_INT(31 downto 0);
         RXC_SDR(7 downto 4)   <= XGMII_RXC_INT(3 downto 0);
      end if;
   end process IOB_DDR_RISING;

-- purpose: Infere IOB input DDR registers on falling clock edge.
-- type   : sequential
   IOB_DDR_FALLING: process (RESET, RX_CLK0)
   begin
      if RESET = '1' then
         RXD_SDR(31 downto 0)  <= (others => '0');
         RXC_SDR(3 downto 0)   <= (others => '0');

      elsif RX_CLK0'event and RX_CLK0 = '0' then
         RXD_SDR(31 downto 0)  <= XGMII_RXD_INT(31 downto 0);
         RXC_SDR(3 downto 0)   <= XGMII_RXC_INT(3 downto 0);
      end if;
   end process IOB_DDR_FALLING;

-- purpose: CLB logic: Reclock RXD_SDR<63:32> / RXC_SDR<7:4> on the rising edge.
-- type   : sequential
   RECLOCK_RISING : process (RX_CLK0, RESET)
   begin
      if RESET = '1' then
         RXD_INT(63 downto 32)    <= (others => '0');
         RXC_INT(7 downto 4)      <= (others => '0');

      elsif RX_CLK0'event and RX_CLK0 = '1' then
         RXD_INT(63 downto 32)    <=  RXD_SDR(63 downto 32);
         RXC_INT(7 downto 4)      <=  RXC_SDR(7 downto 4);

      end if;
   end process RECLOCK_RISING;

-- purpose: CLB LOGIC: This relocks the falling edge RXD/RXC bits twice, fistly on the falling edge and
--          then again on the rising edge.  These flip-flop pairs are have RLOC constraints (see xgmii.ucf)
--          to place these 2 flip-flops in adjacent slices.  This enables the PAR tools to meet the 960 ps
--          delay constaint that arises from the worst case clock duty-cycle (see xgmii.pdf).

   RXD_FALLING_RECLOCK_BUS:
   for I in 0 to 31 generate
      RXD_FALLING_RECLOCK_BITS: FF_PAIR
      port map (
         CLK                    => RX_CLK0,
         RST                    => RESET,
         CLKEN                  => VCC,
         I                      => RXD_SDR(I),
         O_REG                  => RXD_INT(I)
         );
   end generate;

   RXC_FALLING_RECLOCK_BUS:
   for I in 0 to 3 generate
      RXC_FALLING_RECLOCK_BITS: FF_PAIR
      port map (
         CLK                    => RX_CLK0,
         RST                    => RESET,
         CLKEN                  => VCC,
         I                      => RXC_SDR(I),
         O_REG                  => RXC_INT(I)
         );
   end generate;

end RTL;
