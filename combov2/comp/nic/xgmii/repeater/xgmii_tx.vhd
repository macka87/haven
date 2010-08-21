-- Title      : XGMII Tx component
-- Project    : XGMII Reference Design
-------------------------------------------------------------------------------
-- File       : xgmii_tx.vhd
-- Author     : Xilinx Inc.
-------------------------------------------------------------------------------
-- Description:  This performs the XGMII Transmitter Clock Production and Data Transmission
--               as described in the Application Note.
--
--              II. Module I/O
--
--              Inputs: RESET, TX_CLK0, TX_CLK90, TXD_INT, TXC_INT,
--              Outputs: XGMII_TX_CLK, XGMII_TXD, XGMII_TXC
--

library IEEE;
use IEEE.std_logic_1164.all;

--pragma translate_off
library UNISIM;
use UNISIM.VCOMPONENTS.ALL;
--pragma translate_on

entity XGMII_TX is
    port(
        XGMII_TX_CLK           : out std_logic;                      -- XGMII TX_CLK.
        XGMII_TXD              : out std_logic_vector(31 downto 0);  -- XGMII TXD (Data driven onto XGMII).
        XGMII_TXC              : out std_logic_vector(3 downto 0);   -- XGMII TXC (Data Delimiters driven onto XGMII).
        RESET                  : in std_logic;                       -- Global Asynchronous Reset.
        TX_CLK0                : in std_logic;                       -- Reference TX_CLK provided by user (156.25MHz)
        TX_CLK90               : in std_logic;                       -- Reference TX_CLK shifted by 90 dgr
        TX_CLK180              : in std_logic;                       -- Reference TX_CLK shifted by 90 dgr and inverted
        TX_CLK270              : in std_logic;                       -- Reference TX_CLK shifted by 90 dgr and inverted
        TXD_INT                : in std_logic_vector(63 downto 0);   -- Internal TXD at Single Data Rate.
        TXC_INT                : in std_logic_vector(7 downto 0)     -- Internal TXC at Single Data Rate.
     );
end XGMII_TX;

architecture RTL_NO_DCM of XGMII_TX is


    -------------------------------------------------------------
    --  Xilinx Primitives used in this entity                  --
    -------------------------------------------------------------

    component OBUF
        port(
            O                      :	out   STD_ULOGIC;
            I                      :	in    STD_ULOGIC);
    end component;


    component FDDRRSE
        port(
            Q                      :	out   STD_ULOGIC;
            D0                     :	in    STD_ULOGIC;
            D1                     :	in    STD_ULOGIC;
            C0                     :	in    STD_ULOGIC;
            C1                     :	in    STD_ULOGIC;
            CE                     :	in    STD_ULOGIC;
            S                      :	in    STD_ULOGIC;
            R                      :	in    STD_ULOGIC);
    end component;

    signal VCC                : std_logic;
    signal GND                : std_logic;

    signal TX_CLK90_INV       : std_logic;                          -- The inverse of TX_CLK90.
    signal TX_CLK0_INV        : std_logic;                          -- The inverse of TX_CLK0.
    signal XGMII_TX_CLK_INT   : std_logic;                          -- XGMII_TX_CLK before Ouput HSTL Buffer

    signal TXD_INT_RISING     : std_logic_vector(63 downto 0);      -- TXD_INT<63:0> reclocked on rising edge.
    signal TXD_INT_FALLING    : std_logic_vector(63 downto 32);     -- TXD_INT_RISING<63:32> reclocked on falling edge.
    signal TXC_INT_RISING     : std_logic_vector(7 downto 0);       -- TXC_INT<7:0> reclocked on rising edge.
    signal TXC_INT_FALLING    : std_logic_vector(7 downto 4);       -- TXC_INT_RISING<7:4> on falling edge.
    signal XGMII_TXD_INT      : std_logic_vector(31 downto 0);      -- XGMII_TXD before Ouput HSTL Buffers.
    signal XGMII_TXC_INT      : std_logic_vector(3 downto 0);       -- XGMII_TXC before Ouput HSTL Buffers.


begin

   VCC <= '1';
   GND <= '0';

   ------------------------------------------------------------
   --  XGMII Transmitter Clock Production                    --
   ------------------------------------------------------------

   -- Obtain inverse clocks for DDR registers (to clock on falling edge)
   TX_CLK0_INV        <= TX_CLK180;
   TX_CLK90_INV       <= TX_CLK270;

   --  Produce XGMII_TX_CLK using IOB DDR output registers.
   TX_CLK_DDR: FDDRRSE
   port map (
       Q   => XGMII_TX_CLK_INT,
       D0  => VCC, --GND,
       D1  => GND, --VCC,
       C0  => TX_CLK90,
       C1  => TX_CLK90_INV,
       CE  => VCC,
       R   => GND,
       S   => GND
    );

--    XGMII_TX_CLK_INT <= TX_CLK0;

   -- Drive XGMII_TX_CLK onto external PAD using HSTL_I SelectIO
   DRIVE_XGMII_TX_CLK: OBUF
   port map (
      I  => XGMII_TX_CLK_INT,
      O  => XGMII_TX_CLK
   );
    
    ------------------------------------------------------------
    --  XGMII Data Transmission                               --
    ------------------------------------------------------------

    -- purpose: CLB logic: Reclock SDR inputs on the rising edge.
    -- type   : sequential
    RECLOCK_RISING : process (TX_CLK0, RESET)
    begin
        if RESET = '1' then
            TXD_INT_RISING(63 downto 0)     <= (others => '0');
            TXC_INT_RISING(7 downto 0)      <= (others => '0');

        elsif TX_CLK0'event and TX_CLK0 = '1' then
            TXD_INT_RISING(63 downto 0)     <= TXD_INT(63 downto 0);
            TXC_INT_RISING(7 downto 0)      <= TXC_INT(7 downto 0);

        end if;
    end process RECLOCK_RISING;

    -- purpose: CLB logic: Reclock on the falling edge.
    -- type   : sequential
    RECLOCK_FALLING : process (TX_CLK0_INV, RESET)
    begin
        if RESET = '1' then
            TXD_INT_FALLING(63 downto 32)   <= (others => '0');
            TXC_INT_FALLING(7 downto 4)     <= (others => '0');

        elsif TX_CLK0_INV'event and TX_CLK0_INV = '1' then
            TXD_INT_FALLING(63 downto 32)   <= TXD_INT_RISING(63 downto 32);
            TXC_INT_FALLING(7 downto 4)     <= TXC_INT_RISING(7 downto 4);

        end if;
    end process RECLOCK_FALLING;

    --  Produce XGMII_TXD_INT using IOB DDR output registers.
    GEN_TXD_DDR_OUT_REGS:
        for I in 0 to 31 generate
        TXD_DDR: FDDRRSE
        port map (
            Q               => XGMII_TXD_INT(I),
            D0              => TXD_INT_RISING(I),
            D1              => TXD_INT_FALLING(32 + I),
            C0              => TX_CLK0,
            C1              => TX_CLK0_INV,
            CE              => VCC,
            R               => GND,
            S               => GND
            );
    end generate;

    --  Produce XGMII_TXC using IOB DDR output registers.
    GEN_TXC_DDR_OUT_REGS:
        for I in 0 to 3 generate
        TXC_DDR: FDDRRSE
        port map (
            Q               => XGMII_TXC_INT(I),
            D0              => TXC_INT_RISING(I),
            D1              => TXC_INT_FALLING(4 + I),
            C0              => TX_CLK0,
            C1              => TX_CLK0_INV,
            CE              => VCC,
            R               => GND,
            S               => GND
            );
    end generate;

    -- Drive XGMII_TXD onto external PADs using HSTL_I SelectIO
    DRIVE_XGMII_TXD_BUS:
        for I in 0 to 31 generate
        DRIVE_XGMII_TXD_BITS: OBUF
        port map(
            I               => XGMII_TXD_INT(I),
            O               => XGMII_TXD(I)
            );
    end generate;

    -- Drive XGMII_TXC onto external PADs using HSTL_I SelectIO
    DRIVE_XGMII_TXC_BUS:
        for I in 0 to 3 generate
        DRIVE_XGMII_TXC_BITS: OBUF
        port map(
            I               => XGMII_TXC_INT(I),
            O               => XGMII_TXC(I)
            );
    end generate;

end RTL_NO_DCM;
