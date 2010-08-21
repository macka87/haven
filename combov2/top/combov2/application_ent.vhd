-- application_ent.vhd : Combov2 NetCOPE application module entity
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--

-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;

entity APPLICATION is
   port (
      -- ----------------------------------------------------------------------
      -- CLOCKs and RESETs
      -- ----------------------------------------------------------------------
      -- Clock signal for user interface
      CLK                  : in std_logic; --  set DIV constants to derive from 1GHz

      -- Global reset
      RESET                : in std_logic;

      -- ----------------------------------------------------------------------
      -- DMA INTERFACE
      -- ----------------------------------------------------------------------

      -- input interface
      RX_DATA            :  in std_logic_vector(63 downto 0);
      RX_DREM            :  in std_logic_vector(2 downto 0);
      RX_SOF_N           :  in std_logic;
      RX_EOF_N           :  in std_logic;
      RX_SOP_N           :  in std_logic;
      RX_EOP_N           :  in std_logic;
      RX_SRC_RDY_N       :  in std_logic;
      RX_DST_RDY_N       : out std_logic;

      -- output interface
      TX_DATA            : out std_logic_vector(63 downto 0);
      TX_DREM            : out std_logic_vector(2 downto 0);
      TX_SOF_N           : out std_logic;
      TX_EOF_N           : out std_logic;
      TX_SOP_N           : out std_logic;
      TX_EOP_N           : out std_logic;
      TX_SRC_RDY_N       : out std_logic;
      TX_DST_RDY_N       :  in std_logic;

      -- MI32 interface
      MI32_DWR           : in  std_logic_vector(31 downto 0);
      MI32_ADDR          : in  std_logic_vector(31 downto 0);
      MI32_RD            : in  std_logic;
      MI32_WR            : in  std_logic;
      MI32_BE            : in  std_logic_vector(3 downto 0);
      MI32_DRD           : out std_logic_vector(31 downto 0);
      MI32_ARDY          : out std_logic;
      MI32_DRDY          : out std_logic
   );

end APPLICATION;
