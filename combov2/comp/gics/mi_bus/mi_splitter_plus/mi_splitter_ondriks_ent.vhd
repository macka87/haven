-- mi_splitter_ondriks_ent.vhd: Ondrik's MI Splitter entity
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             ENTITY DECLARATION                            --
-- ---------------------------------------------------------------------------- 

entity MI_SPLITTER_ONDRIKS is
   generic(
      -- Data width
      DATA_WIDTH    : integer := 32;
      -- Number of output ports
      ITEMS         : integer := 8;
      -- Bases of address spaces (base of port0 is 0x00000000)
      PORT0_BASE    : std_logic_vector(31 downto 0) := X"00080000";
      PORT0_LIMIT   : std_logic_vector(31 downto 0) := X"00001000";
      PORT1_BASE    : std_logic_vector(31 downto 0) := X"00081000";
      PORT1_LIMIT   : std_logic_vector(31 downto 0) := X"00001000";
      PORT2_BASE    : std_logic_vector(31 downto 0) := X"01000000";
      PORT2_LIMIT   : std_logic_vector(31 downto 0) := X"01000000";
      PORT3_BASE    : std_logic_vector(31 downto 0) := X"00040000";
      PORT3_LIMIT   : std_logic_vector(31 downto 0) := X"00010000";
      PORT4_BASE    : std_logic_vector(31 downto 0) := X"00050000";
      PORT4_LIMIT   : std_logic_vector(31 downto 0) := X"00010000";
      PORT5_BASE    : std_logic_vector(31 downto 0) := X"00060000";
      PORT5_LIMIT   : std_logic_vector(31 downto 0) := X"00020000";
      PORT6_BASE    : std_logic_vector(31 downto 0) := X"00090000";
      PORT6_LIMIT   : std_logic_vector(31 downto 0) := X"00010000";
      PORT7_BASE    : std_logic_vector(31 downto 0) := X"00A00000";
      PORT7_LIMIT   : std_logic_vector(31 downto 0) := X"00100000";
      -- Input pipeline
      PIPE          : boolean := true;
      PIPE_OUTREG   : boolean := false
   );
   port(
      -- Common interface -----------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;
      
      -- Input MI interface ---------------------------------------------------
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_ADDR     : in  std_logic_vector(31 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;
      
      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     : out std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ITEMS*32-1 downto 0);
      OUT_BE      : out std_logic_vector(ITEMS*DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_WR      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_ARDY    : in  std_logic_vector(ITEMS-1 downto 0);
      OUT_DRD     : in  std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic_vector(ITEMS-1 downto 0)
      
   );
end entity;
