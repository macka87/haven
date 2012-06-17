--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Rearranger (Upwards)
-- Description: 
-- Author:       Marcela Simkova <xsimko03@stud.fit.vutbr.cz> 
-- Date:         15.4.2011 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity REARRANGER_UP is

   generic
   (
      IN_DATA_WIDTH    : integer := 64;
      OUT_DATA_WIDTH   : integer := 128
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      RX_VALID       : in  std_logic;
      RX_READ_NEXT   : out std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      TX_DATA        : out std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_VALID       : out std_logic;
      TX_READ_NEXT   : in  std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of REARRANGER_UP is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

-- input signals
signal sig_rx_data      : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
signal sig_rx_read_next : std_logic;
signal sig_rx_valid     : std_logic;

-- output signals
signal sig_tx_data      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
signal sig_tx_read_next : std_logic;
signal sig_tx_valid     : std_logic;

begin

   assert (IN_DATA_WIDTH < OUT_DATA_WIDTH)
      report "OUT_DATA_WIDTH needs to be bigger than IN_DATA_WIDTH"
      severity failure;

   assert(false)
      report "Not implemented"
      severity failure;

end architecture;


