--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Signal Observer's Rearranger
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
entity OBSERVER_REARRANGER is

   generic
   (
      IN_DATA_WIDTH    : integer := 64;
      OUT_DATA_WIDTH   : integer := 64
   );

   port
   (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- ----------------- INPUT INTERFACE ----------------------------------
      RX_DATA        : in  std_logic_vector(IN_DATA_WIDTH-1 downto 0);
      RX_READ_NEXT   : out std_logic;
      RX_VALID       : in  std_logic;
      
      -- ----------------- OUTPUT INTERFACE ---------------------------------      
      TX_DATA        : in  std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
      TX_READ_NEXT   : out std_logic;
      TX_VALID       : in  std_logic
   );
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of OBSERVER_REARRANGER is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================


begin


end architecture;
