-- ondriks_cdc_fifo.vhd: Clock-Domain Crossing FIFO for Virtex-5
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity ONDRIKS_CDC_FIFO is
   generic
   (
      -- data width
      DATA_WIDTH       : integer
   );
   port
   (
      -- asynchronous reset
      RESET            :  in std_logic;

      -- write interface
      WR_CLK           :  in std_logic;
      WR_DATA          :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      WR_WRITE         :  in std_logic;
      WR_FULL          : out std_logic;
      WR_ALMOST_FULL   : out std_logic;

      -- read interface
      RD_CLK           :  in std_logic;
      RD_DATA          : out std_logic_vector(DATA_WIDTH-1 downto 0);
      RD_READ          :  in std_logic;
      RD_EMPTY         : out std_logic;
      RD_ALMOST_EMPTY  : out std_logic
   );
end entity;


-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of ONDRIKS_CDC_FIFO is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

begin

   -- -----------------------------------------------------------------------
   --                              Assertions
   -- -----------------------------------------------------------------------
   assert ((DATA_WIDTH = 64) AND (DATA_WIDTH /= 64))
      report "Invalid data width"
      severity failure;


end architecture;
