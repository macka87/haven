--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    Rearranger
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

-- This unit serves as a rearranger of signals of different width. It either
-- splits a single word from the input into multiple words at the output (in
-- case the input width is bigger than the output width), or multiple words at
-- the input into a single word at the output (in case the input width is
-- smaller than the output width).
entity REARRANGER is

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
architecture arch of REARRANGER is

begin

   -- data widths are equal
   GEN_ARCH_EQUAL:
   if (IN_DATA_WIDTH = OUT_DATA_WIDTH) generate
      TX_DATA        <= RX_DATA;
      TX_VALID       <= RX_VALID;
      RX_READ_NEXT   <= TX_READ_NEXT;
   end generate;

   -- RX data width > TX data width
   GEN_ARCH_DOWN:
   if (IN_DATA_WIDTH > OUT_DATA_WIDTH) generate
      rearranger_down_i: entity work.REARRANGER_DOWN
         generic map(
            IN_DATA_WIDTH  => IN_DATA_WIDTH,
            OUT_DATA_WIDTH => OUT_DATA_WIDTH
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            --
            RX_DATA        => RX_DATA,
            RX_VALID       => RX_VALID,
            RX_READ_NEXT   => RX_READ_NEXT,
            --
            TX_DATA        => TX_DATA,
            TX_VALID       => TX_VALID,
            TX_READ_NEXT   => TX_READ_NEXT
         );
   end generate;

   -- RX data width < TX data width
   GEN_ARCH_UP:
   if (IN_DATA_WIDTH < OUT_DATA_WIDTH) generate
      rearranger_up_i: entity work.REARRANGER_UP
         generic map(
            IN_DATA_WIDTH  => IN_DATA_WIDTH,
            OUT_DATA_WIDTH => OUT_DATA_WIDTH
         )
         port map(
            CLK            => CLK,
            RESET          => RESET,
            --
            RX_DATA        => RX_DATA,
            RX_VALID       => RX_VALID,
            RX_READ_NEXT   => RX_READ_NEXT,
            --
            TX_DATA        => TX_DATA,
            TX_VALID       => TX_VALID,
            TX_READ_NEXT   => TX_READ_NEXT
         );
   end generate;

end architecture;
