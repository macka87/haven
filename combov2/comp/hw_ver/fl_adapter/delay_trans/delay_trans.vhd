--------------------------------------------------------------------------
-- Project Name: Hardware - Software Framework for Functional Verification
-- File Name:    FrameLink Adapter
-- Description:  Transforms random data to desired delays.
-- Author:       Marcela Simkova <isimkova@fit.vutbr.cz> 
-- Date:         19.6.2013 
-- --------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity DELAY_TRANSFORMER is

   generic
   (
      -- data width
      DATA_WIDTH  : integer := 64
   );

   port
   (
      INPUT    :  in std_logic_vector(DATA_WIDTH-1 downto 0);
      OUTPUT   : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );       
   
end entity;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of DELAY_TRANSFORMER is
begin
   OUTPUT <= (others => '0');
end architecture;
