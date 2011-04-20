-- prng_8.vhd: LFSR generator of 8-bit pseudo-random numbers
-- Copyright (C) 2011
-- Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity PRNG_8 is
  port
  (
     CLK    : in  std_logic;
     RESET  : in  std_logic;
     SEED   : in  std_logic_vector(7 downto 0);
     OUTPUT : out std_logic_vector(7 downto 0)
  );
end entity PRNG_8;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of PRNG_8 is

-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================
signal r_reg, r_next : std_logic_vector(7 downto 0); 
signal fb : std_logic; 

-- ==========================================================================
--                           ARCHITECTURE BODY
-- ==========================================================================
begin
  process (CLK)
  begin
    if (RESET = '1') then
      r_reg <= SEED;
    elsif (CLK'event and CLK = '1') then
      r_reg <= r_next;
    end if;
  end process;   
  
  -- next state logic (taps of primitive polynom are [8 4 3 2])
  fb <= r_reg(7) xor r_reg(3) xor r_reg(2) xor r_reg(1);
  r_next <= fb & r_reg(7 downto 1);
  
  -- output logic 
  OUTPUT <= r_reg;
end architecture arch;  