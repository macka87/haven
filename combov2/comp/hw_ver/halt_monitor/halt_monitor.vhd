--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   halt_monitor.vhd
--  \date   10-04-2013
--  \brief  Halt monitor monitors port_halt for detection of halt instruction
--          after detection of halt instruction holds processor in reset
--          and propagate information about halt instruction to other monitors

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity HALT_MONITOR is port
   (
      CLK       : in  std_logic;
      RESET     : in  std_logic;

      -- detection of halt instruction
      port_halt : in std_logic;

      -- HALT propagation
      HALT      : out std_logic;

      -- Codix reset
      RST_n     : out std_logic

   );
   
end entity;

-- ----------------------------------------------------------
--                 architecture
-- ----------------------------------------------------------
architecture arch of HALT_MONITOR is
begin

   process(CLK, RESET, port_halt)
   begin

      if CLK = '1' and CLK'event then
         if RESET = '1' then
            HALT  <= '0';
            RST_n <= '1';
         elsif port_halt = '1' then
            HALT  <= '1';
            RST_n <= '0';
         elsif port_halt = '0' then
            HALT  <= '0';
            RST_n <= '1';
         end if;
      end if;

   end process;

end architecture;
