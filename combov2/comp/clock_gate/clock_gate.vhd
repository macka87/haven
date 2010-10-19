-- clock_gate.vhd: Clock gate: a component that can be used for
--                 clock gating
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

entity clock_gate is
   port
   (
      -- input clock
      CLK_IN             :  in std_logic;
      -- input clock enable signal
      CLOCK_ENABLE       :  in std_logic;

      -- output clock
      CLK_OUT            : out std_logic
   );
end entity;

architecture arch of clock_gate is

   -- clock buffer with clock enable
   component BUFGCE
   port (
      I  : in  std_logic;
      CE : in  std_logic;
      O  : out std_logic
   );
   end component;

begin

   bufgce_i: BUFGCE
   port map (
      I => CLK_IN,
      CE => CLOCK_ENABLE,
      O => CLK_OUT
   );

end architecture;
