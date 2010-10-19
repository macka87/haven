-- clock_gate_tb.vhd: Clock gate testbench
-- Author(s): Ondrej Lengal <ilengal@fit.vutbr.cz>
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;

library work;

entity testbench is
end entity;

architecture test of testbench is

   -- ------------------------------------------------------------------------
   --                                Constants
   -- ------------------------------------------------------------------------

   -- clock period
   constant CLK_PERIOD  : time := 10 ns;

   -- ------------------------------------------------------------------------
   --                                 Signals
   -- ------------------------------------------------------------------------

   -- common signals
   signal clk_in         : std_logic;
   signal enable         : std_logic;
   signal clk_out        : std_logic;

begin

   -- -----------------------------------------------------------------------
   --                             Unit under test
   -- -----------------------------------------------------------------------
   uut: entity work.clock_gate
   port map(
      CLK_IN         => clk_in,
      CLOCK_ENABLE   => enable,
      CLK_OUT        => clk_out
   );


   -- -------------------------------------------------------------------------
   --                                CLOCKs
   -- -------------------------------------------------------------------------
   clk_genp: process
   begin
      clk_in  <= '1';
      wait for CLK_PERIOD/2;
      clk_in  <= '0';
      wait for CLK_PERIOD/2;
   end process;


   -- -----------------------------------------------------------------------
   --                                 Test
   -- -----------------------------------------------------------------------
   tb : process
   begin

      enable <= '0';

      wait for 25 ns;
      enable <= '1';
      wait for 5 ns;

      wait for 45 ns;
      enable <= '0';

      wait;
   end process;


end architecture;
