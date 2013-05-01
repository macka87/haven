--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   testbench.vhd
--  \date   10-04-2013
--  \brief  Testbench for memory monitor

library ieee;
use ieee.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
--use work.fl_sim_oper.all;
--use work.fl_bfm_pkg.all;
--use work.fl_bfm_rdy_pkg.all;
--use work.math_pack.all;


entity testbench is
end entity testbench;

architecture behavioral of testbench is

   constant clkper     : time := 10 ns; 
   constant reset_time : time := 10 ns;

   -- signals
   signal clk          : std_logic;
   signal reset        : std_logic;
   
   -- UUT input signals
   signal port_halt    : std_logic;
   signal driver_done  : std_logic;   


   -- UUT output signals
   signal RST_n        : std_logic;
   signal HALT         : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                   program driver
   -- -------------------------------------------------------------------------
   uut: entity work.HALT_MONITOR
      port map (
         CLK         => clk,
         RESET       => reset,
         port_halt   => port_halt,
         RST_n       => RST_n, 
         HALT        => HALT,
         DRIVER_DONE => driver_done
      );

   -- CLK generator
   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;
   
   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process

   begin
   
      port_halt   <= '0';
      driver_done <= '0';

      -- program driver finished loading memory
      wait for 40 ns;
      driver_done <= '1';

      -- processor finished computation
      wait for 40 ns;
      port_halt <= '1';

--      report "signal HALT is " & std_logic'image(HALT) & " at time " & time'image(now);

      wait;

  end process tb; 
   
end architecture behavioral;
