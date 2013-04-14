--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   testbench.vhd
--  \date   11-04-2013
--  \brief  Testbench for portout output signal of processor

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

   -- constants
   constant IN_DATA_WIDTH        : integer := 32;
   constant OUT_DATA_WIDTH       : integer := 64;

   constant clkper               : time := 10 ns; 
   constant reset_time           : time := 100 ns;

   -- signals
   signal clk                    : std_logic;
   signal reset                  : std_logic;

   signal port_error   : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
   signal port_output  : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
   signal port_output_en : std_logic;

   signal TX_DATA      : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal TX_REM       : std_logic_vector(2 downto 0);
   signal TX_SRC_RDY_N : std_logic;
   signal TX_DST_RDY_N : std_logic;
   signal TX_SOP_N     : std_logic;
   signal TX_EOP_N     : std_logic;
   signal TX_SOF_N     : std_logic;
   signal TX_EOF_N     : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                   program driver
   -- -------------------------------------------------------------------------
   uut: entity work.PORTOUT_MONITOR
      generic map (
         IN_DATA_WIDTH     => IN_DATA_WIDTH,
         OUT_DATA_WIDTH    => OUT_DATA_WIDTH
      )
      port map (
         CLK          => clk,
         RESET        => reset,

         -- inputs
         port_error     => port_error,
         port_output    => port_output,
         port_output_en => port_output_en,

         -- outputs
         TX_DATA      => TX_DATA,
         TX_REM       => TX_REM,
         TX_SRC_RDY_N => TX_SRC_RDY_N,
         TX_DST_RDY_N => TX_DST_RDY_N,
         TX_SOP_N     => TX_SOP_N,
         TX_EOP_N     => TX_EOP_N,
         TX_SOF_N     => TX_SOF_N,
         TX_EOF_N     => TX_EOF_N
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

      wait for 10 ns;
   
      TX_DST_RDY_N   <= '0';
      port_output_en <= '1';
      port_output    <= X"22222222";

      wait for 10 ns;

--      report "signal xy is " & std_logic'image(xy) & " at time " & time'image(now);

  end process tb; 
   
end architecture behavioral;
