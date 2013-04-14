--  ---------------------------------------------------------
--  Hardware accelerated Functional Verification of Processor
--  ---------------------------------------------------------

--  \file   testbench.vhd
--  \date   08-04-2013
--  \brief  Testbench for program driver

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
   constant IN_DATA_WIDTH        : integer := 64;
   constant OUT_DATA_WIDTH       : integer := 32;

   constant clkper               : time := 10 ns; 
   constant reset_time           : time := 100 ns;

   -- signals
   signal clk                    : std_logic;
   signal reset                  : std_logic;
   
   -- UUT input signals
   signal driver_in_data         : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
   signal driver_in_rem          : std_logic_vector(2 downto 0);
   signal driver_in_sof_n        : std_logic;
   signal driver_in_sop_n        : std_logic;
   signal driver_in_eof_n        : std_logic;
   signal driver_in_eop_n        : std_logic;
   signal driver_in_src_rdy_n    : std_logic;
   signal driver_in_dst_rdy_n    : std_logic;
   
   -- UUT output signals
   signal driver_out_d0          : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal driver_out_dbg_mode    : std_logic;
   signal driver_out_wa0         : std_logic_vector(18 downto 0);
   signal driver_out_we0         : std_logic;
   signal driver_out_wsc0        : std_logic_vector(2 downto 0);
   signal driver_out_wsi0        : std_logic_vector(1 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                   program driver
   -- -------------------------------------------------------------------------
   uut: entity work.PROGRAM_DRIVER
      generic map (
         IN_DATA_WIDTH     => IN_DATA_WIDTH,
         OUT_DATA_WIDTH    => OUT_DATA_WIDTH
      )
      port map (
         CLK               => clk,
         RESET             => reset,

         RX_DATA           => driver_in_data,
         RX_REM            => driver_in_rem,
         RX_SOF_N          => driver_in_sof_n,
         RX_SOP_N          => driver_in_sop_n,
         RX_EOP_N          => driver_in_eop_n,
         RX_EOF_N          => driver_in_eof_n,
         RX_SRC_RDY_N      => driver_in_src_rdy_n,
         RX_DST_RDY_N      => driver_in_dst_rdy_n,
         
         D0                => driver_out_d0,
         dbg_mode_mem      => driver_out_dbg_mode,
         WA0               => driver_out_wa0,
         WE0               => driver_out_we0,
         WSC0              => driver_out_wsc0,
         WSI0              => driver_out_wsi0

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
   
      wait for reset_time; 

      wait for 50 ns;

      wait until rising_edge(clk);

      driver_in_data  <= X"1111111122222222";
      driver_in_rem   <= "111";
      driver_in_sof_n <= '0';
      driver_in_eof_n <= '1';
      driver_in_sop_n <= '0';
      driver_in_eop_n <= '1';
      driver_in_src_rdy_n <= '0';
--      driver_in_dst_rdy_n <= '0';

      wait until rising_edge(clk);

      driver_in_data  <= X"3333333344444444";
      driver_in_rem   <= "111";
      driver_in_sof_n <= '1';
      driver_in_eof_n <= '1';
      driver_in_sop_n <= '1';
      driver_in_eop_n <= '1';
      driver_in_src_rdy_n <= '0';
--      driver_in_dst_rdy_n <= '0';

      wait until rising_edge(clk);

      driver_in_data  <= X"5555555566666666";
      driver_in_rem   <= "111";
      driver_in_sof_n <= '1';
      driver_in_eof_n <= '0';
      driver_in_sop_n <= '1';
      driver_in_eop_n <= '0';
      driver_in_src_rdy_n <= '0';
--      driver_in_dst_rdy_n <= '0';


     wait;
      
  end process tb; 
   
end architecture behavioral;
