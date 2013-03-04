-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use ieee.math_real.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   -- constants declarations
   ----------------------------------------------------------------------------
   constant SIZE_WIDTH        : integer := 32;
   constant DATA_WIDTH        : integer := 64;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal unit_data_size         : std_logic_vector(SIZE_WIDTH-1 downto 0);
   signal unit_data_size_vld     : std_logic;
   signal unit_data_size_req     : std_logic;

   signal unit_data_rem          : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal unit_data_complete     : std_logic;
   signal unit_data_rdy          : std_logic;
   signal unit_data_take         : std_logic;
   
   signal reg_rand_bit           : std_logic;   

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL_REG_PROC_UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.DATA_PROC_UNIT
      generic map (
         SIZE_WIDTH        => SIZE_WIDTH,
         DATA_WIDTH        => DATA_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- DATA_SIZE_PROC_UNIT interface
         DATA_SIZE          => unit_data_size,
         DATA_SIZE_VLD      => unit_data_size_vld,
         DATA_SIZE_REQ      => unit_data_size_req,
      
         -- output interface
         DATA_COMPLETE      => unit_data_complete,
         DATA_REM           => unit_data_rem,
         DATA_RDY           => unit_data_rdy,
         DATA_TAKE          => unit_data_take
      );

   -- ----------------------------------------------------

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

   -- random bit register for the take signal
   reg_rand_bit_p: process(clk)
      variable seed1, seed2: positive;     -- Seed values for random generator
      variable rand: real;                 -- Random real-number value in range 0 to 1.0
   begin
      if (rising_edge(clk)) then
         UNIFORM(seed1, seed2, rand);
         if (rand > 0.5) then
            reg_rand_bit <= '0';
         else
            reg_rand_bit <= '1';
         end if;
      end if;
   end process;

   unit_data_take <= reg_rand_bit AND unit_data_rdy;

   -- the testbench
   tb: process
   begin
   
      wait for reset_time; 
      wait until rising_edge(clk);
   
      -- initialization 
      unit_data_size     <=  X"00000000";
      unit_data_size_vld <= '0';
      wait until rising_edge(clk);

      -- send the data
      unit_data_size     <=  X"00000020";
      unit_data_size_vld <= '1';
      wait until rising_edge(clk); 
      unit_data_size_vld <= '0';

      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      
      unit_data_size     <=  X"00000015";
      unit_data_size_vld <= '1';
      wait until rising_edge(clk); 
      unit_data_size     <=  X"00000037";
      unit_data_size_vld <= '1';
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      wait until rising_edge(clk); 
      unit_data_size_vld <= '0';

      wait;
   end process;
end architecture behavioral;
