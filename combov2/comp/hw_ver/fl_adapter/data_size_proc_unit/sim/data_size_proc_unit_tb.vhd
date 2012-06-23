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
   constant IN_DATA_WIDTH         : integer := 32;
   constant OUT_DATA_WIDTH        : integer := 12;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal unit_part_size         : std_logic_vector(IN_DATA_WIDTH-1 downto 0);
   signal unit_part_size_vld     : std_logic;
   signal unit_part_complete     : std_logic;

   signal unit_data_size         : std_logic_vector(OUT_DATA_WIDTH-1 downto 0);
   signal unit_data_size_vld     : std_logic;
   signal unit_data_request      : std_logic;
      
   signal reg_rand_bit                : std_logic;

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL_REG_PROC_UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.DATA_SIZE_PROC_UNIT
      generic map (
         IN_DATA_WIDTH        => IN_DATA_WIDTH,
         OUT_DATA_WIDTH       => OUT_DATA_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- input interface
         PART_SIZE         => unit_part_size, 
         PART_SIZE_VLD     => unit_part_size_vld,
         PART_COMPLETE     => unit_part_complete,

         -- output interface
         DATA_SIZE         => unit_data_size,
         DATA_SIZE_VLD     => unit_data_size_vld,
         DATA_REQUEST      => unit_data_request
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

   unit_data_request <= reg_rand_bit AND unit_data_size_vld;

   -- the testbench
   tb: process
   begin
   
      wait for reset_time; 
      wait until rising_edge(clk);
   
      -- initialization 
      unit_part_size     <= X"00000000";
      unit_part_size_vld <= '0';
      wait until rising_edge(clk);
      
      -- sending data
      unit_part_size     <= X"0000000A";
      unit_part_size_vld <= '1';
      wait until rising_edge(clk);

      unit_part_size     <= X"000000A0";
      unit_part_size_vld <= '1';
      wait until rising_edge(clk);
      unit_part_size_vld <= '0';

      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);

      unit_part_size     <= X"00000A00";
      unit_part_size_vld <= '1';
      wait until rising_edge(clk);
      unit_part_size_vld <= '0';

      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);

      unit_part_size     <= X"0000A000";
      unit_part_size_vld <= '1';
      wait until rising_edge(clk);
      unit_part_size_vld <= '0';

--      unit_part_size     <= X"000000A0";
--      unit_part_size_vld <= '1';
--      if (unit_part_complete = '1') then
--         wait until rising_edge(clk);
--      else
--         while (NOT (unit_part_complete = '1')) loop
--            wait until rising_edge(clk);
--         end loop;
--      end if;
--      
--
--      unit_part_size     <= X"00000A00";
--      unit_part_size_vld <= '1';
--      if (unit_part_complete = '1') then
--         wait until rising_edge(clk);
--      else
--         while (NOT (unit_part_complete = '1')) loop
--            wait until rising_edge(clk);
--         end loop;
--      end if;
--
--      unit_part_size     <= X"0000A000";
--      unit_part_size_vld <= '1';
--      if (unit_part_complete = '1') then
--         wait until rising_edge(clk);
--      else
--         while (NOT (unit_part_complete = '1')) loop
--            wait until rising_edge(clk);
--         end loop;
--      end if;
--
--      unit_part_size     <= X"000A0000";
--      unit_part_size_vld <= '1';
--      if (unit_part_complete = '1') then
--         wait until rising_edge(clk);
--      else
--         while (NOT (unit_part_complete = '1')) loop
--            wait until rising_edge(clk);
--         end loop;
--      end if;

      wait;
   end process;
end architecture;
