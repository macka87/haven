-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use IEEE.numeric_std.all;
use IEEE.math_real.all;

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
   constant DATA_WIDTH          : integer := 64;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;
   
   constant RUN_REG_ADDR      : std_logic_vector(31 downto 0) := X"00000000";
   constant SEED_REG_ADDR     : std_logic_vector(31 downto 0) := X"00000004";

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal mi_dwr              : std_logic_vector(31 downto 0);
   signal mi_addr             : std_logic_vector(31 downto 0);
   signal mi_rd               : std_logic;
   signal mi_wr               : std_logic;
   signal mi_be               : std_logic_vector(3 downto 0);
   signal mi_drd              : std_logic_vector(31 downto 0);
   signal mi_ardy             : std_logic;
   signal mi_drdy             : std_logic;
   
   signal rnd_val             : std_logic;
   signal rnd_num             : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rnd_run             : std_logic;
  
   signal reg_rand_bit        : std_logic;
   
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   -- -------------------------------------------------------------------------
   --                          RANDOM GENERATOR
   -- -------------------------------------------------------------------------
   uut: entity work.RAND_GEN
   generic map (
      OUTPUT_WIDTH           => DATA_WIDTH
   )
   port map (
      CLK               => CLK,
      RESET             => RESET,
      
      -- MI32 interface
      MI_DWR            => mi_dwr, 
      MI_ADDR           => mi_addr,
      MI_RD             => mi_rd,
      MI_WR             => mi_wr,
      MI_BE             => mi_be,
      MI_DRD            => mi_drd,
      MI_ARDY           => mi_ardy,
      MI_DRDY           => mi_drdy,
    
      -- Output Interface
      RND_VAL           => rnd_val,
      RND_NUM           => rnd_num,
      RND_RUN           => rnd_run
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
   
   -- reset generator
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

   --rnd_run   <= reg_rand_bit;
   rnd_run   <= '1';

   -- the testbench process
   tb: process
   begin

      -- initialisation of signals
      mi_rd    <= '0';
      mi_wr    <= '0';
      mi_be    <= "1111";
      mi_dwr   <= (others => '0');
      mi_addr  <= X"DEADBEEF";

      wait for reset_time; 
      wait until rising_edge(clk);

      -- initialization of registers

      mi_wr    <= '1';

      -- -------------- SEED -----------------
      mi_addr  <= SEED_REG_ADDR;
      mi_dwr   <= X"01234567";
      wait until rising_edge(clk);

      -- -------------- RUN ------------------
      mi_addr  <= RUN_REG_ADDR;
      mi_dwr   <= X"00000001";
      wait until rising_edge(clk);

      mi_wr    <= '0';

      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);

      -- -------------- RUN ------------------
      mi_addr  <= RUN_REG_ADDR;
      mi_dwr   <= X"00000000";
      mi_wr    <= '1';
      wait until rising_edge(clk);
      mi_wr    <= '0';

      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);
      wait until rising_edge(clk);

      -- -------------- RUN ------------------
      mi_addr  <= RUN_REG_ADDR;
      mi_dwr   <= X"00000001";
      mi_wr    <= '1';
      wait until rising_edge(clk);
      mi_wr    <= '0';
      wait;
   end process;
end architecture behavioral;

