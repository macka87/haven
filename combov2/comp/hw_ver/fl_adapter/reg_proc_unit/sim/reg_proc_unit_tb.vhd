-- Copyright (C) 2012 
-- Author(s): Marcela Simkova <isimkova@fit.vutbr.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
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
   constant DATA_WIDTH        : integer := 32;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal reg_proc_unit_mi_dwr   : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_proc_unit_mi_addr  : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_proc_unit_mi_rd    : std_logic;
   signal reg_proc_unit_mi_wr    : std_logic;
   signal reg_proc_unit_mi_be    : std_logic_vector(3 downto 0);
   signal reg_proc_unit_mi_drd   : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_proc_unit_mi_ardy  : std_logic;
   signal reg_proc_unit_mi_drdy  : std_logic;
   
   signal reg_proc_unit_gen_flow : std_logic_vector(DATA_WIDTH-1 downto 0);
   
   signal reg_proc_unit_parts_num     : std_logic_vector(2 downto 0);
   signal reg_proc_unit_parts_num_vld : std_logic;
   signal reg_proc_unit_part_size     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_proc_unit_part_size_vld : std_logic;
   
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL_REG_PROC_UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.FL_REG_PROC_UNIT
      generic map (
         DATA_WIDTH        => DATA_WIDTH
      )
      port map (
         CLK               => CLK,
         RESET             => RESET,
         
         -- MI32 interface
         MI_DWR            => reg_proc_unit_mi_dwr, 
         MI_ADDR           => reg_proc_unit_mi_addr,
         MI_RD             => reg_proc_unit_mi_rd,
         MI_WR             => reg_proc_unit_mi_wr,
         MI_BE             => reg_proc_unit_mi_be,
         MI_DRD            => reg_proc_unit_mi_drd,
         MI_ARDY           => reg_proc_unit_mi_ardy,
         MI_DRDY           => reg_proc_unit_mi_drdy,
       
         -- Generator interface
         GEN_FLOW          => reg_proc_unit_gen_flow,
      
         -- Output interface
         PARTS_NUM         => reg_proc_unit_parts_num,
         PARTS_NUM_VLD     => reg_proc_unit_parts_num_vld,
         PART_SIZE         => reg_proc_unit_part_size,
         PART_SIZE_VLD     => reg_proc_unit_part_size_vld  
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

   tb: process

   begin
   
      wait for reset_time; 
      wait until rising_edge(clk);
   
      -- initialization of registers
      
      -- ----------- PART 0 -----------------
      -- PART0_MASK
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      reg_proc_unit_mi_addr  <= X"00000000";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"44444444";
      wait until rising_edge(clk);
      
      -- PART0_BASE
      reg_proc_unit_mi_dwr   <= X"00000001";
      reg_proc_unit_mi_addr  <= X"00000004";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"55555555";
      wait until rising_edge(clk);
      
      -- PART0_MAX
      reg_proc_unit_mi_dwr   <= X"0000FFFF";
      reg_proc_unit_mi_addr  <= X"00000008";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"66666666";
      wait until rising_edge(clk);
      
      -- ----------- PART 1 -----------------
      -- PART1_MASK
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      reg_proc_unit_mi_addr  <= X"00000010";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"77777777";
      wait until rising_edge(clk);
      
      -- PART1_BASE
      reg_proc_unit_mi_dwr   <= X"00000001";
      reg_proc_unit_mi_addr  <= X"00000014";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"88888888";
      wait until rising_edge(clk);
      
      -- PART1_MAX
      reg_proc_unit_mi_dwr   <= X"00000FFF";
      reg_proc_unit_mi_addr  <= X"00000018";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"99999999";
      wait until rising_edge(clk);
      
      -- ----------- PART 2 -----------------
      -- PART2_MASK
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      reg_proc_unit_mi_addr  <= X"00000020";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"AAAAAAAA";
      wait until rising_edge(clk);
      
      -- PART2_BASE
      reg_proc_unit_mi_dwr   <= X"00000001";
      reg_proc_unit_mi_addr  <= X"00000024";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"BBBBBBBB";
      wait until rising_edge(clk);
      
      -- PART2_MAX
      reg_proc_unit_mi_dwr   <= X"000000FF";
      reg_proc_unit_mi_addr  <= X"00000028";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"CCCCCCCC";
      wait until rising_edge(clk);
      
      -- ----------- PART 3 -----------------
      -- PART3_MASK
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      reg_proc_unit_mi_addr  <= X"00000030";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"DDDDDDDD";
      wait until rising_edge(clk);
      
      -- PART3_BASE
      reg_proc_unit_mi_dwr   <= X"00000001";
      reg_proc_unit_mi_addr  <= X"00000034";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"EEEEEEEE";
      wait until rising_edge(clk);
      
      -- PART3_MAX
      reg_proc_unit_mi_dwr   <= X"0000000F";
      reg_proc_unit_mi_addr  <= X"00000038";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"FFFFFFFF";
      wait until rising_edge(clk);
      
      -- ----------- PART 4 -----------------
      -- PART4_MASK
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      reg_proc_unit_mi_addr  <= X"00000040";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"11111111";
      wait until rising_edge(clk);
      
      -- PART4_BASE
      reg_proc_unit_mi_dwr   <= X"00000001";
      reg_proc_unit_mi_addr  <= X"00000044";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"22222222";
      wait until rising_edge(clk);
      
      -- PART4_MAX
      reg_proc_unit_mi_dwr   <= X"0000FFFF";
      reg_proc_unit_mi_addr  <= X"00000048";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"33333333";
      wait until rising_edge(clk);
      
      -- ----------- PART 5 -----------------
      -- PART5_MASK
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      reg_proc_unit_mi_addr  <= X"00000050";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"44444444";
      wait until rising_edge(clk);
      
      -- PART5_BASE
      reg_proc_unit_mi_dwr   <= X"00000001";
      reg_proc_unit_mi_addr  <= X"00000054";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"55555555";
      wait until rising_edge(clk);
      
      -- PART5_MAX
      reg_proc_unit_mi_dwr   <= X"00000FFF";
      reg_proc_unit_mi_addr  <= X"00000058";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"66666666";
      wait until rising_edge(clk);
      
      -- ----------- PART 6 -----------------
      -- PART6_MASK
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      reg_proc_unit_mi_addr  <= X"00000060";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"77777777";
      wait until rising_edge(clk);
      
      -- PART6_BASE
      reg_proc_unit_mi_dwr   <= X"00000001";
      reg_proc_unit_mi_addr  <= X"00000064";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"88888888";
      wait until rising_edge(clk);
      
      -- PART6_MAX
      reg_proc_unit_mi_dwr   <= X"000000FF";
      reg_proc_unit_mi_addr  <= X"00000068";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"99999999";
      wait until rising_edge(clk);
      
      -- ----------- PARTS NUM --------------
      -- PARTS_NUM_MASK
      reg_proc_unit_mi_dwr   <= X"00000003";
      reg_proc_unit_mi_addr  <= X"00000070";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"11111111";
      wait until rising_edge(clk);
      
      -- PARTS_NUM_BASE
      reg_proc_unit_mi_dwr   <= X"00000000";
      reg_proc_unit_mi_addr  <= X"00000074";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"22222222";
      wait until rising_edge(clk);
      
      -- PARTS_NUM_MAX
      reg_proc_unit_mi_dwr   <= X"00000003";
      reg_proc_unit_mi_addr  <= X"00000078";
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '1';
      reg_proc_unit_mi_be    <= "0000";
      reg_proc_unit_gen_flow <= X"33333333";
      wait until rising_edge(clk);
      
      wait;
   end process;
end architecture behavioral;
