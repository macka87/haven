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
   constant DATA_WIDTH        : integer := 64;
   constant PART_NUM_CNT_WIDTH: integer := 3;
   constant PART_SIZE_CNT_WIDTH:integer := 32;
   
   constant clkper            : time := 10 ns; 
   constant reset_time        : time := 100 ns;

   constant RUN_REG_ADDR      : std_logic_vector(31 downto 0) := X"00000000";
   constant TRANS_REG_ADDR    : std_logic_vector(31 downto 0) := X"00000004";
   constant PART_NUM_REG_ADDR : std_logic_vector(31 downto 0) := X"00000010";
   constant PART_SIZE_REG_ADDR: std_logic_vector(31 downto 0) := X"00000080";
   constant PART_REG_OFFSET   : integer := 16;
   constant PART_MASK_OFFSET  : integer := 0;
   constant PART_BASE_OFFSET  : integer := 4;
   constant PART_MAX_OFFSET   : integer := 8;

   -- signals declarations
   ----------------------------------------------------------------------------
   signal clk                 : std_logic;
   signal reset               : std_logic;
   
   -- UUT signals
   signal reg_proc_unit_mi_dwr   : std_logic_vector(31 downto 0);
   signal reg_proc_unit_mi_addr  : std_logic_vector(31 downto 0);
   signal reg_proc_unit_mi_rd    : std_logic;
   signal reg_proc_unit_mi_wr    : std_logic;
   signal reg_proc_unit_mi_be    : std_logic_vector(3 downto 0);
   signal reg_proc_unit_mi_drd   : std_logic_vector(31 downto 0);
   signal reg_proc_unit_mi_ardy  : std_logic;
   signal reg_proc_unit_mi_drdy  : std_logic;
   
   signal reg_proc_unit_gen_flow : std_logic_vector(DATA_WIDTH-1 downto 0);
   
   signal reg_proc_unit_part_size     : std_logic_vector(PART_SIZE_CNT_WIDTH-1 downto 0);
   signal reg_proc_unit_part_size_vld : std_logic;
   signal reg_proc_unit_part_size_take: std_logic;
   
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   REG_PROC_UNIT
   -- -------------------------------------------------------------------------
   uut: entity work.REG_PROC_UNIT
   generic map (
      DATA_WIDTH        => DATA_WIDTH,
      PART_NUM_CNT_WIDTH=> PART_NUM_CNT_WIDTH,
      PART_SIZE_CNT_WIDTH=>PART_SIZE_CNT_WIDTH
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
      PART_SIZE         => reg_proc_unit_part_size,
      PART_SIZE_VLD     => reg_proc_unit_part_size_vld,
      PART_SIZE_TAKE    => reg_proc_unit_part_size_take
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

   reg_proc_unit_gen_flow_p: process(clk)
   begin
      if (rising_edge(clk)) then
         if (reset = '1') then
            reg_proc_unit_gen_flow <= X"3A89DF04332C9AB1";
         else
            reg_proc_unit_gen_flow <=
               (reg_proc_unit_gen_flow(DATA_WIDTH-2 downto 0) & NOT reg_proc_unit_gen_flow(DATA_WIDTH-1))
               XOR reg_proc_unit_gen_flow;
         end if;
      end if;
   end process;

   tb: process
   begin

      -- initialisation of signals
      reg_proc_unit_mi_rd    <= '0';
      reg_proc_unit_mi_wr    <= '0';
      reg_proc_unit_mi_be    <= "1111";
      reg_proc_unit_mi_dwr   <= (others => '0');
      reg_proc_unit_mi_addr  <= X"DEADBEEF";


      wait for reset_time; 
      wait until rising_edge(clk);

      -- initialization of registers

      reg_proc_unit_mi_wr    <= '1';

      -- ----------- PARTS NUM --------------
      -- PARTS_NUM_MASK
      reg_proc_unit_mi_addr  <= PART_NUM_REG_ADDR + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000007";
      wait until rising_edge(clk);

      -- PARTS_NUM_BASE
      reg_proc_unit_mi_addr  <= PART_NUM_REG_ADDR + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000001";
      wait until rising_edge(clk);

      -- PARTS_NUM_MAX
      reg_proc_unit_mi_addr  <= PART_NUM_REG_ADDR + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000005";
      wait until rising_edge(clk);

      -- ----------- PART 0 -----------------
      -- PART0_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 0*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"0000000F";
      wait until rising_edge(clk);

      -- PART0_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 0*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000001";
      wait until rising_edge(clk);

      -- PART0_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 0*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"0000000A";
      wait until rising_edge(clk);

      -- ----------- PART 1 -----------------
      -- PART1_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 1*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"000000FF";
      wait until rising_edge(clk);

      -- PART1_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 1*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000010";
      wait until rising_edge(clk);

      -- PART1_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 1*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"000000A0";
      wait until rising_edge(clk);

      -- ----------- PART 2 -----------------
      -- PART2_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 2*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000FFF";
      wait until rising_edge(clk);

      -- PART2_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 2*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000100";
      wait until rising_edge(clk);

      -- PART2_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 2*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00000A00";
      wait until rising_edge(clk);

      -- ----------- PART 3 -----------------
      -- PART3_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 3*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"0000FFFF";
      wait until rising_edge(clk);

      -- PART3_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 3*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00001000";
      wait until rising_edge(clk);

      -- PART3_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 3*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"0000A000";
      wait until rising_edge(clk);

      -- ----------- PART 4 -----------------
      -- PART4_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 4*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"000FFFFF";
      wait until rising_edge(clk);

      -- PART4_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 4*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00010000";
      wait until rising_edge(clk);

      -- PART4_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 4*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"000A0000";
      wait until rising_edge(clk);

      -- ----------- PART 5 -----------------
      -- PART5_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 5*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00FFFFFF";
      wait until rising_edge(clk);

      -- PART5_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 5*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00100000";
      wait until rising_edge(clk);

      -- PART5_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 5*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"00A00000";
      wait until rising_edge(clk);

      -- ----------- PART 6 -----------------
      -- PART6_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 6*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"0FFFFFFF";
      wait until rising_edge(clk);

      -- PART6_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 6*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"01000000";
      wait until rising_edge(clk);

      -- PART6_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 6*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"0A000000";
      wait until rising_edge(clk);

      -- ----------- PART 7 -----------------
      -- PART7_MASK
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 7*PART_REG_OFFSET + PART_MASK_OFFSET;
      reg_proc_unit_mi_dwr   <= X"FFFFFFFF";
      wait until rising_edge(clk);

      -- PART7_BASE
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 7*PART_REG_OFFSET + PART_BASE_OFFSET;
      reg_proc_unit_mi_dwr   <= X"10000000";
      wait until rising_edge(clk);

      -- PART7_MAX
      reg_proc_unit_mi_addr  <= PART_SIZE_REG_ADDR + 7*PART_REG_OFFSET + PART_MAX_OFFSET;
      reg_proc_unit_mi_dwr   <= X"A0000000";
      wait until rising_edge(clk);

      wait;
   end process;
end architecture behavioral;
