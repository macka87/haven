library ieee;
use ieee.std_logic_1164.all;

entity testbench is
end entity testbench;

architecture tb_arch of testbench is
  -- perioda hodin 
  constant clk_period   : time := 20 ns;
  constant reset_time   : time := 100 ns;
  constant data_width   : integer := 8;
  
  -- prepajacie signaly
  signal clk         : std_logic;
  signal rst         : std_logic;
  signal act         : std_logic;
  signal op          : std_logic_vector(3 downto 0);
  signal movi        : std_logic_vector(1 downto 0);
  signal reg_a       : std_logic_vector(data_width-1 downto 0);
  signal reg_b       : std_logic_vector(data_width-1 downto 0);
  signal mem         : std_logic_vector(data_width-1 downto 0);
  signal imm         : std_logic_vector(data_width-1 downto 0);
  signal alu_rdy     : std_logic;
  signal ex_alu      : std_logic_vector(data_width-1 downto 0);
  signal ex_alu_vld  : std_logic;

begin
  -- instancia testovanej komponenty
  UUT : entity work.ALU_ENT
  port map( CLK         => clk,
            RST         => rst,
            ACT         => act,
            OP          => op,
            MOVI        => movi,
            REG_A       => reg_a,
            REG_B       => reg_b,
            MEM         => mem,
            IMM         => imm, 
            ALU_RDY     => alu_rdy,
            EX_ALU      => ex_alu,
            EX_ALU_VLD  => ex_alu_vld
  );

  -- generovanie hodinoveho signalu 
  clk_gen :  process 
  begin  
    clk <='1';
    wait for clk_period/2;
    clk <='0';
    wait for clk_period/2;
  end process clk_gen;
  
  resetgen: process
   begin
      rst <= '1';
      wait for reset_time;
      rst <= '0';
      wait;
   end process;

  -- generovanie vstupov
  behaviour : process
  begin
    
    act    <= '0';
    op     <= "0000"; 
    movi   <= "00";
    reg_a  <= "00000000";
    reg_b  <= "00000000";
    mem    <= "00000000";
    imm    <= "00000000";
    
    wait for 8*clk_period;
    
    -- pociatocne hodnoty vstupov
    act    <= '1';
    op     <= "0010"; 
    movi   <= "00";
    reg_a  <= "11111111";
    reg_b  <= "11111111";
    mem    <= "00000100";
    imm    <= "00001000";
    
    wait for 10*clk_period;
    act    <= '0';  
    
    wait for clk_period;
    
    -- pociatocne hodnoty vstupov
    act    <= '1';
    op     <= "0010"; 
    movi   <= "00";
    reg_a  <= "00000001";
    reg_b  <= "00000111";
    mem    <= "00000100";
    imm    <= "00001000";
    wait for 10*clk_period;
    wait;
  end process behaviour; 
   
end architecture tb_arch;
