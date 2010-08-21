-- TestBench Template

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

ENTITY testbench IS
END testbench;


architecture beh of testbench is
signal CLK: std_logic; --hodiny
signal RESET: std_logic;  --externi reset
signal DATA: std_logic_vector(15 downto 0);
signal DATAOUT: std_logic_vector(15 downto 0);
signal PHYDATA: std_logic; --vystup do phyteru
signal ADR: std_logic_vector(1 downto 0);
signal EN: std_logic;  -- enable = 1
signal RW: std_logic;
signal RDY: std_logic;

component mx is
 port (
  -------------- clock and reset ----------------
  CLK: in std_logic; --clock
  RESET: in std_logic;  --external reset

  ---------ports on  LBConn_mem -----------------
  DATA: in std_logic_vector(15 downto 0);
  DATAOUT: out std_logic_vector(15 downto 0);
  ADR: in std_logic_vector(1 downto 0);  -- 16#001# = head reg, 16#010#= data reg
  EN: in std_logic;  -- enable = 1	=> prisla data
  RW: in std_logic;	 -- chce psat ci cist
  RDY: in std_logic;   -- az chcem dat do LB tak na 1..

  ----------output to phyter ------------------
  PHYDATA: inout std_logic
);
end component mx;

begin
UUT : mx
port map (
CLK => CLK, RESET => RESET,
DATA => DATA, PHYDATA =>PHYDATA,DATAOUT=>DATAOUT,
ADR => ADR, EN => EN,RW => RW, RDY => RDY
);


-- LCLKF clock generator
clkgen : process
begin
   clk <= '1';
   wait for 50 ns;
   clk <= '0';
   wait for 50 ns;
end process;


process
begin
 PHYDATA<='Z';
 Reset<='1';
 wait for 100 ns;
 Reset<='0';
 wait for 50 ns;
 Data<="0110101101100101";
 RW<='1';
 En<='1';
 Adr<="01";
 wait for 50 ns; --first bit send
 wait for 1300 ns; --last bit send
 Adr<="10";
 wait for 100 ns; --last bit recieved
 wait for 100 ns;
 wait for 20 ns;
 PHYDATA<='0';
 wait for 100 ns;
 PHYDATA<='1';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='1';	 wait for 100 ns;
 PHYDATA<='1';	 wait for 100 ns;
 PHYDATA<='1';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='1';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='1';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='0';	 wait for 100 ns;
 PHYDATA<='1';	 wait for 100 ns;
 PHYDATA<='Z';
 wait for 3000 ns;
end process;
end beh;
