--DUT pre verifikaciu
--xbeles00
--ALU

--LIBRARY------------------------------------
library IEEE;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--ENTITY-------------------------------------
entity en_alu is
port (
  --reset aktivny v log 1
  RST       : IN  std_logic;
  --clock
  CLK       : IN  std_logic;
  --00: scitanie, 01: min(OPERAND_A,OPERAND_B), 10: OPERAND_A mod 2, 11: neplatne
  OPERACIA  : IN  std_logic_vector(1 downto 0);
  --<0,9)dec
  OPERAND_A : IN  std_logic_vector(3 downto 0);
  --lubovolne pre OPERACIA=10 inak <0,9)dec 
  OPERAND_B : IN  std_logic_vector(3 downto 0);
  --pre neplatne vstupy 11111
  VYSLEDOK  : OUT std_logic_vector(4 downto 0)
);
end en_alu;

--ARCHITECTURE-------------------------------
architecture behavioral of en_alu is

begin 
alu : process (CLK)
  begin
  if (CLK'event and CLK='1') then
    if (RST='1') then
      VYSLEDOK <= (others => '0');
    elsif (OPERACIA = "11" or (unsigned(OPERAND_A)) > 9) then
      VYSLEDOK <= (others => '1');
    elsif (OPERACIA = "10") then
      VYSLEDOK <= "00" & OPERAND_A(3 downto 1);
    elsif (unsigned(OPERAND_B) > 9) then
      VYSLEDOK <= (others => '1');
    elsif (OPERACIA = "00") then
      VYSLEDOK <= (('0'&unsigned(OPERAND_A)) + ('0'&unsigned(OPERAND_B)));
    else
      if (unsigned(OPERAND_A) < unsigned(OPERAND_B)) then
        VYSLEDOK <= '0'&OPERAND_A;
      else
        VYSLEDOK <= '0'&OPERAND_B;
      end if;
    end if;
  end if;    
end process;
 
end architecture;