--
-- dual_dec_8b10b_tb.vhd: Testbench for dual-port 8b/10b decoder
-- Copyright (C) 2003 CESNET
-- Author(s): Petr Mikusek <xmikus01@stud.fit.vutbr.cz>
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:
-- 1. Redistributions of source code must retain the above copyright
--    notice, this list of conditions and the following disclaimer.
-- 2. Redistributions in binary form must reproduce the above copyright
--    notice, this list of conditions and the following disclaimer in
--    the documentation and/or other materials provided with the
--    distribution.
-- 3. Neither the name of the Company nor the names of its contributors
--    may be used to endorse or promote products derived from this
--    software without specific prior written permission.
--
-- This software is provided ``as is'', and any express or implied
-- warranties, including, but not limited to, the implied warranties of
-- merchantability and fitness for a particular purpose are disclaimed.
-- In no event shall the company or contributors be liable for any
-- direct, indirect, incidental, special, exemplary, or consequential
-- damages (including, but not limited to, procurement of substitute
-- goods or services; loss of use, data, or profits; or business
-- interruption) however caused and on any theory of liability, whether
-- in contract, strict liability, or tort (including negligence or
-- otherwise) arising in any way out of the use of this software, even
-- if advised of the possibility of such damage.
--
-- $Id$
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_textio.all;

library STD;
use STD.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

component dual_dec_8b10b
   port (
      CLK0      : in  std_logic;
      RESET0    : in  std_logic;
      DIN0      : in  std_logic_vector(9 downto 0);
      DOUT0     : out std_logic_vector(7 downto 0);
      K0        : out std_logic;
      INVALID0  : out std_logic;

      CLK1      : in  std_logic;
      RESET1    : in  std_logic;
      DIN1      : in  std_logic_vector(9 downto 0);
      DOUT1     : out std_logic_vector(7 downto 0);
      K1        : out std_logic;
      INVALID1  : out std_logic
   );
end component;

   signal CLK0      : std_logic := '0';
   signal RESET0    : std_logic := '1';
   signal DIN0      : std_logic_vector(9 downto 0) := (others => '0');
   signal DOUT0     : std_logic_vector(7 downto 0);
   signal K0        : std_logic;
   signal INVALID0  : std_logic;

   signal CLK1      : std_logic := '0';
   signal RESET1    : std_logic;
   signal DIN1      : std_logic_vector(9 downto 0) := (others => '0');
   signal DOUT1     : std_logic_vector(7 downto 0);
   signal K1        : std_logic;
   signal INVALID1  : std_logic;

   constant C_CLKPER0 : time := 8 ns;
   constant C_CLKPER1 : time := 3200 ps;

begin
   UUT: dual_dec_8b10b
   port map (
      CLK0 => CLK0, RESET0 => RESET0, DIN0 => DIN0, DOUT0 => DOUT0,
      K0 => K0, INVALID0 => INVALID0,

      CLK1 => CLK1, RESET1 => RESET1, DIN1 => DIN1, DOUT1 => DOUT1,
      K1 => K1, INVALID1 => INVALID1
   );

   CLK0 <= not CLK0 after C_CLKPER0/2;
   RESET0 <= '1', '0' after 1*C_CLKPER0;

   CLK1 <= not CLK1 after C_CLKPER1/2;
   RESET1 <= '1', '0' after 1*C_CLKPER1;

   P_TB0: process
      file infile : text is "dec0.dat";
      variable l : line;
      variable din : std_logic_vector(9 downto 0);

   begin
      wait for 1*C_CLKPER0;
      while not(endfile(infile)) loop
         readline(infile, l);
         read(l, din);
         DIN0 <= din;
         wait for C_CLKPER0;
      end loop;

      wait;
   end process;

   P_TB1: process
      file infile : text is "dec1.dat";
      variable l : line;
      variable din : std_logic_vector(9 downto 0);

   begin
      wait for 1*C_CLKPER1;
      while not(endfile(infile)) loop
         readline(infile, l);
         read(l, din);
         DIN1 <= din;
         wait for C_CLKPER1;
      end loop;

      wait;
   end process;

end behavioral;

