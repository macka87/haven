-- signals.fdo: Include file with signals
-- Copyright (C) 2006 CESNET
-- Author: Jan Kastil <xkasti00@stud.fit.vutbr.cz>
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


--This testbench provides you with several test mode,which is available
--throught choosing TestType.
-- TestType = 1 will full the fifo, then will read it all. This will be repeat for ever (block size are set to 4)
-- TestType = 2 will do the same as 1, but in this options, fifo will be used as variable size (end block is generated after all 4 numbers are writen)

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

use work.math_pack.all;
use work.fifo_pkg.all;
entity testbench is

end testbench;

architecture behavioral of testbench is

--Constant for memory settings
constant Itm : integer := 16;
constant Adrs : integer := 20;
constant lat : integer := 1;  --Tested latency
constant TestType : integer := 1;

signal clkw : std_logic;
signal clkr : std_logic;
signal WriteEn : std_logic;
signal DataIn :std_logic_vector(Adrs-1 downto 0);
signal ReadEn : std_logic;
signal DataOut :std_logic_vector(Adrs-1 downto 0);
signal DataValid : std_logic;
signal Emt :std_logic;
signal Fl: std_logic;
signal Stat: std_logic_vector(log2(itm)-1 downto 0);
signal BlEnd: std_logic;
signal Dis1:std_logic;
signal Dis2:std_logic;
signal BlReady:std_logic;
signal BlFin:std_logic;
signal Reset:std_logic;

signal RW :  std_logic;
--Constant for tesbench
constant period1 : time := 20 ns; --Period for write clock
constant period2 : time := 15 ns; --Period for read clock
constant reset_time : time := 100 ns; --How long will be reset active

begin
--Generatin Reset
gen_reset: process
begin
   Reset <= '1';
   wait for reset_time;
   Reset <= '0';
   wait;
end process;
--Generating clocks
clk_gen : process 
begin
    clkw <= '1';
    wait for period1/2;
    clkw <= '0';
    wait for period1/2;
end process clk_gen;

clk_gen1 : process
begin
    clkr <= '1';
    wait for period2/2;
    clkr <= '0';
    wait for period2/2;
end process clk_gen1;


RW_GEN: process
begin
  wait until reset='0';
  wait for period1;
  for i in 3000 downto 0 loop
  RW <= '0';
  wait until fl='1';
  RW <= '1';
  wait until emt='1';
  RW <= '0';
  end loop;
end process;
   
--Generating tests
testW_WE: process
begin
  wait until reset = '0';
  wait for period1;
wait for 5 ns;
WE_C: for i in 3000 downto 0 loop
  WriteEn <=  RW;
  wait for period1 /2;
  WriteEn <= not RW;
  wait for period1 /2;
end loop;
end process;

TestW: process
variable DataInV : integer := 3;
begin
   BlEnd <='0';
  DataIn <= conv_std_logic_vector(5,Adrs);
  wait until (Reset = '0');
  wait for 7 ns;
  GC: for i in 3000 downto 0 loop
   DataInV := DataInV + 1;
   DataIn <= conv_std_logic_vector(DataInV, Adrs);
   wait for period1;
   DataInV := DataInV + 1;
   DataIn <= conv_std_logic_vector(DataInV, Adrs);
   wait for period1;
   DataInV := DataInV + 1;
   DataIn <= conv_std_logic_vector(DataInV, Adrs);
   wait for period1;
   BlEnd <= '1';
   DataInV := DataInV + 1;
   DataIn <= conv_std_logic_vector(DataInV, Adrs);
   wait for period1;
   BlEnd <= '0';
   end loop;
end process;

TestR: process
begin
   wait for 1000 ns;
   CYKGEN: for i in 1000 downto 0 loop
   ReadEn <= '0';
   wait for period2;
   ReadEn <= RW;
   wait for period2;
   ReadEn <= '0';
   wait for period2;
   wait for period2;
   end loop;
   ReadEn <= '0';
   wait;
end process;

Dis1Gen: process
begin
  Dis1<='0';
  wait for 195 ns;
  --Dis1<= '1';
  wait for period1;
  Dis1 <= '0';
  wait;
end process;

Dis2Gen: process
begin
   Dis2<='0';
   wait for 900 ns;
   --Dis2<='1';
   wait for period2;
   wait for 5 ns;
   Dis2 <='0';
   wait;
end process;

   uut : entity work.fifo_async_blocka
      generic map (
         items => Itm,
	      item_width =>Adrs,
	      latency =>lat,
	      mem_type => LUT,
	      block_type => variable_size,
	      block_size => 4,
	      discard => ReadDiscard,
	      prefetch =>true 
     )
      port map (
         WR_CLK => clkw,
         WR => WriteEn,
	 DI => DataIn,

	 RD_CLK =>clkr,
	 RD =>ReadEn,
	 DO =>DataOut,
	 DO_DV => DataValid,

	 EMPTY => Emt,
	 FULL => Fl,
	 STATUS => Stat,

	 BLK_END => BlEnd,
	 WR_DISCARD => Dis1,
	 RD_DISCARD =>Dis2,
	 BLK_READY => BlReady,
	 BLK_FINISH =>BlFin,
	 RESET => Reset
   );

end architecture;
