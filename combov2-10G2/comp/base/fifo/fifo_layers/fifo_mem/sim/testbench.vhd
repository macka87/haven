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
constant Itm : integer := 50;
constant Adrs : integer := 20;
constant lat : integer := 3;  --Tested latency


signal clkw : std_logic;
signal clkr : std_logic;
signal reset: std_logic;
signal Write_Enabled : std_logic;
signal Writing_Adress : std_logic_vector(log2(Itm)-1 downto 0);
signal Adress : std_logic_vector(log2(Itm)-1 downto 0);
signal Adress1 : std_logic_vector(log2(Itm)-1 downto 0);
signal Reading_Adress : std_logic_vector(log2(Itm)-1 downto 0);
signal DataIn : std_logic_vector(Adrs-1 downto 0);
signal Read_Enable: std_logic;
signal DataOut : std_logic_vector(Adrs-1 downto 0);
signal Data_Valid: std_logic;
signal DataOut1 : std_logic_vector(Adrs-1 downto 0);
signal Data_Valid1 : std_logic;
signal pipe_en : std_logic;
signal pipe_en1 : std_logic;

--Constant for tesbench
constant period1 : time := 20 ns; --Period for write clock
constant period2 : time := 15 ns; --Period for read clock
constant reset_time : time := 101 ns; --How long will be reset active

begin

--Generating PIPE_EN

Pipe_en_gen: process
begin
   pipe_en <= '1';
   pipe_en1 <= '1';
   wait for period2;
   pipe_en <= '0';
   pipe_en1 <= '0';
   wait for period2;
   wait for 1 ns;
end process;
--Generating reset
Reset_gen : process
begin
   reset <= '1';
   wait for reset_time;
   reset <= '0';
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

--Importing FIFO memory
   uut : entity work.fifo_mem
      generic map (
         items => Itm,
         item_width =>Adrs,
         latency =>lat,
         mem_type => LUT
     )
      port map (
         CLKW => clkw,
         WRITE_EN => Write_Enabled,
         WRITE_ADDR =>Writing_Adress,
         DI => DataIn,
       PIPE_EN => pipe_en,
         CLKR => clkr,
         READ_EN => Read_Enable,
         RE_ADDR => Reading_Adress,
         DO => DataOut,
         DO_DV => Data_Valid,
         RESET => reset,
       ADDR_OUT => Adress
      );
   uut1 : entity work.fifo_mem
      generic map (
         item_width => Adrs,
         items =>Itm,
    latency => lat,
    mem_type => BRAM
    )
      port map (
         CLKW =>clkw,
    WRITE_EN => Write_Enabled,
    WRITE_ADDR => Writing_Adress,
    DI => DataIn,
    PIPE_EN => pipe_en1,
    CLKR => clkr,
    READ_EN => Read_Enable,
    RE_ADDR => Reading_Adress,
    DO => DataOut1,
    DO_DV => Data_Valid1,
    RESET => reset,
    ADDR_OUT =>Adress1
      );
read_write: process
   variable Adr : integer := 0;
   variable Number : integer := 2356;
begin
   Read_Enable <= '0';
   Write_Enabled <= '0';

   Writing_Adress <= (others => '0');
   Reading_Adress <= (others => '0');
   DataIn <= (others => '0');

   wait for 2*reset_time;
 --  wait until clkr= '1' and clkr'event;

   Writing_Adress <= conv_std_logic_vector(Adr,LOG2(Itm));
   DataIn <= conv_std_logic_vector(Number, Adrs);

   wait for period1;
   --wait until clkr= '1' and clkr'event;
   
   Write_Enabled <= '1';

   wait for period1;
 --  wait until clkr= '1' and clkr'event;
   
   Write_Enabled <= '0';

   wait for period1;
--   wait until clkr= '1' and clkr'event;
   
   DataIn <= (others => 'X');

   wait for period1;
--   wait until clkr= '1' and clkr'event;
   
   Reading_Adress <= conv_std_logic_vector(Adr,LOG2(Itm));

   wait for period1;
--   wait until clkr= '1' and clkr'event;
   
   Read_Enable <= '1';

   wait for period2;
--   wait until clkr= '1' and clkr'event;
   
   wait for period2;
--   wait until clkr= '1' and clkr'event;
   
   wait for period2;
--   wait until clkr= '1' and clkr'event;
   
   Read_Enable <= '0';

   wait for period2;
--   wait until clkr= '1' and clkr'event;
   
   Adr := Adr +1;
   Number := Number +135;
end process;

end architecture;
