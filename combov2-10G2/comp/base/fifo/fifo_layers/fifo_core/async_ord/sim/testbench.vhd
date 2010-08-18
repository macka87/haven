-- testbench.vhd: Testbench file
-- Copyright (C) 2006 CESNET
-- Author: Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
   constant MEM_TYPE    : mem_type := BRAM;
   constant ITEMCOUNT   : integer  := 4;
   constant ITEMSIZE    : integer  := 16;
   constant LAT         : integer  := 1;  --Tested latency
   constant PREFETCH    : boolean  := true;
   
   --Constants for tesbench
   constant PERIOD_R         : time := 20 ns; --Read clock period
   constant PERIOD_W         : time := 27 ns; --Write clock period
   constant RESET_TIME       : time := 100 ns; --Reset duration

   constant DELAY1           : time := 20 ns;
   constant DELAY2           : time := 80 ns;

   --Signals
   signal reset         : std_logic;
   signal clk_r         : std_logic;
   signal clk_w         : std_logic;
   signal WriteEn       : std_logic;
   signal DataIn        : std_logic_vector(ITEMSIZE-1 downto 0);
   signal ReadEn        : std_logic;
   signal DataOut       : std_logic_vector(ITEMSIZE-1 downto 0);
   signal DataValid     : std_logic;
   signal Empty         : std_logic;
   signal Full          : std_logic;
   signal Status        : std_logic_vector((log2(ITEMCOUNT)-1) downto 0);
   

   begin
 
   --Generating reset
   Reset_gen : process
      begin
      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';
      wait;
   end process;

   --Generating read clock
   clk_gen_r : process
   begin
      clk_r <= '1';
      wait for PERIOD_R/2;
      clk_r <= '0';
      wait for PERIOD_R/2;
   end process clk_gen_r;

   --Generating write clock
   clk_gen_w : process
   begin
      clk_w <= '1';
      wait for PERIOD_W/2;
      clk_w <= '0';
      wait for PERIOD_W/2;
   end process clk_gen_w;

   --Importing FIFO memory
   uut : entity work.fifo_async_ord
      generic map (
         MEM_TYPE => MEM_TYPE,
         LATENCY =>LAT,
         ITEMS => ITEMCOUNT,
         ITEM_WIDTH =>ITEMSIZE,
         PREFETCH => PREFETCH
      )
      port map (
         WR_CLK => clk_w,
         WR => WriteEn,
         DI => DataIn,

         RD_CLK => clk_r,
         RD => ReadEn,
         DO => DataOut,
         DO_DV => DataValid,

         EMPTY => Empty,
         FULL => Full,
         STATUS => Status,
         RESET =>reset
      );
      
--        ReadEn <= DataValid;

   -- Testing FIFO
   test : process
   begin

      -- Initializing signals
      WriteEn <= '0';
      DataIn <= X"0000";
      ReadEn <= '0';

      -- Adding a bunch of items
      wait for 110 ns;
      DataIn <= X"0123";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      wait for DELAY2;
      DataIn <= X"1234";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      wait for DELAY2;
      DataIn <= X"2345";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      -- Simultaneous reading and writing
      wait for DELAY2;
      DataIn <= X"3456";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      ReadEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';
      ReadEn <= '0';

      -- Continue writing
      wait for DELAY2;
      DataIn <= X"4567";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      wait for DELAY2;
      DataIn <= X"5678";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      wait for DELAY2;
      DataIn <= X"6789";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      wait for DELAY2;
      DataIn <= X"789A";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      wait for DELAY2;
      DataIn <= X"89AB";
      wait for DELAY1;
      wait until clk_w'event and clk_w = '0';
      WriteEn <= '1';
      wait for DELAY1;
      WriteEn <= '0';

      -- Reading out all items
      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait for DELAY2;
      ReadEn <= '1';
      wait for DELAY1;
      ReadEn <= '0';

      wait;
   end process test;

end architecture;
