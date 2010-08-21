--
-- testbench.vhd: Testbench of top level entity
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--            Pus Viktor xpusvi00@stud.fit.vutbr.cz
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
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_WIDTH  : integer   := 18;
   constant clkper      : time      := 10 ns;

   signal clk      : std_logic;
   signal reset    : std_logic;
   signal wr       : std_logic;
   signal eob      : std_logic;
   signal di       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal full     : std_logic;
   signal lstblk   : std_logic;
   signal rd       : std_logic;
   signal discard  : std_logic;
   signal do       : std_logic_vector(TEST_WIDTH - 1 downto 0);
   signal dv       : std_logic;



-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.fifo_bram_discard
generic map(
   ITEMS       => 16,
   BLOCK_SIZE  => 2,
   BRAM_TYPE   => 9,
   DATA_WIDTH  => TEST_WIDTH,
   STATUS_WIDTH => 5,
   MAX_DISCARD_BLOCKS => 10
)
port map(
   CLK      => clk,
   RESET    => reset,

   -- Write interface
   WR       => wr,
   EOB      => eob,
   DI       => di,
   FULL     => full,
   LSTBLK   => lstblk,

   -- Read interface
   RD       => rd,
   DISCARD  => discard,
   DO       => do,
   DV       => dv
);

-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

begin
   reset   <= '1';
   rd      <= '0';
   wr      <= '0';
   di      <= (others => '0');
   eob     <= '0';
   discard <= '0';

   wait for 4*clkper;
   reset <= '0';

   wait for 20*clkper;
   wait for 2 ns;

   -- fill fifo
   wr    <= '1';
   for i in 1 to 20 loop
      di    <= conv_std_logic_vector(i, di'length);

      -- Write end of block in last word
--       if (i = 8) then
--          eob <= '1';
--       else
--          eob <= '0';
--       end if;

      wait for clkper;
   end loop;
   wr    <= '0';

   wait for 10*clkper;

   -- two cycles of reading will result in one data output
   rd    <='1';
   wait for clkper;
   rd    <='0';
   wait for 10*clkper;
   rd    <='1';
   wait for clkper;
   rd    <='0';


   wait for 10*clkper;

   -- read one word and discard - FIFO should stay empty
   rd    <= '1';
   for i in 1 to 14 loop
      if (i = 2) then
         discard <= '1';
      else
         discard <= '0';
      end if;

      wait for clkper;
   end loop;

   rd    <= '0';

   -- final part is interesting
--    wait for clkper;
--    rd    <= '1';
--    wait for clkper;
--    rd    <= '0';
-- 
--    wait for clkper;
--    rd    <= '1';
--    wait for clkper;
--    rd    <= '0';


   wait for 20*clkper;


   -- write to the discarded FIFO - should stay empty waiting for EOB
   wr    <= '1';
   for i in 1 to 20 loop
      di    <= conv_std_logic_vector(i, di'length);

      if (i = 2) then
         eob <= '1';
      else
         eob <= '0';
      end if;

      wait for clkper;
   end loop;

   eob <= '0';


   -- ... and read at once + set EOB true to fill the block fifo
   rd    <= '1';
   eob   <= '1';
   for i in 21 to 40 loop
      di    <= conv_std_logic_vector(i, di'length);
      wait for clkper;
   end loop;

   rd    <= '0';
   wr    <= '0';
   eob   <= '0';


   wait for 10*clkper;

   -- Reset
   reset <= '1';
   wait for clkper;
   reset <= '0';

   wait for 10*clkper;

   -- Write one word - discard and write EOB at once
   wr <= '1';
   wait for clkper;
   discard <= '1';
   eob <= '1';
   wait for clkper;

   discard <= '0';
   eob <= '0';

   -- And continue writing
   for i in 1 to 4 loop
      di    <= conv_std_logic_vector(i, di'length);
      wait for clkper;
   end loop;

   wr <= '0';

   wait for 10*clkper;


   reset <= '1';
   wait for 10*clkper;
   reset <= '0';
   wait for clkper;

   wr <= '1';
   for i in 1 to 3 loop
      di    <= conv_std_logic_vector(i, di'length);
      if (i = 3) then
         eob <= '1';
      else
         eob <= '0';
      end if;

      wait for clkper;
   end loop;
   
   eob <= '0';
   wr <= '0';

   for i in 1 to 2 loop
      rd <= '1';
      wait for clkper;
   end loop;
   rd <= '0';

--    wait for 5*clkper;

--    rd <= '1';
   discard <= '1';
   wait for clkper;
   discard <= '0';
   rd <= '0';

   -- Write one word
   wr <= '1';
   eob <= '1';
   di <= conv_std_logic_vector(15, di'length);
   wait for clkper;

   eob <= '0';
   di <= conv_std_logic_vector(16, di'length);
   wait for clkper;
   wr <= '0';

   -- Try to read it, should be without the word discarded
   for i in 1 to 3 loop
      rd <= '1';
      wait for clkper;
   end loop;

   rd <= '0';

   wait for 10*clkper;


   -- RESET
   reset <= '1';
   wait for 3*clkper;
   reset <= '0';


   wait for 10*clkper;

   discard <= '1';
   wait for clkper;
   discard <= '0';


   wait for 10*clkper;


   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
