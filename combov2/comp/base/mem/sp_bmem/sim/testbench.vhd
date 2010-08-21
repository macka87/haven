-- testbench.vhd: test_sp_bmem testbench
-- Copyright (C) 2005 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
--
-- TODO:
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;
-- auxilarity functions and constant needed to evaluate generic address etc.
use WORK.bmem_func.all;
-- test constants
use WORK.test_par.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
end TESTBENCH;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ARCH_TESTBENCH of TESTBENCH is



-- ---------------------Tested Component---------------------------------------
   component TEST_SP_BMEM
      port(
         RESET   : in    std_logic;
         CLK     : in    std_logic;
         PIPE_EN : in  std_logic;
         RE      : in    std_logic;
         WE      : in    std_logic;
         ADDR    : in    std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
         DI      : in    std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
         DO_DV   : out   std_logic; -- Data valid
         DO      : out   std_logic_vector(TEST_DATA_WIDTH-1 downto 0)
      );
   end component;


-- -----------------------Testbench constant-----------------------------------
   constant TEST_MAX_ADDR : integer := TEST_ITEMS;
   constant period : time :=20 ns;
   constant reset_time : time := 10 * period;


-- -----------------------Testbench auxilarity signals-------------------------
   signal reset    : std_logic;
   signal clk      : std_logic;
   signal pipe_en  : std_logic;
   signal re       : std_logic;
   signal we       : std_logic;
   signal addr     : std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   signal di       : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   signal do_dv    : std_logic;
   signal do       : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);


begin

-- -----------------------Portmaping of tested component-----------------------
   uut: TEST_SP_BMEM
   port map(
      RESET => reset,
      CLK => clk,
      PIPE_EN => pipe_en,
      RE => re,
      WE => we,
      ADDR => addr,
      DI => di,
      DO_DV =>do_dv,
      DO => do
	);


--------------------- Clock  generation --------------------------
   clka_gen : process
   begin
      clk <= '0';
      wait for period/2;
      clk <= '1';
      wait for period/2;
   end process clka_gen;


--------------------- Reset generation --------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;



-------------- WE generator -------------------------------------
   we_gen : process
   begin
     WE <= '0';
     wait for reset_time;
     WE <= '1';
     for i in 0 to (TEST_MAX_ADDR-1) loop
        wait for period;
     end loop;
     WE <= '0';
     wait;
   end process we_gen;


---------------------- RE  generation --------------------------
   re_gen : process
   begin
      re <= '0';
      wait for reset_time;

      for i in 0 to TEST_MAX_ADDR + 2 loop
        wait for period;
      end loop;

      re <= '1';
      wait for 5*period;
      re <= '0';
      wait for 5*period;
      re <= '1';
      wait for 5*period;
      re <= '0';
      wait for 5*period;
      re <= '1';
      wait for 5*period;
      re <= '0';
      wait for 5*period;
      re <= '1';
      wait;
   end process re_gen;


--------------------- PIPE_EN generation --------------------------
   pipe_gen : process
   begin
      PIPE_EN <= '0';
      wait for reset_time;
      for i in 0 to TEST_MAX_ADDR+2 loop
        wait for period;
      end loop;

      PIPE_EN <= '0';
      wait for 5*period;
      PIPE_EN <= '0';
      wait for 5*period;
      PIPE_EN <= '1';
      wait for 5*period;
      PIPE_EN <= '0';
      wait for 3*period;
      PIPE_EN <= '1';
      wait for 7*period;
      PIPE_EN <= '0';
      wait for 5*period;
      PIPE_EN <= '1';

      wait;
   end process pipe_gen;



-------------- ADRRA generator -------------------------------------
   adrr_gen : process
   variable counter: std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   begin
      wait for reset_time;
      counter:= (others => '0');
      for i in 0 to (2*TEST_MAX_ADDR)+10 loop
         ADDR <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process adrr_gen;


-------------- DIN generator -----------------------------------
   din_gen : process
   variable counter: std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   begin
      wait for reset_time;
      counter:=(others => '0');
      for i in 0 to TEST_MAX_ADDR loop
         DI <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process din_gen;


end architecture ARCH_TESTBENCH;

