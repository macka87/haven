-- testbench.vhd: dp_distmem testbench
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
use WORK.distmem_func.all;
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
   component TEST_DP_DISTMEM
      port(
      -- Common interface
      RESET  : in    std_logic; -- not used yet
      -- R/W Port
      DI     : in std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDRA  : in std_logic_vector (LOG2(TEST_ITEMS)-1 downto 0);
      DOA    : out std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
      -- Read Port
      ADDRB  : in std_logic_vector (LOG2(TEST_ITEMS)-1 downto 0);
      DOB    : out std_logic_vector(TEST_DATA_WIDTH-1 downto 0)
      );
   end component;


-- -----------------------Testbench constant-----------------------------------
   constant TEST_MAX_ADDR : integer := integer(TEST_ITEMS);
   constant period : time :=20 ns;
   constant reset_time : time := 10 * period;


-- -----------------------Testbench auxilarity signals-------------------------
   -- Common interface
   signal reset  : std_logic;

   -- R/W port
   signal di    : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   signal we    : std_logic;
   signal wclk   : std_logic;
   signal addra  : std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   signal doa    : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);

   -- Read port
   signal addrb  : std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   signal dob    : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);

begin

-- -----------------------Portmaping of tested component-----------------------
   uut: TEST_DP_DISTMEM
   port map(
      RESET => reset,
      -- R/W Port
      DI => di,
      WE => we,
      WCLK => wclk,
      ADDRA => addra,
      DOA => doa,
      -- Read Port
      ADDRB => addrb,
      DOB => dob
      );


--------------------- WCLK generation ---------------------------
   wclk_gen : process
   begin
      wclk <= '0';
      wait for period/2;
      wclk <= '1';
      wait for period/2;
   end process wclk_gen;


--------------------- Reset generation --------------------------
   reset_gen : process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process reset_gen;


-------------- WA generator -------------------------------------
   wea_gen : process
   begin
      we <= '0';
      wait for reset_time;
      we <= '1';
      wait;
   end process wea_gen;


-------------- ADRRA generator -------------------------------------
   adrra_gen : process
   variable counter: std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   begin
      wait for reset_time;
      counter:= (others => '0');
      for i in 0 to TEST_MAX_ADDR+10 loop
         addra <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process adrra_gen;


-------------- DIN generator -----------------------------------
   din_gen : process
   variable counter: std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   begin
      wait for reset_time;
      counter:=(others => '0');
      for i in 0 to TEST_MAX_ADDR + 10 loop
         di <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process din_gen;



-------------- ADRRB generator -------------------------------------
   adrrb_gen : process
   variable counter: std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   begin
      wait for reset_time + 5*period;
      counter:= (others => '0');
      for i in 0 to TEST_MAX_ADDR + 10 loop
         addrb <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process adrrb_gen;


end architecture ARCH_TESTBENCH;

