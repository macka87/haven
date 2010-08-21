-- testbench.vhd: sp_distmem testbench
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
-- use WORK.test_par.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TESTBENCH is
   generic(
      -- Data Width
      DATA_WIDTH  : integer := 4;
      -- Item in memory needed, one item size is DATA_WIDTH
      ITEMS : integer := 16;
      -- Distributed Ram Type(capacity) only 16, 32, 64 bits
      DISTMEM_TYPE : integer := 16;
      -- debug prints
      DEBUG   : boolean := false
   );
end TESTBENCH;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ARCH_TESTBENCH of TESTBENCH is


-- ---------------------Tested Component---------------------------------------
   component SP_DISTMEM
      port(
      -- Common interface
      RESET  : in    std_logic; -- not used yet
      -- R/W Port
      DI     : in std_logic_vector(DATA_WIDTH-1 downto 0);
      WE     : in std_logic;
      WCLK   : in std_logic;
      ADDR   : in std_logic_vector (LOG2(ITEMS)-1 downto 0);
      DO     : out std_logic_vector(DATA_WIDTH-1 downto 0)
      );
   end component;


-- -----------------------Testbench constant-----------------------------------
   constant MAX_ADDR : integer := integer(ITEMS);
   constant period : time :=20 ns;
   constant reset_time : time := 10 * period;


-- -----------------------Testbench auxilarity signals-------------------------
   -- Common interface
   signal reset  : std_logic;

   -- R/W port
   signal di     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal we     : std_logic;
   signal wclk   : std_logic;
   signal addr   : std_logic_vector(LOG2(ITEMS)-1 downto 0);
   signal do     : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

-- -----------------------Portmaping of tested component-----------------------
   uut: SP_DISTMEM
   port map(
      RESET => reset,
      -- R/W Port
      DI => di,
      WE => we,
      WCLK => wclk,
      ADDR => addr,
      DO => do
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


-------------- WE generator -------------------------------------
   wea_gen : process
   begin
      we <= '0';
      wait for reset_time;
      we <= '1';
      wait for MAX_ADDR * period;
      we <= '0';
      wait;
   end process wea_gen;


-------------- ADDR generator --------------------------------------
   addr_gen : process
   variable counter: std_logic_vector(LOG2(ITEMS)-1 downto 0);
   begin
      wait for reset_time;
      counter:= (others => '0');
      for i in 0 to 2*MAX_ADDR loop
         addr <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process addr_gen;


-------------- DIN generator -----------------------------------
   din_gen : process
   variable counter: std_logic_vector(DATA_WIDTH-1 downto 0);
   begin
      wait for reset_time;
      counter:=(others => '0');
      for i in 0 to MAX_ADDR loop
         di <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process din_gen;


end architecture ARCH_TESTBENCH;

