-- testbench.vhd: test_dp_bmem testbench
-- Copyright (C) 2004 CESNET
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
   component TEST_DP_BMEM
      port(
         -- Common interface
         RESET  : in    std_logic;

         -- Interface A
         CLKA   : in    std_logic;
         PIPE_ENA : in  std_logic;
         REA    : in    std_logic;
         WEA    : in    std_logic;
         ADDRA  : in    std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
         DIA    : in    std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
         DOA_DV : out   std_logic; -- Data valid
         DOA    : out   std_logic_vector(TEST_DATA_WIDTH-1 downto 0);

         -- Interface B
         CLKB   : in    std_logic;
         PIPE_ENB : in  std_logic;
         REB    : in    std_logic;
         WEB    : in    std_logic;
         ADDRB  : in    std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
         DIB    : in    std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
         DOB_DV : out   std_logic; -- Data valid
         DOB    : out   std_logic_vector(TEST_DATA_WIDTH-1 downto 0)
      );
   end component;


-- -----------------------Testbench constant-----------------------------------
   constant TEST_MAX_ADDR : integer := TEST_ITEMS;
   constant period : time :=20 ns;
   constant reset_time : time := 10 * period;


-- -----------------------Testbench auxilarity signals-------------------------
   -- Common interface
   signal reset  : std_logic;
   -- Interface A
   signal clka   : std_logic;
   signal pipe_ena  : std_logic;
   signal rea    : std_logic;
   signal wea    : std_logic;
   signal addra  : std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   signal dia    : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   signal doa_dv : std_logic;
   signal doa    : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);

   -- Interface B
   signal clkb   : std_logic;
   signal pipe_enb : std_logic;
   signal reb    : std_logic;
   signal web    : std_logic;
   signal addrb  : std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   signal dib    : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
   signal dob_dv : std_logic; -- Data valid
   signal dob    : std_logic_vector(TEST_DATA_WIDTH-1 downto 0);


begin

-- -----------------------Portmaping of tested component-----------------------
   uut: TEST_DP_BMEM
   port map(
	   -- Common interface
      RESET => reset,
      -- Interface A
      CLKA => clka,
      PIPE_ENA => pipe_ena,
      REA => rea,
      WEA => wea,
      ADDRA => addra,
      DIA => dia,
      DOA_DV =>doa_dv,
      DOA => doa,
      -- Interface B
      CLKB => clkb,
      PIPE_ENB => pipe_enb,
      REB => reb,
      WEB => web,
      ADDRB => addrb,
      DIB => dib,
      DOB_DV =>  dob_dv,
      DOB => dob
	);


--------------------- ClockA generation --------------------------
   clka_gen : process
   begin
      clka <= '0';
      wait for period/2;
      clka <= '1';
      wait for period/2;
   end process clka_gen;

--------------------- ClockB generation --------------------------
   clkb_gen : process
   begin
      clkb <= '0';
      wait for period/2;
      clkb <= '1';
      wait for period/2;
   end process clkb_gen;


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
      WEA <= '0';
      wait for reset_time;
      WEA <= '1';
      wait;
   end process wea_gen;


-------------- WB generator -------------------------------------
   web_gen : process
   begin
      WEB <= '0';
      wait for reset_time;
--    WEB <= '1';
      wait;
   end process web_gen;


--------------------- REA generation --------------------------
   rea_gen : process
   begin
      rea <= '0';
      wait for reset_time;
--      rea <= '1';
      wait;
   end process rea_gen;

--------------------- REB generation --------------------------
   reb_gen : process
   begin
      reb <= '0';
      wait for reset_time + 8*period;
      reb <= '1';
      wait for 5*period;
      reb <= '0';
      wait for 5*period;
      reb <= '1';
      wait for 5*period;
      reb <= '0';
      wait for 5*period;
      reb <= '1';
      wait for 5*period;
      reb <= '0';
      wait for 5*period;
      reb <= '1';
      wait;
   end process reb_gen;

--------------------- PIPE_ENA generation --------------------------
   pipea_gen : process
   begin
      PIPE_ENA <= '1';
      --wait for reset_time + 8*period;
      --PIPE_ENA <= '0';
      wait;
   end process pipea_gen;



--------------------- PIPE_ENB generation --------------------------
   pipeb_gen : process
   begin
      PIPE_ENB <= '0';
      wait for reset_time + 8*period;
      PIPE_ENB <= '0';
      wait for 5*period;
      PIPE_ENB <= '0';
      wait for 5*period;
      PIPE_ENB <= '1';
      wait for 5*period;
      PIPE_ENB <= '0';
      wait for 3*period;
      PIPE_ENB <= '1';
      wait for 7*period;
      PIPE_ENB <= '0';
      wait for 5*period;
      PIPE_ENB <= '0';

      wait;
   end process pipeb_gen;



-------------- ADRRA generator -------------------------------------
   adrra_gen : process
   variable counter: std_logic_vector(LOG2(TEST_ITEMS)-1 downto 0);
   begin
      wait for reset_time;
      counter:= (others => '0');
      for i in 0 to TEST_MAX_ADDR+10 loop
         ADDRA <= counter;
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
         DIA <= counter;
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
         ADDRB <= counter;
         counter:=counter+1;
         wait for period;
      end loop;
      wait;
   end process adrrb_gen;


end architecture ARCH_TESTBENCH;

