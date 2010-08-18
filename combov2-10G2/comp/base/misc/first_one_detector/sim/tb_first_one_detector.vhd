--
-- tb_first_one_detector.fdo: testbench for first one detector
-- Copyright (C) 2010 CESNET
-- Author: Koranda Karel <xkoran01@stud.fit.vutbr.cz>
--
-- $Id$
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

-- ---------------------------------------------------------------
-- ENTITY DECLARATION
-- ---------------------------------------------------------------

entity testbench is
end entity;

-- ----------------------------------------------------------------
-- ARCHITECTURE DECLARATION
-- ----------------------------------------------------------------
architecture behavioral of testbench is

  constant TEST_DATA_WIDTH	: integer 	:= 16;
  constant clkper		: time	  	:= 10 ns;

  signal CLK			: std_logic;
  signal RESET			: std_logic;

  signal mask			: std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
  signal first_one_onehot	: std_logic_vector(TEST_DATA_WIDTH-1 downto 0);
  signal first_one_binary	: std_logic_vector(max(log2(TEST_DATA_WIDTH)-1,0) downto 0);
  signal first_one_present	: std_logic;

begin

  uut : entity work.FIRST_ONE_DETECTOR
    generic map (
      DATA_WIDTH	=> TEST_DATA_WIDTH
    )
    port map (
      MASK		=> mask,
      FIRST_ONE_ONEHOT	=> first_one_onehot,
      FIRST_ONE_BINARY	=> first_one_binary,
      FIRST_ONE_PRESENT	=> first_one_present
    );

  clkgen : process
  begin
    clk <= '1';
    wait for clkper/2;
    clk <= '0';
    wait for clkper/2;
  end process;

  tb : process
  begin
    
    mask <= (others => '0');

    for j in 0 to TEST_DATA_WIDTH-1 loop
      mask <= (others => '0');
      mask(j) <= '1';
      wait for 2*clkper;
    end loop;



    mask <= (others => '0');
    wait for 10*clkper;

    for j in 0 to 100 loop
      mask <= mask + 1;
      wait for 2*clkper;
    end loop;

    wait for 10*clkper;

  end process;

end architecture behavioral;

