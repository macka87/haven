-- cam_tb.vhd: Testbench for CAM
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use work.cam_tb_pkg.all; -- package with default CAM constants

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_tb of testbench is
   
-- ------------------ Signals declaration -------------------------------------
   signal ADDR              : std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
   signal DATA_IN           : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal MASK_IN           : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal WRITE_ENABLE      : std_logic;
   signal MATCH_ENABLE      : std_logic;
   signal MATCH_RST         : std_logic;
   signal RESET             : std_logic;
   signal CLK               : std_logic;
   signal MATCH_BUS         : std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
   signal MATCH_BUS_VLD     : std_logic;
   
-- ------------------ Component declaration -------------------------------------
   component CAM is
      generic (
         -- Data row width (bits, should be a multiple of 4)
         CAM_ROW_WIDTH     : integer;
         -- Number of data rows (depth of the CAM)
         CAM_ROW_COUNT     : integer;
         -- Width of address bus 
         -- should be greater or equal to log2(CAM_ROW_COUNT)
         CAM_ADDR_WIDTH    : integer
      );
      port (
         ADDR              : in std_logic_vector((CAM_ADDR_WIDTH - 1) 
                                                                     downto 0);
         DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
         MASK_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
         WRITE_EN          : in std_logic;
         MATCH_EN          : in std_logic;
         MATCH_RST         : in std_logic;
         RESET             : in std_logic;
         CLK               : in std_logic;
         MATCH_BUS         : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
         MATCH_BUS_VLD     : out std_logic
      );
   end component CAM;


begin

-- ---------- Connecting component to testbench  ------------------------------
   UUT : CAM
      generic map (
         CAM_ROW_WIDTH => CAM_ROW_WIDTH,
         CAM_ROW_COUNT => CAM_ROW_COUNT,
         CAM_ADDR_WIDTH => CAM_ADDR_WIDTH
      )
      port map (
         ADDR              => ADDR,
         DATA_IN           => DATA_IN,
         MASK_IN           => MASK_IN,
         WRITE_EN          => WRITE_ENABLE,
         MATCH_EN          => MATCH_ENABLE,
         MATCH_RST         => MATCH_RST,
         RESET             => RESET,
         CLK               => CLK,
         MATCH_BUS         => MATCH_BUS,
         MATCH_BUS_VLD     => MATCH_BUS_VLD
      );
   
-- ----------- Generating clock signal ----------------------------------------
   tb_clk_gen: process
   begin
      CLK <= '1';
      wait for clk_period/2; 
      CLK <= '0';
      wait for clk_period/2; 
   end process tb_clk_gen;

-- ----------- Probes ---------------------------------------------------------
   probe : process
-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------

-- ----------------------------------------------------------------
-- procedure cam_insert_word inserts one word into CAM data array in the row
-- selected by address
--
-- Parameters:
--    p_addr:     data row address
--    p_data_in:  inserted data
--    p_mask_in:  specify 'care' and 'dont't care' bits
--                '1' => I care about that bit
--                '0' => I don't care about that bit
--
      procedure cam_insert_word(
         p_addr     : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
         p_data_in  : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
         p_mask_in  : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0)
      ) is
      begin
         wait until clk'event and clk='1';
         WRITE_ENABLE <= '1';
         ADDR     <= p_addr;
         DATA_IN  <= p_data_in;
         MASK_IN  <= p_mask_in;
         wait for clk_period;
         WRITE_ENABLE <= '0';
         wait for 16*clk_period;
         wait until clk'event and clk='1';
      end cam_insert_word;

-- ----------------------------------------------------------------
-- procedure cam_search_word searches in CAM for selected data
--
-- Parameters:
--    p_data_in:     data that should be searched in CAM
--
      procedure cam_search_word(
         p_data_in  : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0)
      ) is
      begin
         wait until clk'event and clk='1';
         DATA_IN  <= p_data_in;
         wait for clk_period;
      end cam_search_word;

   begin
-- ----------- Activating RESET signal ----------------------------------------
   RESET <= '1';
   wait for 10*clk_period;
   wait until CLK'event and CLK='1';

   RESET <= '0';  

   MATCH_RST <= '0';
   WRITE_ENABLE <= '0';
   MATCH_ENABLE <= '0';
   MASK_IN  <= "00000000";
   ADDR     <= "00000000";
   DATA_IN  <= "00000000";

   wait for clk_period;
   wait until CLK'event and CLK='1';
   
-- ----------- Fill memory elements -------------------------------------------

-- Try simple inserting (without using MASK)
   cam_insert_word("00000000","00000000","11111111");
   cam_insert_word("00000001","11111111","11111111");
   cam_insert_word("00000010","11110000","11111111");
   cam_insert_word("00000011","00001111","11111111");
   cam_insert_word("00000100","10101010","11111111");
   cam_insert_word("00000101","01010101","11111111");
   cam_insert_word("00000110","11001100","11111111");
   cam_insert_word("00000111","00110011","11111111");
   cam_insert_word("00001000","11000011","11111111");
   cam_insert_word("00001001","00111100","11111111");
   cam_insert_word("00001010","01000010","11111111");
   cam_insert_word("00001011","01100110","11111111");

-- Try advanced inserting (specifying MASK)
   cam_insert_word("00001100","11111111","10101010"); -- 1d1d1d1d
   cam_insert_word("00001101","11111111","11110000"); -- 1111dddd
   cam_insert_word("00001110","11111111","00001111"); -- dddd1111
   cam_insert_word("00001111","11111111","00000000"); -- dddddddd

-- ----------- Try memory elements --------------------------------------------
   wait for 5*clk_period;
   wait until clk'event and clk='1';
   MATCH_ENABLE <= '1';
   
   cam_search_word("00000000");
   wait for 2*clk_period; -- this wait is here only for testing purposes (so that
                        -- assertion will work)
   assert (MATCH_BUS="1000000000000001") report "Search #1 FAILED!!!" severity error; 

   cam_search_word("11111111");
   wait for 2*clk_period;
   assert (MATCH_BUS="1111000000000010") report "Search #2 FAILED!!!" severity error; 
   
   cam_search_word("10101010");
   wait for 2*clk_period;
   assert (MATCH_BUS="1001000000010000") report "Search #3 FAILED!!!" severity error; 
   
   cam_search_word("01010101");
   wait for 2*clk_period;
   assert (MATCH_BUS="1000000000100000") report "Search #4 FAILED!!!" severity error; 
   
   wait; 
   end process probe;

end cam_tb;
