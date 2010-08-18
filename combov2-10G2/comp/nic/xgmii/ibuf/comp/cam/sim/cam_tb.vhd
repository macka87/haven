-- cam_tb.vhd: Testbench for CAM
-- Copyright (C) 2005-2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_tb of testbench is
   
-- ------------------ Constant definition -------------------------------------
   constant CAM_ADDR_WIDTH  : integer := log2(CAM_ROW_COUNT);

-- ------------------ Signals declaration -------------------------------------
   signal ADDR              : std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
   signal DATA_IN           : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal WRITE_ENABLE      : std_logic;
   signal MATCH_ENABLE      : std_logic;
   signal MATCH_RST         : std_logic;
   signal RESET             : std_logic;
   signal CLK               : std_logic;
   signal MATCH_BUS         : std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
   signal MATCH_BUS_VLD     : std_logic;
   signal READ_EN           : std_logic;
   signal DATA_OUT          : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal DATA_OUT_VLD      : std_logic;
   
-- ------------------ Component declaration -------------------------------------
   component IBUF_CAM is
      generic (
         -- Data row width (bits, should be a multiple of 4)
         CAM_ROW_WIDTH     : integer;
         -- Number of data rows (depth of the CAM)
         CAM_ROW_COUNT     : integer
      );
      port (
         ADDR              : in std_logic_vector((CAM_ADDR_WIDTH - 1) 
                                                                     downto 0);
         DATA_IN           : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
         WRITE_EN          : in std_logic;
         READ_EN           : in std_logic;
         DATA_OUT          : out std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
         DATA_OUT_VLD      : out std_logic;
         MATCH_EN          : in std_logic;
         MATCH_RST         : in std_logic;
         RESET             : in std_logic;
         CLK               : in std_logic;
         MATCH_BUS         : out std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
         MATCH_BUS_VLD     : out std_logic
      );
   end component IBUF_CAM;


begin

-- ---------- Connecting component to testbench  ------------------------------
   UUT : IBUF_CAM
      generic map (
         CAM_ROW_WIDTH => CAM_ROW_WIDTH,
         CAM_ROW_COUNT => CAM_ROW_COUNT
      )
      port map (
         ADDR              => ADDR,
         DATA_IN           => DATA_IN,
         WRITE_EN          => WRITE_ENABLE,
         READ_EN           => READ_EN,
         DATA_OUT          => DATA_OUT,
         DATA_OUT_VLD      => DATA_OUT_VLD,
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
--
      procedure cam_insert_word(
         p_addr     : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
         p_data_in  : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0)
      ) is
      begin
         wait until clk'event and clk='1';
         WRITE_ENABLE <= '1';
         ADDR     <= p_addr;
         DATA_IN  <= p_data_in;
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

-- ----------------------------------------------------------------
-- procedure cam_read_word reads word from specified ADDR
--
-- Parameters:
--    p_addr_in:     address that should be read
--
      procedure cam_read_word(
         p_addr_in   : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0)
      ) is
      begin
         wait until clk'event and clk='1';
         wait for clk_period;
         ADDR <= p_addr_in;
         READ_EN <= '1';
         wait for clk_period;
         READ_EN <= '0';
         wait until DATA_OUT_VLD='1';
      end cam_read_word;

   begin
-- ----------- Activating RESET signal ----------------------------------------
   RESET <= '1';
   wait for 10*clk_period;
   wait until CLK'event and CLK='1';

   RESET <= '0';

   MATCH_RST <= '0';
   WRITE_ENABLE <= '0';
   MATCH_ENABLE <= '0';
   READ_EN  <= '0';
   ADDR     <= "0000";
   DATA_IN  <= "00000000";

   wait for 5*clk_period;
   wait until clk'event and clk='1';

   cam_read_word("1011");
   wait for clk_period/2;
   wait for 2*clk_period;

   wait for clk_period;
   wait until CLK'event and CLK='1';

-- ----------- Fill memory elements -------------------------------------------

-- Try simple inserting
   cam_insert_word("0000","00000000");
   cam_insert_word("0001","11111111");
   cam_insert_word("0010","11110000");
   cam_insert_word("0011","00001111");
   cam_insert_word("0100","10101010");
   cam_insert_word("0101","01010101");
   cam_insert_word("0110","11001100");
   cam_insert_word("0111","00110011");
   cam_insert_word("1000","11000011");
   cam_insert_word("1001","00111100");
   cam_insert_word("1010","01000010");
   cam_insert_word("1011","01100110");

   cam_insert_word("1100","11111111");
   cam_insert_word("1101","11111111");
   cam_insert_word("1110","11111111");
   cam_insert_word("1111","11111111");

-- ----------- Try memory elements --------------------------------------------
   wait for 5*clk_period;
   wait until clk'event and clk='1';
   MATCH_ENABLE <= '1';
   
   cam_search_word("00000000");
   wait for 2*clk_period; -- this wait is here only for testing purposes (so that
                        -- assertion will work)
   assert (MATCH_BUS="0000000000000001") report "Search #1 FAILED!!!" severity error; 

   cam_search_word("11111111");
   wait for 2*clk_period;
   assert (MATCH_BUS="1111000000000010") report "Search #2 FAILED!!!" severity error; 
   
   cam_search_word("10101010");
   wait for 2*clk_period;
   assert (MATCH_BUS="0000000000010000") report "Search #3 FAILED!!!" severity error; 
   
   cam_search_word("01010101");
   wait for 2*clk_period;
   assert (MATCH_BUS="0000000000100000") report "Search #4 FAILED!!!" severity error; 

   wait for 5*clk_period;
   wait until clk'event and clk='1';
   MATCH_ENABLE <= '0';

   cam_read_word("0000");
   wait for clk_period/2;
   assert (DATA_OUT="00000000") report "Read #1 FAILED!!!" severity error; 
   wait for 2*clk_period;
   
   cam_read_word("0001");
   wait for clk_period/2;
   assert (DATA_OUT="11111111") report "Read #2 FAILED!!!" severity error; 
   wait for 2*clk_period;

   cam_read_word("1011");
   wait for clk_period/2;
   assert (DATA_OUT="01100110") report "Read #3 FAILED!!!" severity error; 
   wait for 2*clk_period;

   cam_read_word("1000");
   wait for clk_period/2;
   assert (DATA_OUT="11000011") report "Read #4 FAILED!!!" severity error; 
   wait for 2*clk_period;

   wait; 
   end process probe;

end cam_tb;
