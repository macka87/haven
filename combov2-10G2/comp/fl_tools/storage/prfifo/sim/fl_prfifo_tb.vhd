-- fl_prfifo_tb.vhd: Testbench
-- Copyright (C) 2007 CESNET
-- Author: Jan Koritak <jenda@liberouter.org>
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


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

use work.math_pack.all;
use work.fifo_pkg.all;
entity testbench is

end testbench;

architecture behavioral of testbench is

   --Simulation Constants
   constant MemType     : mem_type := BRAM;
   constant Items       : integer  := 9;
   constant DataWidth   : integer  := 16;

   constant period      : time := 20 ns; --Clock period
   constant reset_time  : time := 100 ns; --Reset duration

   --Signals
   signal reset         : std_logic;
   signal clk           : std_logic;

   -- input FrameLink interface
   signal RX_SOF_N      :  std_logic;
   signal RX_SOP_N      :  std_logic;
   signal RX_EOP_N      :  std_logic;
   signal RX_EOF_N      :  std_logic;
   signal RX_SRC_RDY_N  :  std_logic;
   signal RX_DST_RDY_N  :  std_logic;
   signal RX_DATA       :  std_logic_vector(DataWidth-1 downto 0);
   signal RX_REM        :  std_logic_vector(log2(DataWidth/8)-1 downto 0);

   -- output FrameLink interface
   signal TX_SOF_N      :  std_logic;
   signal TX_SOP_N      :  std_logic;
   signal TX_EOP_N      :  std_logic;
   signal TX_EOF_N      :  std_logic;
   signal TX_SRC_RDY_N  :  std_logic;
   signal TX_DST_RDY_N  :  std_logic;
   signal TX_DATA       :  std_logic_vector(DataWidth-1 downto 0);
   signal TX_REM        :  std_logic_vector(log2(DataWidth/8)-1 downto 0);
   
   begin

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
      clk <= '1';
      wait for period/2;
      clk <= '0';
      wait for period/2;
   end process clk_gen;

   --Importing PRFIFO
   uut : entity work.fl_prfifo
      generic map (
         MEM_TYPE       => MemType,
         DATA_WIDTH     => DataWidth,
         ITEMS          => items
      )
      port map (
         CLK            => clk,
         RESET          => reset,

         RX_SOF_N       => RX_SOF_N,
         RX_SOP_N       => RX_SOP_N,
         RX_EOP_N       => RX_EOP_N,
         RX_EOF_N       => RX_EOF_N,
         RX_SRC_RDY_N   => RX_SRC_RDY_N,
         RX_DST_RDY_N   => RX_DST_RDY_N,
         RX_DATA        => RX_DATA,
         RX_REM         => RX_REM,

         TX_SOF_N       => TX_SOF_N,
         TX_SOP_N       => TX_SOP_N,
         TX_EOP_N       => TX_EOP_N,
         TX_EOF_N       => TX_EOF_N,
         TX_SRC_RDY_N   => TX_SRC_RDY_N,
         TX_DST_RDY_N   => TX_DST_RDY_N,
         TX_DATA        => TX_DATA,
         TX_REM         => TX_REM

      );

   -- Simulating output load
   output : process
   begin

      -- In first part of the simulation, the output is free to receive data
      -- The input flow is strobed which makes input flow slower than output
      TX_DST_RDY_N <= '0';


      -- The second part of the simulation - output flow is interrupted while the
      -- input component continues sending the data - packet releasing in effect
      
      wait for 600 ns;

      TX_DST_RDY_N <= '1';

      
      -- Unblock the output, so we can load and analyze the data stored in FIFO

      wait for 1000 ns;

      TX_DST_RDY_N <= '0';

      wait;

   end process output;

   -- Simulating input flow 
   input_flow : process
   begin

      -- Initializing input interface
      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_SRC_RDY_N       <= '1';
      RX_DATA            <= conv_std_logic_vector('1', DataWidth);
      RX_REM             <= conv_std_logic_vector('1', log2(DataWidth/8));

      wait for 200 ns;
      -- Generating some packets

      -- Packet A Part 1
      
      RX_SOP_N           <= '0';
      RX_SOF_N           <= '0';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"A101";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"A102";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet A Part 2

      RX_SOP_N           <= '0';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '0';
      RX_DATA            <= x"A203";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet B Part 1
      
      RX_SOP_N           <= '0';
      RX_SOF_N           <= '0';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"B101";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet B Part 2

      RX_SOP_N           <= '0';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"B202";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '0';
      RX_DATA            <= x"B203";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for 300 ns;

      -- Generating some other packets (longer, so we can test the releasing ability)
      -- The output is blocked, so the fifo releases packets, as it gets full

      -- Desired behaviour is dropping the packet labeled C from the flow

      RX_SRC_RDY_N       <= '1';

      -- Packet A Part 1
      
      RX_SOP_N           <= '0';
      RX_SOF_N           <= '0';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"A101";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"A102";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet A Part 2

      RX_SOP_N           <= '0';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '0';
      RX_DATA            <= x"A203";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet B Part 1
      
      RX_SOP_N           <= '0';
      RX_SOF_N           <= '0';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"B101";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet B Part 2

      RX_SOP_N           <= '0';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"B202";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '0';
      RX_DATA            <= x"B203";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet C Part 1 -- Very long packet, which will be released
      
      RX_SOP_N           <= '0';
      RX_SOF_N           <= '0';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"C101";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet C Part 2

      RX_SOP_N           <= '0';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"C202";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"C203";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"C204";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '0';
      RX_DATA            <= x"C205";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';
      
      wait for period;

      -- Packet D Part 1 -- Shorter packet which fits in the FIFO
      
      RX_SOP_N           <= '0';
      RX_SOF_N           <= '0';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"D101";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      -- Packet D Part 2

      RX_SOP_N           <= '0';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '1';
      RX_EOF_N           <= '1';
      RX_DATA            <= x"D202";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      RX_SOP_N           <= '1';
      RX_SOF_N           <= '1';
      RX_EOP_N           <= '0';
      RX_EOF_N           <= '0';
      RX_DATA            <= x"D203";
      RX_SRC_RDY_N       <= '0';

      wait for period;

      RX_SRC_RDY_N       <= '1';

      wait for period;

      wait;

   end process input_flow;

end architecture;
