-- testbench.vhd: CB_ENDPOINT testbench
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;

library work;

use work.math_pack.all;
use work.cb_pkg.all;
use work.fl_pkg.all;


ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

   constant clkper : time := 10 ns;

   signal CB         : t_control_bus;

   signal CB_CLK     : std_logic;
   signal CB_RESET   : std_logic;

      -- User Component Upstream Interface
   signal UPS_FL     : t_fl16;

      -- User Component Downstream Interface
   signal DNS_FL     : t_fl16;

begin
   uut: entity work.CB_ENDPOINT
   generic map(
      DATA_WIDTH     => 16,
      SOURCE_ID      => "0100",
      EMPTY_INTERVAL => 2,
      IN_BUF_SIZE    => 16,
      OUT_BUF_SIZE   => 16,
      OUT_BUF_MSGS   => 4
   )
   port map(
      -- Common Control Bus signals
      CB_CLK         => CB_CLK,
      CB_RESET       => CB_RESET,
      
      -- One Control Bus interface
      CB             => CB,

      -- User Component Upstream Interface
      UPS_FL         => UPS_FL,

      -- User Component Downstream Interface
      DNS_FL         => DNS_FL
   );

   clk_gen : process
   begin
      CB_CLK <= '1';
      wait for clkper/2;
      CB_CLK <= '0';
      wait for clkper/2;
   end process;

   tb: process
   begin
      CB_RESET <= '1';
      
      UPS_FL.DATA <= (others => '0');
      UPS_FL.DREM <= "1";
      UPS_FL.SOP_N <= '1';
      UPS_FL.EOP_N <= '1';
      UPS_FL.SOF_N <= '1';
      UPS_FL.EOF_N <= '1';
      UPS_FL.SRC_RDY_N <= '1';
      DNS_FL.DST_RDY_N <= '0';

      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      CB.UP.DST_RDY_N <= '0';
      
      wait for 10*clkper;
      wait for 2 ns;
      CB_RESET <= '0';
      wait for 10*clkper;
      
      -- Recieve init message but with incorrect DST_ID
      CB.DOWN.DATA <= "0000000010000000";
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.EOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;  
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 5*clkper;
      
      -- Recieve init message with correct DST_ID
      CB.DOWN.DATA <= "0100000000010100"; -- 20 free items in root TX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.EOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;  
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 1*clkper;
      CB.UP.DST_RDY_N <= '1';
      wait for 2*clkper;
      CB.UP.DST_RDY_N <= '0';
      wait for 10*clkper;
      
      -- Reset the component
      CB_RESET <= '1';
      wait for clkper;
      CB_RESET <= '0';
      wait for 10*clkper;

      -- Send first message
      UPS_FL.DATA <= conv_std_logic_vector(5, 16);
      UPS_FL.SOP_N <= '0';
      UPS_FL.SOF_N <= '0';
      UPS_FL.SRC_RDY_N <= '0';
      wait for clkper;  -- SOP
      UPS_FL.DATA <= conv_std_logic_vector(6, 16);
      UPS_FL.SOP_N <= '1';
      UPS_FL.SOF_N <= '1';
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(7, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(8, 16);
      UPS_FL.EOP_N <= '0';
      UPS_FL.EOF_N <= '0';
      wait for clkper;  -- EOP
      UPS_FL.EOP_N <= '1';
      UPS_FL.EOF_N <= '1';
      UPS_FL.DATA <= (others => '0');
      UPS_FL.SRC_RDY_N <= '1';
      wait for 10*clkper;
      
      -- Recieve init message with correct DST_ID
      CB.DOWN.DATA <= "0100000000010100"; -- 20 free items in root TX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.EOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;  
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 3*clkper;
      CB.UP.DST_RDY_N <= '1';
      wait for 4*clkper;
      CB.UP.DST_RDY_N <= '0';
      wait for 20*clkper;

      -- Send second message, only one word long
      UPS_FL.DATA <= conv_std_logic_vector(10, 16);
      UPS_FL.SOP_N <= '0';
      UPS_FL.EOP_N <= '0';
      UPS_FL.SOF_N <= '0';
      UPS_FL.EOF_N <= '0';
      UPS_FL.SRC_RDY_N <= '0';
      wait for clkper;  -- SOP
      UPS_FL.DATA <= (others => '0');
      UPS_FL.SOP_N <= '1';
      UPS_FL.EOP_N <= '1';
      UPS_FL.SOF_N <= '1';
      UPS_FL.EOF_N <= '1';
      UPS_FL.SRC_RDY_N <= '1';
      wait for 10*clkper;

      -- Recieve message from Control Bus interface
      CB.DOWN.DATA <= "0100000000000010"; -- 2 items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(20, 16);
      CB.DOWN.SOP_N <= '1';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(21, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(22, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(23, 16);
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 2*clkper;
      CB.UP.DST_RDY_N <= '1';
      wait for 1*clkper;
      CB.UP.DST_RDY_N <= '0';
      wait for 10*clkper;
      
      -- The same message, but with wrong DST_ID field
      CB.DOWN.DATA <= "0010000000000010"; -- 2 items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(20, 16);
      CB.DOWN.SOP_N <= '1';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(21, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(22, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(23, 16);
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 10*clkper;

      -- Message with only one data word
      CB.DOWN.DATA <= "0100000000000000"; -- no items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(30, 16);
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 10*clkper;
      
      -- Send message of maximal length (16)
      UPS_FL.DATA <= conv_std_logic_vector(40, 16);
      UPS_FL.SOP_N <= '0';
      UPS_FL.SOF_N <= '0';
      UPS_FL.SRC_RDY_N <= '0';
      wait for clkper;  -- SOP
      UPS_FL.DATA <= conv_std_logic_vector(41, 16);
      UPS_FL.SOP_N <= '1';
      UPS_FL.SOF_N <= '1';
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(42, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(43, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(44, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(45, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(46, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(47, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(48, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(49, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(50, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(51, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(52, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(53, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(54, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(55, 16);
      UPS_FL.EOP_N <= '0';
      UPS_FL.EOF_N <= '0';
      wait for clkper;  -- EOP
      UPS_FL.EOP_N <= '1';
      UPS_FL.EOF_N <= '1';
      UPS_FL.DATA <= (others => '0');
      UPS_FL.SRC_RDY_N <= '1';
      wait for 6*clkper;

      -- interrupt transmit with RDY
      CB.UP.DST_RDY_N <= '1';
      wait for 3*clkper;
      CB.UP.DST_RDY_N <= '0';
      wait for 3*clkper;

      -- recieve message during transmit
      CB.DOWN.DATA <= "0100000000000010"; -- 2 items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(60, 16);
      CB.DOWN.SOP_N <= '1';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(61, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(62, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(63, 16);
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 10*clkper;
      
      -- recieve long message
      CB.DOWN.DATA <= "0100000000000011"; -- 3 items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(70, 16);
      CB.DOWN.SOP_N <= '1';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(71, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(72, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(73, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(74, 16);
      
      UPS_FL.DATA <= conv_std_logic_vector(10, 16);   -- Send message during
      UPS_FL.SOP_N <= '0';                              -- recieving
      UPS_FL.EOP_N <= '0';
      UPS_FL.SOF_N <= '0';                              -- recieving
      UPS_FL.EOF_N <= '0';
      UPS_FL.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(75, 16);
      
      UPS_FL.DATA <= (others => '0');
      UPS_FL.SOP_N <= '1';
      UPS_FL.EOP_N <= '1';
      UPS_FL.SOF_N <= '1';
      UPS_FL.EOF_N <= '1';
      UPS_FL.SRC_RDY_N <= '1';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(76, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(77, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(78, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(79, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(80, 16);
      DNS_FL.DST_RDY_N <= '0';  -- Interruput recieving with RDY
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(81, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(82, 16);
      wait for clkper;
      DNS_FL.DST_RDY_N <= '1';
      CB.DOWN.DATA <= conv_std_logic_vector(83, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(84, 16);
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(85, 16);
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for 10*clkper;

      -- Send message of maximal length (16)
      UPS_FL.DATA <= conv_std_logic_vector(40, 16);
      UPS_FL.SOP_N <= '0';
      UPS_FL.SOF_N <= '0';
      UPS_FL.SRC_RDY_N <= '0';
      wait for clkper;  -- SOP
      UPS_FL.DATA <= conv_std_logic_vector(41, 16);
      UPS_FL.SOP_N <= '1';
      UPS_FL.SOF_N <= '1';
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(42, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(43, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(44, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(45, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(46, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(47, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(48, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(49, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(50, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(51, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(52, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(53, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(54, 16);
      wait for clkper;  -- data
      UPS_FL.DATA <= conv_std_logic_vector(55, 16);
      UPS_FL.EOP_N <= '0';
      UPS_FL.EOF_N <= '0';
      wait for clkper;  -- EOP
      UPS_FL.EOP_N <= '1';
      UPS_FL.EOF_N <= '1';
      UPS_FL.DATA <= (others => '0');
      UPS_FL.SRC_RDY_N <= '1';
      wait for 3*clkper;
            
      -- Send next message, only one word long
      UPS_FL.DATA <= conv_std_logic_vector(10, 16);
      UPS_FL.SOP_N <= '0';
      UPS_FL.EOP_N <= '0';
      UPS_FL.SOF_N <= '0';
      UPS_FL.EOF_N <= '0';
      UPS_FL.SRC_RDY_N <= '0';
      wait for clkper;  -- SOP
      UPS_FL.DATA <= (others => '0');
      UPS_FL.SOP_N <= '1';
      UPS_FL.EOP_N <= '1';
      UPS_FL.SOF_N <= '1';
      UPS_FL.EOF_N <= '1';
      UPS_FL.SRC_RDY_N <= '1';
      wait for 3*clkper;

      -- Message with only one data word
      CB.DOWN.DATA <= "0100000000000000"; -- no items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(30, 16);
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for clkper;
      -- Message with only one data word
      CB.DOWN.DATA <= "0100000000000000"; -- no items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(30, 16);
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for clkper;     
      -- Message with only one data word
      CB.DOWN.DATA <= "0100000000000000"; -- no items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(30, 16);
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for clkper;
      -- Message with only one data word
      CB.DOWN.DATA <= "0100000000010000"; -- 16 items freed from root RX buffer
      CB.DOWN.SOP_N <= '0';
      CB.DOWN.SRC_RDY_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= conv_std_logic_vector(30, 16);
      CB.DOWN.SOP_N <= '1';
      CB.DOWN.EOP_N <= '0';
      wait for clkper;
      CB.DOWN.DATA <= (others => '0');
      CB.DOWN.EOP_N <= '1';
      CB.DOWN.SRC_RDY_N <= '1';
      wait for clkper;

      wait for 17*clkper;
      CB.UP.DST_RDY_N <= '1';
      wait for 2*clkper;
      CB.UP.DST_RDY_N <= '0';


      wait;
   end process;

end;
