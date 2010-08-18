-- testbench.vhd: cb_root testbench
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
use work.math_pack.all;
use work.cb_pkg.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

constant clkper :time := 10 ns;
constant QADDR_WIDTH : integer := 8;

signal CB_CLK       : std_logic;
signal CB_RESET     : std_logic;
      
      -- RX, TX queues interface
signal QADDR        : std_logic_vector(QADDR_WIDTH-1 downto 0);
signal QWR          : std_logic;
signal QRD          : std_logic;
signal QDWR         : std_logic_vector(63 downto 0);
signal QBE          : std_logic_vector(7 downto 0);
signal QDRD         : std_logic_vector(63 downto 0);
signal QDRDY        : std_logic;

      -- Control/Status interface
signal CADDR        : std_logic_vector(7 downto 0);
signal CWR          : std_logic;
signal CRD          : std_logic;
signal CDWR         : std_logic_vector(31 downto 0);
signal CBE          : std_logic_vector(3 downto 0);
signal CDRD         : std_logic_vector(31 downto 0);
signal CDRDY        : std_logic;

      -- Control Bus interfaces
signal CB           : t_control_bus;

begin

uut: entity work.cb_root
   generic map(
      QADDR_WIDTH  => 8
   )
   port map(
      -- Common interface
      CB_CLK       => CB_CLK,
      CB_RESET     => CB_RESET,
      
      -- RX, TX queues interface
      QADDR        => QADDR,
      QWR          => QWR,
      QRD          => QRD,
      QDWR         => QDWR,
      QBE          => QBE,
      QDRD         => QDRD,
      QDRDY        => QDRDY,

      -- Control/Status interface
      CADDR        => CADDR,
      CWR          => CWR,
      CRD          => CRD,
      CDWR         => CDWR,
      CBE          => CBE,
      CDRD         => CDRD,
      CDRDY        => CDRDY,

      -- Control Bus interfaces
      CB           => CB
   );

-- Clock generation
local_clock: process
begin
   CB_CLK <= '1';
   wait for clkper/2;
   CB_CLK <= '0';
   wait for clkper/2;
end process;

-- Test process
test: process
begin
   wait for 2 ns;
   CB_RESET <= '1';
   QADDR <= "00000000";
   QWR <= '0';
   QRD <= '0';
   QDWR <= X"0000000000000000";
   QBE <= "00000000";
   CADDR <= "00000000";
   CWR <= '0';
   CRD <= '0';
   CDWR <= X"00000000";
   CBE <= "0000";
   CB.DOWN.DST_RDY_N <= '0';
   CB.UP.DATA <= X"0000";
   CB.UP.SOP_N <= '1';
   CB.UP.EOP_N <= '1';
   CB.UP.SRC_RDY_N <= '1';
   wait for 5*clkper;

   CB_RESET <= '0';
   wait for 5*clkper;

   -- "Flow Control Init" command from PPC
   CADDR <= "10000010";
   CWR <= '1';
   CBE <= "1111";
   CDWR <= X"00000001";
   wait for clkper;
   CWR <= '0';
   CB.DOWN.DST_RDY_N <= '0';
   wait for 2*clkper;
   CB.DOWN.DST_RDY_N <= '0';
   
   wait for 8*clkper;
   CB.DOWN.DST_RDY_N <= '0';
   wait for 2*clkper;
   CB.DOWN.DST_RDY_N <= '0';
   wait for clkper;
   CB.DOWN.DST_RDY_N <= '1';
   wait for clkper;
   CB.DOWN.DST_RDY_N <= '0';
   wait for 30*clkper;

   -- Recieve empty (head only) message from CB
   CB.UP.SRC_RDY_N <= '0';
   CB.UP.DATA <= X"3010";  -- Src_Id=3 & 0 & Endpoint diff buffer size=0x10
   CB.UP.SOP_N <= '0';
   CB.UP.EOP_N <= '0';
   wait for clkper;
   CB.UP.SOP_N <= '1';
   CB.UP.EOP_N <= '1';
   CB.UP.SRC_RDY_N <= '1';
   
   -- Recieve empty (head only) message from CB
   CB.UP.SRC_RDY_N <= '0';
   CB.UP.DATA <= X"5005";  -- Src_Id=5 & 0 & Endpoint diff buffer size=5
   CB.UP.SOP_N <= '0';
   CB.UP.EOP_N <= '0';
   wait for clkper;
   CB.UP.SOP_N <= '1';
   CB.UP.EOP_N <= '1';
   CB.UP.SRC_RDY_N <= '1';
   wait for 5*clkper;

   -- Recieve head + one word message from CB
   CB.UP.SRC_RDY_N <= '0';
   CB.UP.DATA <= X"3008";  -- Endpoint 3, 8 items freed
   CB.UP.SOP_N <= '0';
   wait for clkper;
   CB.UP.DATA <= X"3210";
   CB.UP.SOP_N <= '1';
   CB.UP.EOP_N <= '0';
   wait for clkper;
   CB.UP.SRC_RDY_N <= '1';
   CB.UP.EOP_N <= '1';

   -- -- Recieve head + two words message from CB
   -- CB.UP.SRC_RDY_N <= '0';
   -- CB.UP.DATA <= X"3000";  -- Endpoint 3, no items freed
   -- CB.UP.SOP_N <= '0';
   -- wait for clkper;
   -- CB.UP.DATA <= X"0001";
   -- CB.UP.SOP_N <= '1';
   -- wait for clkper;
   -- CB.UP.EOP_N <= '0';
   -- CB.UP.DATA <= X"0002";
   -- wait for clkper;
   -- CB.UP.SRC_RDY_N <= '1';
   -- CB.UP.EOP_N <= '1';
   -- wait for clkper;
-- 
   -- -- Recieve head + three words message from CB
   -- CB.UP.SRC_RDY_N <= '0';
   -- CB.UP.DATA <= X"3001";  -- Endpoint 3, 1 item freed
   -- CB.UP.SOP_N <= '0';
   -- wait for clkper;
   -- CB.UP.DATA <= X"0011";
   -- CB.UP.SOP_N <= '1';
   -- wait for clkper;
   -- CB.UP.DATA <= X"0012";
   -- wait for clkper;
   -- CB.UP.DATA <= X"0013";
   -- CB.UP.EOP_N <= '0';
   -- wait for clkper;
   -- CB.UP.SRC_RDY_N <= '1';
   -- CB.UP.EOP_N <= '1';
   -- -- Recieve head + four words message from CB
   -- CB.UP.SRC_RDY_N <= '0';
   -- CB.UP.DATA <= X"3002";  -- Endpoint 3, 2 item freed
   -- CB.UP.SOP_N <= '0';
   -- wait for clkper;
   -- CB.UP.DATA <= X"0021";
   -- CB.UP.SOP_N <= '1';
   -- wait for clkper;
   -- CB.UP.DATA <= X"0022";
   -- wait for clkper;
   -- CB.UP.DATA <= X"0023";
   -- wait for clkper;
   -- CB.UP.DATA <= X"0024";
   -- CB.UP.EOP_N <= '0';
   -- wait for clkper;
   -- CB.UP.SRC_RDY_N <= '1';
   -- CB.UP.EOP_N <= '1';
   
   wait for 5*clkper;

   -- PPC read info about recieved data
   CRD <= '1';
   CBE <= "1111";
   CADDR <= "00000011";
   wait for clkper;
   CRD <= '0';
   wait for 5*clkper;

   -- PPC read some data from RX queue
   QRD <= '1';
   QADDR <= "00011000";  -- Queue 3 word 0
   wait for clkper;
   QADDR <= "00011001";  -- Queue 3 word 1
   wait for clkper;
   QADDR <= "00011010";  -- Queue 3 word 2
   wait for clkper;
   QRD <= '0';
   wait for 5*clkper;

   --------------- Test vvv

   -- PPC release data from RX queue
   CWR <= '1';
   CBE <= "1111";
   CADDR <= "00000011";
   CDWR <= X"00000002"; -- 2 items
   wait for clkper;
   CWR <= '0';
   wait for 1*clkper;

   -- PPC read info about recieved data
   CRD <= '1';
   CBE <= "1111";
   CADDR <= "00000011";
   wait for clkper;
   CRD <= '0';
   wait for 5*clkper;

   -------------- Test ^^^

   -- PPC release data from RX queue
   CWR <= '1';
   CBE <= "1111";
   CADDR <= "00000011";
   CDWR <= X"0000000C"; -- 12 items
   wait for clkper;
   CWR <= '0';
   wait for 5*clkper;
   
   -- PPC read counters and masks
   wait for clkper;
   CRD <= '1';
   CADDR <= "00000000"; -- RX Counter 0
   wait for clkper;
   CADDR <= "00000011"; -- RX Counter 3
   wait for clkper;
   CADDR <= "00010011"; -- RX Start Pointer 3
   wait for clkper;
   CADDR <= "00100011"; -- RX End Pointer 3
   wait for clkper;
   CADDR <= "10000000"; -- RX Mask
   wait for clkper;
   CADDR <= "10000001"; -- TX Mask
   wait for clkper;
   CRD <= '0';
   wait for 5*clkper;
   
   -- PPC write into TX queue 5
   QWR <= '1';
   QADDR <= "10101000";
   QDWR <= X"0053005200510007";  -- 7 valid data words
   QBE <= "11111111";
   wait for clkper;
   QADDR <= "10101001";
   QDWR <= X"0057005600550054";
   wait for clkper;
   QWR <= '0';
   wait for 5*clkper;

   -- PPC write into queue counters
   CWR <= '1';
   CBE <= "1111";
   CADDR <= "01000101"; -- TX counter for queue 5
   CDWR <= X"00000008";
   wait for clkper;
   CWR <= '0';

   wait for 20*clkper;

   -- PPC write into TX queue 3
   QWR <= '1';
   QADDR <= "10011000";
   QDWR <= X"0003000200010004";  -- 4 valid data words
   QBE <= "11111111";
   wait for clkper;
   QADDR <= "10011001";
   QDWR <= X"0007000600050004";
   QBE <= "00001111";
   wait for clkper;
   QWR <= '0';
   wait for 5*clkper;

   -- PPC write into queue counters
   CWR <= '1';
   CBE <= "1111";
   CADDR <= "01000011"; -- TX counter for queue 3
   CDWR <= X"00000006";
   wait for clkper;
   CWR <= '0';

   -- Read that possibly interferes with transmitting
   wait for 2*clkper;
   CRD <= '1';
   CADDR <= "01000101"; -- TX counter for queue 3
   wait for 15*clkper;
   CRD <= '0';
   wait for 10*clkper;

   -- Recieve empty (head only) message from CB
   CB.UP.SRC_RDY_N <= '0';
   CB.UP.DATA <= X"5005";  -- Src_Id=5 & 0 & Endpoint diff buffer size=5
   CB.UP.SOP_N <= '0';
   CB.UP.EOP_N <= '0';
   wait for clkper;
   CB.UP.SOP_N <= '1';
   CB.UP.EOP_N <= '1';
   CB.UP.SRC_RDY_N <= '1';
   wait for 5*clkper;
   
   -- PPC write into TX queue 3
   QWR <= '1';
   QADDR <= "10011001";
   QDWR <= X"0031000100000000";  -- 1 valid data word
   QBE <= "11110000";
   wait for clkper;
   QWR <= '0';
   wait for 5*clkper;

   -- PPC write into queue counters
   CWR <= '1';
   CBE <= "1111";
   CADDR <= "01000011"; -- TX counter for queue 3
   CDWR <= X"00000002";
   wait for clkper;
   CWR <= '0';
   
   -- Recieve head + really long message from CB
   CB.UP.SRC_RDY_N <= '0';
   CB.UP.DATA <= X"6002";  -- Endpoint 6, 2 item freed
   CB.UP.SOP_N <= '0';
   CB.DOWN.DST_RDY_N <= '1';
   wait for clkper;
   CB.DOWN.DST_RDY_N <= '0';
   CB.UP.DATA <= X"6001";
   CB.UP.SOP_N <= '1';
   wait for clkper;
   CB.UP.DATA <= X"6002";
   CB.DOWN.DST_RDY_N <= '1';
   wait for clkper;
   CB.UP.DATA <= X"6003";
   wait for clkper;
   CB.DOWN.DST_RDY_N <= '0';
   CB.UP.DATA <= X"6004";
   wait for clkper;
   CB.UP.DATA <= X"6005";
   wait for clkper;
   CB.UP.DATA <= X"6006";
   CB.DOWN.DST_RDY_N <= '1';
   wait for clkper;
   CB.UP.DATA <= X"6007";
   CB.DOWN.DST_RDY_N <= '0';
   wait for clkper;
   CB.UP.DATA <= X"6008";
   wait for clkper;
   CB.UP.DATA <= X"6009";
   CB.DOWN.DST_RDY_N <= '1';
   wait for clkper;
   CB.UP.DATA <= X"600A";
   wait for clkper;
   CB.UP.DATA <= X"600B";
   CB.DOWN.DST_RDY_N <= '0';
   wait for clkper;
   CB.UP.DATA <= X"600C";
   wait for clkper;
   CB.UP.DATA <= X"600D";
   wait for clkper;
   CB.UP.DATA <= X"600E";
   wait for clkper;
   CB.UP.DATA <= X"600F";
   wait for clkper;
   CB.UP.DATA <= X"6010";
   CB.DOWN.DST_RDY_N <= '1';
   wait for clkper;
   CB.UP.DATA <= X"6011";
   CB.DOWN.DST_RDY_N <= '0';
   wait for clkper;
   CB.UP.DATA <= X"6012";
   wait for clkper;
   CB.UP.DATA <= X"6013";
   wait for clkper;
   CB.UP.DATA <= X"6014";
   wait for clkper;
   CB.UP.DATA <= X"6015";
   wait for clkper;
   CB.UP.DATA <= X"6016";
   wait for clkper;
   CB.UP.DATA <= X"6017";
   wait for clkper;
   CB.UP.DATA <= X"6018";
   CB.UP.EOP_N <= '0';
   wait for clkper;
   CB.UP.SRC_RDY_N <= '1';
   CB.UP.EOP_N <= '1';
   wait for 5*clkper;
   
   -- PPC read some data from RX queue
   QRD <= '1';
   QADDR <= "00110000";  -- Queue 6 word 0
   wait for clkper;
   QADDR <= "00110001";  -- Queue 6 word 1
   wait for clkper;
   QADDR <= "00110010";  -- Queue 6 word 2
   wait for clkper;
   QRD <= '0';
   wait for 50*clkper;

   -- PPC release data from RX queue
   CWR <= '1';
   CBE <= "1111";
   CADDR <= "00000110"; -- Queue 6
   CDWR <= X"00000018"; -- 0x18 items
   wait for clkper;
   CWR <= '0';
   wait for 80*clkper;

   CB.DOWN.DST_RDY_N <= '1';
   wait for 2*clkper;
   CB.DOWN.DST_RDY_N <= '0';

   wait;
end process;

end;
