--/////////////////////////////////////////////////////////////////////////////
--
--    File Name:  seven_bit_reg_w_ce.vhd
--      Version:  1.0
--         Date:  05/19/06
--        Model:  Channel Alignment Module
--
--      Company:  Xilinx, Inc.
--  Contributor:  APD Applications Group
--
--   Disclaimer:  XILINX IS PROVIDING THIS DESIGN, CODE, OR
--                INFORMATION "AS IS" SOLELY FOR USE IN DEVELOPING
--                PROGRAMS AND SOLUTIONS FOR XILINX DEVICES.  BY
--                PROVIDING THIS DESIGN, CODE, OR INFORMATION AS
--                ONE POSSIBLE IMPLEMENTATION OF THIS FEATURE,
--                APPLICATION OR STANDARD, XILINX IS MAKING NO
--                REPRESENTATION THAT THIS IMPLEMENTATION IS FREE
--                FROM ANY CLAIMS OF INFRINGEMENT, AND YOU ARE
--                RESPONSIBLE FOR OBTAINING ANY RIGHTS YOU MAY
--                REQUIRE FOR YOUR IMPLEMENTATION.  XILINX
--                EXPRESSLY DISCLAIMS ANY WARRANTY WHATSOEVER WITH
--                RESPECT TO THE ADEQUACY OF THE IMPLEMENTATION,
--                INCLUDING BUT NOT LIMITED TO ANY WARRANTIES OR
--                REPRESENTATIONS THAT THIS IMPLEMENTATION IS FREE
--                FROM CLAIMS OF INFRINGEMENT, IMPLIED WARRANTIES
--                OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
--                PURPOSE.
--
--                (c) Copyright 2006 Xilinx, Inc.
--                All rights reserved.
--
--/////////////////////////////////////////////////////////////////////////////
------------------------------------------------------------------------------------
--
-- Library declarations
--
-- Standard IEEE libraries
--
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
library unisim;
use unisim.vcomponents.all;
--

ENTITY seven_bit_reg_w_ce IS
   PORT (
      Q                       : OUT std_logic_vector(6 DOWNTO 0);   
      CLK                     : IN std_logic;   
      CE                      : IN std_logic;   
      D                       : IN std_logic_vector(6 DOWNTO 0);   
      RST                     : IN std_logic);   
END seven_bit_reg_w_ce;

ARCHITECTURE translated OF seven_bit_reg_w_ce IS



BEGIN
 
   bit0 : FDRE 
      PORT MAP (
         Q => Q(0),
         C => CLK,
         CE => CE,
         D => D(0),
         R => RST);   
   
   bit1 : FDRE 
      PORT MAP (
         Q => Q(1),
         C => CLK,
         CE => CE,
         D => D(1),
         R => RST);   
   
   bit2 : FDRE 
      PORT MAP (
         Q => Q(2),
         C => CLK,
         CE => CE,
         D => D(2),
         R => RST);   
   
   bit3 : FDRE 
      PORT MAP (
         Q => Q(3),
         C => CLK,
         CE => CE,
         D => D(3),
         R => RST);   
   
   bit4 : FDRE 
      PORT MAP (
         Q => Q(4),
         C => CLK,
         CE => CE,
         D => D(4),
         R => RST);   
   
   bit5 : FDRE 
      PORT MAP (
         Q => Q(5),
         C => CLK,
         CE => CE,
         D => D(5),
         R => RST);   
   
   bit6 : FDRE 
      PORT MAP (
         Q => Q(6),
         C => CLK,
         CE => CE,
         D => D(6),
         R => RST);   
   

END translated;
