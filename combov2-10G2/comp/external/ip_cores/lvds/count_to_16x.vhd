--/////////////////////////////////////////////////////////////////////////////
--
--    File Name:  count_to_16x.vhd
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

ENTITY count_to_16x IS
   PORT (
      --This module counts from 0 to 16

      clk                     : IN std_logic;   
      rst                     : IN std_logic;   
      count                   : IN std_logic;   
      counter_value           : OUT std_logic_vector(3 DOWNTO 0));   
END count_to_16x;

ARCHITECTURE translated OF count_to_16x IS


   SIGNAL counter_value_preserver  :  std_logic_vector(3 DOWNTO 0);   
   SIGNAL temp                     :  std_logic_vector(3 DOWNTO 0);   

BEGIN
   --counter_value <= counter_value ;
   temp  <= counter_value_preserver + "0001" WHEN (count) = '1' 
   ELSE counter_value_preserver;
   counter_value  <= temp  ;

   PROCESS (clk, rst)
      --VARIABLE counter_value_preserver   : std_logic_vector(3 DOWNTO 0);
   BEGIN
      IF (rst = '1') THEN
         counter_value_preserver  <= "0000";    
      ELSIF (clk'EVENT AND clk = '1') THEN
         counter_value_preserver  <= temp ;    
      END IF;
      --counter_value_preserver <= counter_value_preserver ;
   END PROCESS;

END translated;
