--/////////////////////////////////////////////////////////////////////////////
--
--    File Name:  COUNT_TO_64.vhd
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

ENTITY COUNT_TO_64 IS
   PORT (
      --This module counts up/down between 0 to 63

      clk                     : IN std_logic;   
      rst                     : IN std_logic;   
      count                   : IN std_logic;   
      ud                      : IN std_logic;   
      counter_value           : OUT std_logic_vector(5 DOWNTO 0));   
END COUNT_TO_64;

ARCHITECTURE translated OF COUNT_TO_64 IS


   SIGNAL counter_value_preserver  :  std_logic_vector(5 DOWNTO 0);   
   --synthesis syn_noprune = 1
   SIGNAL counter_value_int  :  std_logic_vector(5 DOWNTO 0);   

BEGIN

   PROCESS (clk, rst)
      VARIABLE temp  : std_logic_vector(1 DOWNTO 0);
   BEGIN
      IF (rst = '1') THEN
         counter_value_int  <= "000000";    
      ELSIF (clk'EVENT AND clk = '1') THEN
         temp := count & ud;
         CASE temp IS
            WHEN "00" =>
                     counter_value_int <= counter_value_preserver;    
            WHEN "01" =>
                     counter_value_int <= counter_value_preserver;    
            WHEN "10" =>
                     counter_value_int  <= counter_value_preserver - "000001";    
            WHEN "11" =>
                     counter_value_int  <= counter_value_preserver + "000001";    
            WHEN OTHERS  =>
                     counter_value_int  <= "000000";    
            
         END CASE;
      END IF;
      --counter_value_int  <= counter_value_int ;
   END PROCESS;
   counter_value_preserver <= counter_value_int  ;

      counter_value <= counter_value_int ;

END translated;
