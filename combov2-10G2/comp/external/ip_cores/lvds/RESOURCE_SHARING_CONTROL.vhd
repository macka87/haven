--/////////////////////////////////////////////////////////////////////////////
--
--    File Name:  RESOURCE_SHARING_CONTROL.vhd
--      Version:  1.0
--         Date:  05/19/06
--        Model:  Round Robin Channel Alignment
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
-- 
-- Summary:
--
-- The RESOURCE_SHARING_CONTROL module allocates the BIT_ALIGN_MACHINE
-- module to each of the 16 data channels of the interface.  Each channel 
-- must be aligned one at a time, such that the RESOURCE_SHARING_CONTROL module
-- must determine when training on a given channel is complete, and then 
-- switch the context to the next channel. 
--
------------------------------------------------------------------
-- Library declarations
--
-- Standard IEEE libraries
--
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

ENTITY RESOURCE_SHARING_CONTROL IS
   PORT (
      CHAN_SEL                : OUT std_logic_vector(3 DOWNTO 0);   
                               -- VECTOR INDICATING CURRENT CHANNEL BEING ALIGNED
      ALL_CHANNELS_ALIGNED    : OUT std_logic;   -- SIGNAL THAT ALL CHANNELS ARE ALIGNED
      DATA_ALIGNED            : IN std_logic;   
                               -- FLAG: ALIGNMENT DONE ON CURRENT CHANNEL, GO TO NEXT
      START_ALIGN             : OUT std_logic;   
                               -- SIGNAL THAT ALIGNMENT PROCESS MAY BEGIN ON NEXT CHANNEL
      CLK                     : IN std_logic;   -- CLOCK
      RST                     : IN std_logic);   -- RESET
END RESOURCE_SHARING_CONTROL;

ARCHITECTURE translated OF RESOURCE_SHARING_CONTROL IS

   COMPONENT count_to_128
      PORT (
         clk                     : IN  std_logic;
         rst                     : IN  std_logic;
         count                   : IN  std_logic;
         ud                      : IN  std_logic;
         counter_value           : OUT std_logic_vector(6 DOWNTO 0));
   END COMPONENT;

   COMPONENT count_to_16x
      PORT (
         clk                     : IN  std_logic;
         rst                     : IN  std_logic;
         count                   : IN  std_logic;
         counter_value           : OUT std_logic_vector(3 DOWNTO 0));
   END COMPONENT;


   SIGNAL COUNT_VALUE              :  std_logic_vector(6 DOWNTO 0);   
   SIGNAL UD_DELAY                 :  std_logic;   
   SIGNAL COUNT_DELAY              :  std_logic;   
   SIGNAL COUNT_CHAN               :  std_logic;   
   SIGNAL CS                       :  std_logic_vector(2 DOWNTO 0);   
   SIGNAL CHAN_SEL_INT             :  std_logic_vector(3 DOWNTO 0);   
   SIGNAL NS                       :  std_logic_vector(2 DOWNTO 0);   
   CONSTANT  INIT                  :  std_logic_vector(2 DOWNTO 0) := "000";   
   CONSTANT  INC_CHAN_SEL          :  std_logic_vector(2 DOWNTO 0) := "001";   
   CONSTANT  WAIT_8                :  std_logic_vector(2 DOWNTO 0) := "010";   
   CONSTANT  START_NEXT            :  std_logic_vector(2 DOWNTO 0) := "011";   
   CONSTANT  LAST_CHAN             :  std_logic_vector(2 DOWNTO 0) := "100";   
   CONSTANT  TRAIN_DONE            :  std_logic_vector(2 DOWNTO 0) := "101";   
   CONSTANT  IDLE                  :  std_logic_vector(2 DOWNTO 0) := "110";   
   CONSTANT  START_LAST            :  std_logic_vector(2 DOWNTO 0) := "111";   

BEGIN
   ALL_CHANNELS_ALIGNED <= (CS(2) AND NOT CS(1)) AND CS(0) ;
   CHAN_SEL <= CHAN_SEL_INT;

   delay_counter : count_to_128 
      PORT MAP (
         clk => CLK,
         rst => RST,
         count => COUNT_DELAY,
         ud => UD_DELAY,
         counter_value => COUNT_VALUE);   
   
   channel_counter : count_to_16x 
      PORT MAP (
         clk => CLK,
         rst => RST,
         count => COUNT_CHAN,
         counter_value => CHAN_SEL_INT);   
   

   --CURRENT STATE LOGIC
   
   PROCESS (CLK)
   BEGIN
      IF (CLK'EVENT AND CLK = '1') THEN
         IF (RST = '1') THEN
            CS <= INIT;    
         ELSE
            CS <= NS;    
         END IF;
      END IF;
   END PROCESS;

   --NEXT_STATE LOGIC
   
   PROCESS (CS, DATA_ALIGNED, COUNT_VALUE, CHAN_SEL_INT)
   BEGIN
      CASE CS IS
         WHEN INIT =>
                  IF (COUNT_VALUE < "0001000" OR DATA_ALIGNED = '0') 
                  THEN
                     NS <= INIT;    
                  ELSE
                     NS <= IDLE;    
                  END IF;
         WHEN IDLE =>
                  NS <= INC_CHAN_SEL;    
         WHEN INC_CHAN_SEL =>
                  NS <= WAIT_8;    
         WHEN WAIT_8 =>
                  IF (COUNT_VALUE < "0001000") THEN
                     NS <= WAIT_8;    
                  ELSE
                     IF (CHAN_SEL_INT = "1111") THEN
                        NS <= START_LAST;    
                     ELSE
                        NS <= START_NEXT;    
                     END IF;
                  END IF;
         WHEN START_NEXT =>
                  NS <= INIT;    
         WHEN START_LAST =>
                  NS <= LAST_CHAN;    
         WHEN LAST_CHAN =>
                  IF (COUNT_VALUE < "0001000" OR DATA_ALIGNED = '0') 
                  THEN
                     NS <= LAST_CHAN;    
                  ELSE
                     NS <= TRAIN_DONE;    
                  END IF;
         WHEN TRAIN_DONE =>
                  NS <= TRAIN_DONE;    
         WHEN OTHERS  =>
                  NS <= INIT;    
         
      END CASE;
   END PROCESS;

   --OUTPUT LOGIC
   
   PROCESS (CS)
   BEGIN
      CASE CS IS
         WHEN INIT =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '1';    
                  UD_DELAY <= '1';    
                  START_ALIGN  <= '0';    
         WHEN IDLE =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '0';    
                  UD_DELAY <= '0';    
                  START_ALIGN  <= '0';    
         WHEN INC_CHAN_SEL =>
                  COUNT_CHAN <= '1';    
                  COUNT_DELAY <= '0';    
                  UD_DELAY <= '0';    
                  START_ALIGN  <= '0';    
         WHEN WAIT_8 =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '1';    
                  UD_DELAY <= '1';    
                  START_ALIGN  <= '0';    
         WHEN START_NEXT =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '0';    
                  UD_DELAY <= '0';    
                  START_ALIGN  <= '1';    
         WHEN START_LAST =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '0';    
                  UD_DELAY <= '0';    
                  START_ALIGN  <= '1';    
         WHEN LAST_CHAN =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '1';    
                  UD_DELAY <= '1';    
                  START_ALIGN  <= '0';    
         WHEN TRAIN_DONE =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '0';    
                  UD_DELAY <= '0';    
                  START_ALIGN  <= '0';    
         WHEN OTHERS  =>
                  COUNT_CHAN <= '0';    
                  COUNT_DELAY <= '0';    
                  UD_DELAY <= '0';    
                  START_ALIGN  <= '0';    
         
      END CASE;
   END PROCESS;

END translated;
