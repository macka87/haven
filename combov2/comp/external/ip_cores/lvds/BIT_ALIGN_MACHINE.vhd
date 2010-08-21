--/////////////////////////////////////////////////////////////////////////////
--
--    File Name:  BIT_ALIGN_MACHINE.vhd
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
-- 
-- Summary:
--
-- The BIT_ALIGN_MACHINE module analyzes the data input of a single channel
-- to determine the optimal clock/data relationship for that channel.  By
-- dynamically changing the delay of the data channel (with respect to the 
-- sampling clock), the machine places the sampling point at the center of
-- the data eye.
--  
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

ENTITY BIT_ALIGN_MACHINE IS
   PORT (
      RXCLKDIV         : IN std_logic;   -- RX PARALLEL SIDE CLOCK
      RXDATA           : IN std_logic_vector(7 DOWNTO 0);   -- DATA FROM ONE CHANNEL ONLY
      RST              : IN std_logic;   -- RESET ALL CIRCUITRY IN MACHINE
      USE_BITSLIP      : IN std_logic;   -- OPTION TO BYPASS/INCLUDE BITSLIP FUNCTION
      SAP              : IN std_logic;   -- INDICATES THAT DATA IS STABLE AFTER CHANNEL TRANSITION
                                        --E.G. MACHINE FINISHES CHANNEL 12 AND GOES ON TO 13
      INC              : OUT std_logic;   -- MACHINE ISSUES DELAY INCREMENT TO APPROPRIATE DATA CHANNEL
      ICE              : OUT std_logic;   -- MACHINE ISSUES DELAY DECREMENT TO APPROPRIATE DATA CHANNEL
      BITSLIP          : OUT std_logic;   -- MACHINE ISSUES BITSLIP COMMAND TO APPROPRIATE DATA CHANNEL
      DATA_ALIGNED     : OUT std_logic);   -- FLAG INDICATING ALIGNMENT COMPLETE ON THIS CHANNEL
END BIT_ALIGN_MACHINE;

ARCHITECTURE translated OF BIT_ALIGN_MACHINE IS

------------------------------------------------------------------------------------
--
-- Component Declaration

component count_to_128 
   PORT (
      clk                     : IN std_logic;   
      rst                     : IN std_logic;   
      count                   : IN std_logic;   
      ud                      : IN std_logic;   
      counter_value           : OUT std_logic_vector(6 DOWNTO 0));   
end component;


component seven_bit_reg_w_ce 
   PORT (
      Q                       : OUT std_logic_vector(6 DOWNTO 0);   
      CLK                     : IN std_logic;   
      CE                      : IN std_logic;   
      D                       : IN std_logic_vector(6 DOWNTO 0);   
      RST                     : IN std_logic);   
end component;

------------------------------------------------------------------------------------
--
-- Signal Declaration

   SIGNAL COUNT                    :  std_logic;   
   SIGNAL UD                       :  std_logic;   
   SIGNAL STORE                    :  std_logic;   
   SIGNAL STORE_DATA_PREV          :  std_logic;   
   SIGNAL COUNT_SAMPLE             :  std_logic;   
   SIGNAL UD_SAMPLE                :  std_logic;   
   SIGNAL CURRENT_STATE            :  std_logic_vector(4 DOWNTO 0);   
   SIGNAL NEXT_STATE               :  std_logic_vector(4 DOWNTO 0);   
   SIGNAL COUNT_VALUE              :  std_logic_vector(6 DOWNTO 0);   
   SIGNAL HALF_DATA_EYE            :  std_logic_vector(6 DOWNTO 0);   
   SIGNAL RXDATA_PREV              :  std_logic_vector(7 DOWNTO 0);   
   SIGNAL COUNT_VALUE_SAMPLE       :  std_logic_vector(6 DOWNTO 0);   
   SIGNAL CVS                      :  std_logic_vector(6 DOWNTO 0);   
   SIGNAL CVS_ADJUSTED             :  std_logic_vector(6 DOWNTO 0);   
   SIGNAL CHECK_PATTERN            :  std_logic_vector(7 DOWNTO 0);   
   SIGNAL DATA_ALIGNEDx            :  std_logic;   

BEGIN


   machine_counter_total : count_to_128 
      PORT MAP (
         clk => RXCLKDIV,
         rst => RST,
         count => COUNT_SAMPLE,
         ud => UD_SAMPLE,
         counter_value => COUNT_VALUE_SAMPLE);   
   
   machine_counter : count_to_128 
      PORT MAP (
         clk => RXCLKDIV,
         rst => RST,
         count => COUNT,
         ud => UD,
         counter_value => COUNT_VALUE);   
   
   tap_reserve : seven_bit_reg_w_ce 
      PORT MAP (
         Q => CVS,
         CLK => RXCLKDIV,
         CE => STORE,
         D => COUNT_VALUE,
         RST => RST);   
   
   count_reg : FDR 
      PORT MAP (
         Q => DATA_ALIGNED,
         C => RXCLKDIV,
         D => DATA_ALIGNEDx,
         R => RST);   
   
   
   --STORE ENTIRE DATA BUS FOR COMPARISON AFTER CHANGING DELAY

   bit0 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(0),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(0),
         R => RST);   
   
   bit1 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(1),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(1),
         R => RST);   
   
   bit2 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(2),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(2),
         R => RST);   
   
   bit3 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(3),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(3),
         R => RST);   
   
   bit4 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(4),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(4),
         R => RST);   
   
   bit5 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(5),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(5),
         R => RST);   
   
   bit6 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(6),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(6),
         R => RST);   
   
   bit7 : FDRE 
      PORT MAP (
         Q => RXDATA_PREV(7),
         C => RXCLKDIV,
         CE => STORE_DATA_PREV,
         D => RXDATA(7),
         R => RST);   
   
   DATA_ALIGNEDx <= (((NOT CURRENT_STATE(4) AND NOT CURRENT_STATE(3)) 
   AND CURRENT_STATE(2)) AND CURRENT_STATE(1)) AND CURRENT_STATE(0) ;
   CHECK_PATTERN <= "00101100";

 --CVS IS A SNAPSHOT OF THE TAP COUNTER.  IT'S VALUE IS THE SIZE OF THE DATA VALID WINDOW
 --OUR INTENTION IS TO DECREMENT THE DELAY TO 1/2 THIS VALUE TO BE AT THE CENTER OF THE EYE.
 --SINCE IT MAY BE POSSIBLE TO HAVE AN ODD COUNTER VALUE, THE HALVED VALUE WILL BE A DECIMAL.
 --IN CASES WHERE CVS IS A DECIMAL, WE WILL ROUND UP.  E.G CVS = 4.5, SO DECREMENT 5 TAPS.
 --CVS_ADJUSTED AND HALF_DATA_EYE ARE FINE TUNED ADJUSTMENTS FOR OPTIMAL OPERATION AT HIGH RATES

   CVS_ADJUSTED <= CVS - "0000001" ;
   HALF_DATA_EYE <= '0' & CVS_ADJUSTED(6 DOWNTO 1) + CVS_ADJUSTED(0) ;

   --CURRENT STATE LOGIC
   
   PROCESS (RXCLKDIV, RST)
   BEGIN
      IF (RST = '1') THEN
         CURRENT_STATE <= "00000";    
      ELSIF (RXCLKDIV'EVENT AND RXCLKDIV = '1') THEN
         CURRENT_STATE <= NEXT_STATE;    
      END IF;
   END PROCESS;

   --NEXT_STATE LOGIC
   
   PROCESS (CURRENT_STATE, COUNT_VALUE, USE_BITSLIP, RXDATA, 
   CHECK_PATTERN, RXDATA_PREV, COUNT_VALUE_SAMPLE, SAP, HALF_DATA_EYE)
   BEGIN
      CASE CURRENT_STATE IS
         WHEN "00000" =>
                  IF (SAP = '0') THEN --RST STATE                     
                     NEXT_STATE <= "00001";    
                  ELSE
                     NEXT_STATE <= "00000";    
                  END IF;
         WHEN "00001" => --INITIAL STATE, SAMPLE TRAINING BIT                
                  IF (RXDATA_PREV /= RXDATA) THEN
                     NEXT_STATE <= "01111";    
                  ELSE
                     NEXT_STATE <= "01000";    
                  END IF;
         WHEN "01000" =>   --CHECK SAMPLE TO SEE IF IT IS ON A TRANSITION                  
                  IF (RXDATA_PREV /= RXDATA) THEN
                     NEXT_STATE <= "01111";    
                  ELSE
                     IF (COUNT_VALUE_SAMPLE > "0001111") THEN
                        NEXT_STATE <= "01011";    
                     ELSE
                        NEXT_STATE <= "01000";    
                     END IF;
                  END IF;
         WHEN "01111" =>   --IF SAMPLED POINT IS TRANSITION, EDGE IS FOUND, 
                           --SO INC DELAY TO EXIT TRANSITION                  
                  NEXT_STATE <= "01101";    
         WHEN "01101" =>   --WAIT 16 CYCLES WHILE APPLYING BITSLIP TO FIND CHECK_PATTERN                  
                  IF (COUNT_VALUE_SAMPLE > "0001110") THEN
                     NEXT_STATE <= "01111";    
                  ELSE
                     IF (RXDATA = CHECK_PATTERN) THEN   --IF CHECK_PATTERN IS FOUND, 
                                                 -- WE ARE CLOSE TO END OF TRANSITION                        
                        NEXT_STATE <= "01100";    
                     ELSE
                        NEXT_STATE <= "01101";    
                     END IF;
                  END IF;
         WHEN "01100" =>     --IDLE (NEEDED FOR COUNTER RESET BEFORE NEXT STATE)                  
                  NEXT_STATE <= "10000";    
         WHEN "10000" =>     --IDLE (NEEDED FOR STABILIZATION)                  
                  NEXT_STATE <= "00010";    
         WHEN "00010" =>     --CHECK SAMPLE AGAIN TO SEE IF WE HAVE EXITED TRANSITION                 
                  IF (COUNT_VALUE_SAMPLE < "0000011") THEN 
                              --ALLOW TIME FOR BITSLIP OP TO STABILIZE                   
                     NEXT_STATE <= "00010";    
                  ELSE
                     IF (RXDATA_PREV /= RXDATA) THEN
                        NEXT_STATE <= "01111";    
                     ELSE
                        IF (COUNT_VALUE_SAMPLE > "1111110") THEN 
                               --SCAN FOR STABILITY FOR 128 CYCLES                           
                           NEXT_STATE <= "01110";    
                        ELSE
                           NEXT_STATE <= "00010";    
                        END IF;
                     END IF;
                  END IF;
         WHEN "01011" =>    --INITIAL STATE WAS STABLE, SO INC ONCE TO SEARCH FOR TRANS                  
                  NEXT_STATE <= "00100";    
         WHEN "00100" =>    --WAIT 8 CYCLES, COMPARE RXDATA WITH PREVIOUS DATA                  
                  IF (COUNT_VALUE_SAMPLE < "0000111") THEN
                     NEXT_STATE <= "00100";    
                  ELSE
                     IF (RXDATA_PREV /= RXDATA) THEN
                        NEXT_STATE <= "01111";    
                     ELSE
                        NEXT_STATE <= "01011";    
                     END IF;
                  END IF;
         WHEN "01110" => --DATA IS STABLE AFTER FINDING 1ST TRANS, COUNT 1 TO INCLUDE LAST INC                  
                  NEXT_STATE <= "01001";    
         WHEN "01001" => --INC ONCE TO LOOK FOR 2ND TRANS                 
                  NEXT_STATE <= "00011";    
         WHEN "00011" => --WAIT 8 CYCLES, COMPARE RXDATA WITH PREVIOUS DATA                  
                  IF (COUNT_VALUE_SAMPLE < "0000111") THEN
                     NEXT_STATE <= "00011";    
                  ELSE
                     IF (RXDATA_PREV /= RXDATA) THEN
                        NEXT_STATE <= "10010";    
                     ELSE
                        NEXT_STATE <= "01001";    
                     END IF;
                  END IF;
         WHEN "10010" =>   --IDLE (NEEDED FOR COUNTER RESET BEFORE NEXT STATE)                  
                  NEXT_STATE <= "01010";    
         WHEN "01010" =>   --DECREMENT TO MIDDLE OF DATA EYE                  
                  IF (COUNT_VALUE_SAMPLE < HALF_DATA_EYE - "0000001") 
                  THEN
                     NEXT_STATE <= "01010";    
                  ELSE
                     NEXT_STATE <= "00101";    
                  END IF;
         WHEN "00101" =>    --SAMPLE PATTERN 16 TIMES TO SEE IF WORD ALIGNMENT NEEDED                  
                  IF (USE_BITSLIP = '0') 
                  THEN
                     NEXT_STATE <= "00111";    
                  ELSE
                     IF (COUNT_VALUE < "0001111") THEN
                        NEXT_STATE <= "00101";    
                  ELSE
                     IF (RXDATA = CHECK_PATTERN) THEN
                           NEXT_STATE <= "00111";
                  ELSE
                     NEXT_STATE <= "00110"; 
                        END IF;
                     END IF;
                  END IF;
         WHEN "00110" =>  --INITIATE 1 BITSLIP                  
                  NEXT_STATE <= "00101";    
         WHEN "00111" =>
                  IF (SAP = '0') THEN         --TRAINING COMPLETE FOR THIS CHANNEL                     
                     NEXT_STATE <= "00111";    
                  ELSE
                     NEXT_STATE <= "00000";    
                  END IF;
         WHEN OTHERS  =>
                  NEXT_STATE <= "00000";    
         
      END CASE;
   END PROCESS;

   --OUTPUT LOGIC
   
   PROCESS (CURRENT_STATE)
   BEGIN
      CASE CURRENT_STATE IS
         WHEN "00000" =>  
                  --RST STATE   
               
                  INC <= '0';    
                  ICE <= '0';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "00001" =>
                  --INITIAL STATE, SAMPLE TRAINING BIT
                  
                  INC <= '0';    
                  ICE   <= '0';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP   <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "01000" =>
                  --CHECK SAMPLE TO SEE IF IT IS ON A TRANSITION
                  
                  INC   <= '0';    
                  ICE   <= '0';    
                  COUNT  <= '0';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP   <= '0';    
                  COUNT_SAMPLE  <= '1';    
                  UD_SAMPLE  <= '1';    
         WHEN "01111" =>
                  --IF SAMPLED POINT IS TRANSITION, EDGE IS FOUND, SO INC DELAY TO EXIT TRANSITION
                  
                  INC   <= '1';    
                  ICE   <= '1';    
                  COUNT  <= '0';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP   <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "01101" =>
                  --WAIT 16 CYCLES WHILE APPLYING BITSLIP TO FIND CHECK_PATTERN
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '1';    
                  COUNT_SAMPLE  <= '1';    
                  UD_SAMPLE  <= '1';    
         WHEN "01100" =>
                  --IDLE (NEEDED FOR COUNTER RESET BEFORE NEXT STATE)
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "10000" =>
                  --IDLE (NEEDED FOR STABILIZATION)
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "00010" =>
                  --CHECK SAMPLE AGAIN TO SEE IF WE HAVE EXITED TRANSITION
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '1';    
                  UD_SAMPLE  <= '1';    
         WHEN "01011" =>
                  --INITIAL STATE WAS STABLE, SO INC ONCE TO SEARCH FOR TRANS
                  
                  INC  <= '1';    
                  ICE  <= '1';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "00100" =>
                  --WAIT 8 CYCLES, COMPARE RXDATA WITH PREVIOUS DATA
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '0';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '1';    
                  UD_SAMPLE  <= '1';    
         WHEN "01110" =>
                  --DATA IS STABLE AFTER FINDING 1ST TRANS, COUNT 1 TO INCLUDE LAST INC
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '1';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "01001" =>
                  --INC ONCE TO LOOK FOR 2ND TRANS
                  
                  INC  <= '1';    
                  ICE  <= '1';    
                  COUNT  <= '1';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "00011" =>
                  --WAIT 8 CYCLES, COMPARE RXDATA WITH PREVIOUS DATA
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '1';    
                  STORE  <= '1';    
                  STORE_DATA_PREV  <= '0';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '1';    
                  UD_SAMPLE  <= '1';    
         WHEN "10010" =>
                  --IDLE (NEEDED FOR COUNTER RESET BEFORE NEXT STATE)
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "01010" =>
                  --DECREMENT TO CENTER OF DATA EYE
                  
                  INC  <= '0';    
                  ICE  <= '1';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '1';    
                  UD_SAMPLE  <= '1';    
         WHEN "00101" =>
                  --SAMPLE PATTERN 16 TIMES TO SEE IF WORD ALIGNMENT NEEDED
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '1';    
                  UD  <= '1';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "00110" =>
                  --INITIATE 1 BITSLIP
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '1';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN "00111" =>
                  --TRAINING COMPLETE ON THIS CHANNEL
                  
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         WHEN OTHERS  =>
                  INC  <= '0';    
                  ICE  <= '0';    
                  COUNT  <= '0';    
                  UD  <= '0';    
                  STORE  <= '0';    
                  STORE_DATA_PREV  <= '1';    
                  BITSLIP  <= '0';    
                  COUNT_SAMPLE  <= '0';    
                  UD_SAMPLE  <= '0';    
         
      END CASE;
   END PROCESS;

END translated;
