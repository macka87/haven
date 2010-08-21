--
--/////////////////////////////////////////////////////////////////////////////
--
--    File Name:  DDR_8TO1_16CHAN_TX.vhd
--      Version:  1.0
--         Date:  05/19/06
--        Model:  XAPP855 LVDS Transmitter Module
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
-- The DDR_8TO1_16CHAN_TX module contains all components in the XAPP855 LVDS Transmitter,
-- including 16 channels of LVDS data, one channel of LVDS clock, and a multiplexer
-- that selects between a training pattern and user data.
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
library unisim;
use unisim.vcomponents.all;
--
ENTITY DDR_8TO1_16CHAN_TX IS
   PORT (
      DATA_TX_P               : OUT std_logic_vector(15 DOWNTO 0);   -- SERIAL SIDE TX DATA (P)
      DATA_TX_N               : OUT std_logic_vector(15 DOWNTO 0);   -- SERIAL SIDE TX DATA (N)
      CLOCK_TX_P              : OUT std_logic;   -- FORWARDED CLOCK TO RX (P)
      CLOCK_TX_N              : OUT std_logic;   -- FORWARDED CLOCK TO RX (N)
      TXCLK                   : IN std_logic;   -- SERIAL SIDE TX CLOCK
      TXCLKDIV                : IN std_logic;   -- PARALLEL SIDE TX CLOCK (DIVIDED FROM TXCLK)
      DATA_TO_OSERDES         : IN std_logic_vector(127 DOWNTO 0);   -- PARALLEL SIDE TX DATA
      RESET                   : IN std_logic;   -- TX DOMAIN RESET
      TRAINING_DONE           : IN std_logic);   -- FLAG FROM RECEIVER INDICATING ALIGNMENT
END DDR_8TO1_16CHAN_TX;

ARCHITECTURE translated OF DDR_8TO1_16CHAN_TX IS


   SIGNAL TX_CLOCK_PREBUF          :  std_logic;   
   SIGNAL TX_DATA_PREBUF           :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL SHIFT1                   :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL SHIFT2                   :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL DATA_TO_OSERDES_REG      :  std_logic_vector(127 DOWNTO 0);   

BEGIN


   --DATA SOURCE: TRAINING PAT OR PRBS	
   --IF NO FEEDBACK CONTROLS FROM RX ARE DESIRED, THE TX CAN BE SET TO SEND THE 
   --TRAINING PATTERN FOR A FIXED AMOUNT OF TIME, AFTER WHICH IT AUTOMATICALLY
   --ASSUMES THAT TRAINING IS COMPLETE AND BEGINS SENDING USER DATA.
   
   PROCESS (TXCLKDIV)
   BEGIN
      IF (TXCLKDIV'EVENT AND TXCLKDIV = '1') THEN
         IF (TRAINING_DONE = '1') THEN
            DATA_TO_OSERDES_REG <= DATA_TO_OSERDES;    -- PRBS
         ELSE
            DATA_TO_OSERDES_REG <= "00101100001011000010110000101100001011000010110000101100001011000010110000101100001011000010110000101100001011000010110000101100";    -- TRAINING PATTERN
         END IF;
      END IF;
   END PROCESS;
   
   --FORWARDED CLOCK	

   ODDR_TX_CLOCK : ODDR 
      GENERIC MAP(
         DDR_CLK_EDGE => "OPPOSITE_EDGE", INIT => '0', SRTYPE => "ASYNC")
      PORT MAP (
         Q => TX_CLOCK_PREBUF,
         C => TXCLK,
         CE => '1',
         D1 => '1',
         D2 => '0',
         R => '0',
         S => '0');   
   
   
   --FORWARDED CLOCK OUTPUT BUFFER

   OBUFDS_TX_CLOCK : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => CLOCK_TX_P,
         OB => CLOCK_TX_N,
         I => TX_CLOCK_PREBUF);   
   
   
   --MASTER OSERDES IN DATA PATH

   OSERDES_TX_DATA_00 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(00),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(000),
         D2 => DATA_TO_OSERDES_REG(001),
         D3 => DATA_TO_OSERDES_REG(002),
         D4 => DATA_TO_OSERDES_REG(003),
         D5 => DATA_TO_OSERDES_REG(004),
         D6 => DATA_TO_OSERDES_REG(005),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(00),
         SHIFTIN2 => SHIFT2(00),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_01 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(01),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(008),
         D2 => DATA_TO_OSERDES_REG(009),
         D3 => DATA_TO_OSERDES_REG(010),
         D4 => DATA_TO_OSERDES_REG(011),
         D5 => DATA_TO_OSERDES_REG(012),
         D6 => DATA_TO_OSERDES_REG(013),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(01),
         SHIFTIN2 => SHIFT2(01),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_02 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(02),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(016),
         D2 => DATA_TO_OSERDES_REG(017),
         D3 => DATA_TO_OSERDES_REG(018),
         D4 => DATA_TO_OSERDES_REG(019),
         D5 => DATA_TO_OSERDES_REG(020),
         D6 => DATA_TO_OSERDES_REG(021),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(02),
         SHIFTIN2 => SHIFT2(02),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_03 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(03),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(024),
         D2 => DATA_TO_OSERDES_REG(025),
         D3 => DATA_TO_OSERDES_REG(026),
         D4 => DATA_TO_OSERDES_REG(027),
         D5 => DATA_TO_OSERDES_REG(028),
         D6 => DATA_TO_OSERDES_REG(029),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(03),
         SHIFTIN2 => SHIFT2(03),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_04 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(04),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(032),
         D2 => DATA_TO_OSERDES_REG(033),
         D3 => DATA_TO_OSERDES_REG(034),
         D4 => DATA_TO_OSERDES_REG(035),
         D5 => DATA_TO_OSERDES_REG(036),
         D6 => DATA_TO_OSERDES_REG(037),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(04),
         SHIFTIN2 => SHIFT2(04),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_05 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(05),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(040),
         D2 => DATA_TO_OSERDES_REG(041),
         D3 => DATA_TO_OSERDES_REG(042),
         D4 => DATA_TO_OSERDES_REG(043),
         D5 => DATA_TO_OSERDES_REG(044),
         D6 => DATA_TO_OSERDES_REG(045),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(05),
         SHIFTIN2 => SHIFT2(05),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_06 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(06),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(048),
         D2 => DATA_TO_OSERDES_REG(049),
         D3 => DATA_TO_OSERDES_REG(050),
         D4 => DATA_TO_OSERDES_REG(051),
         D5 => DATA_TO_OSERDES_REG(052),
         D6 => DATA_TO_OSERDES_REG(053),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(06),
         SHIFTIN2 => SHIFT2(06),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_07 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1)
      PORT MAP (
         OQ => TX_DATA_PREBUF(07),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(056),
         D2 => DATA_TO_OSERDES_REG(057),
         D3 => DATA_TO_OSERDES_REG(058),
         D4 => DATA_TO_OSERDES_REG(059),
         D5 => DATA_TO_OSERDES_REG(060),
         D6 => DATA_TO_OSERDES_REG(061),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(07),
         SHIFTIN2 => SHIFT2(07),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_08 : OSERDES 
     GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 
      PORT MAP (
         OQ => TX_DATA_PREBUF(08),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(064),
         D2 => DATA_TO_OSERDES_REG(065),
         D3 => DATA_TO_OSERDES_REG(066),
         D4 => DATA_TO_OSERDES_REG(067),
         D5 => DATA_TO_OSERDES_REG(068),
         D6 => DATA_TO_OSERDES_REG(069),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(08),
         SHIFTIN2 => SHIFT2(08),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_09 : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => TX_DATA_PREBUF(09),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(072),
         D2 => DATA_TO_OSERDES_REG(073),
         D3 => DATA_TO_OSERDES_REG(074),
         D4 => DATA_TO_OSERDES_REG(075),
         D5 => DATA_TO_OSERDES_REG(076),
         D6 => DATA_TO_OSERDES_REG(077),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(09),
         SHIFTIN2 => SHIFT2(09),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_10 : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => TX_DATA_PREBUF(10),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(080),
         D2 => DATA_TO_OSERDES_REG(081),
         D3 => DATA_TO_OSERDES_REG(082),
         D4 => DATA_TO_OSERDES_REG(083),
         D5 => DATA_TO_OSERDES_REG(084),
         D6 => DATA_TO_OSERDES_REG(085),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(10),
         SHIFTIN2 => SHIFT2(10),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_11 : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => TX_DATA_PREBUF(11),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(088),
         D2 => DATA_TO_OSERDES_REG(089),
         D3 => DATA_TO_OSERDES_REG(090),
         D4 => DATA_TO_OSERDES_REG(091),
         D5 => DATA_TO_OSERDES_REG(092),
         D6 => DATA_TO_OSERDES_REG(093),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(11),
         SHIFTIN2 => SHIFT2(11),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_12 : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => TX_DATA_PREBUF(12),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(096),
         D2 => DATA_TO_OSERDES_REG(097),
         D3 => DATA_TO_OSERDES_REG(098),
         D4 => DATA_TO_OSERDES_REG(099),
         D5 => DATA_TO_OSERDES_REG(100),
         D6 => DATA_TO_OSERDES_REG(101),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(12),
         SHIFTIN2 => SHIFT2(12),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_13 : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => TX_DATA_PREBUF(13),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(104),
         D2 => DATA_TO_OSERDES_REG(105),
         D3 => DATA_TO_OSERDES_REG(106),
         D4 => DATA_TO_OSERDES_REG(107),
         D5 => DATA_TO_OSERDES_REG(108),
         D6 => DATA_TO_OSERDES_REG(109),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(13),
         SHIFTIN2 => SHIFT2(13),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_14 : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => TX_DATA_PREBUF(14),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(112),
         D2 => DATA_TO_OSERDES_REG(113),
         D3 => DATA_TO_OSERDES_REG(114),
         D4 => DATA_TO_OSERDES_REG(115),
         D5 => DATA_TO_OSERDES_REG(116),
         D6 => DATA_TO_OSERDES_REG(117),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(14),
         SHIFTIN2 => SHIFT2(14),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_15 : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "MASTER", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => TX_DATA_PREBUF(15),
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => DATA_TO_OSERDES_REG(120),
         D2 => DATA_TO_OSERDES_REG(121),
         D3 => DATA_TO_OSERDES_REG(122),
         D4 => DATA_TO_OSERDES_REG(123),
         D5 => DATA_TO_OSERDES_REG(124),
         D6 => DATA_TO_OSERDES_REG(125),
         OCE => '1',
         REV => '0',
         SHIFTIN1 => SHIFT1(15),
         SHIFTIN2 => SHIFT2(15),
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   --SLAVE OSERDES IN DATA PATH

   OSERDES_TX_DATA_00S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(00),
         SHIFTOUT2 => SHIFT2(00),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(006),
         D4 => DATA_TO_OSERDES_REG(007),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_01S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(01),
         SHIFTOUT2 => SHIFT2(01),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(014),
         D4 => DATA_TO_OSERDES_REG(015),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_02S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(02),
         SHIFTOUT2 => SHIFT2(02),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(022),
         D4 => DATA_TO_OSERDES_REG(023),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_03S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(03),
         SHIFTOUT2 => SHIFT2(03),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(030),
         D4 => DATA_TO_OSERDES_REG(031),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_04S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(04),
         SHIFTOUT2 => SHIFT2(04),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(038),
         D4 => DATA_TO_OSERDES_REG(039),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_05S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(05),
         SHIFTOUT2 => SHIFT2(05),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(046),
         D4 => DATA_TO_OSERDES_REG(047),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_06S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(06),
         SHIFTOUT2 => SHIFT2(06),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(054),
         D4 => DATA_TO_OSERDES_REG(055),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_07S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(07),
         SHIFTOUT2 => SHIFT2(07),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(062),
         D4 => DATA_TO_OSERDES_REG(063),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_08S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(08),
         SHIFTOUT2 => SHIFT2(08),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(070),
         D4 => DATA_TO_OSERDES_REG(071),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_09S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(09),
         SHIFTOUT2 => SHIFT2(09),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(078),
         D4 => DATA_TO_OSERDES_REG(079),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_10S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(10),
         SHIFTOUT2 => SHIFT2(10),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(086),
         D4 => DATA_TO_OSERDES_REG(087),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_11S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(11),
         SHIFTOUT2 => SHIFT2(11),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(094),
         D4 => DATA_TO_OSERDES_REG(095),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   OSERDES_TX_DATA_12S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(12),
         SHIFTOUT2 => SHIFT2(12),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(102),
         D4 => DATA_TO_OSERDES_REG(103),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   

   OSERDES_TX_DATA_13S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(13),
         SHIFTOUT2 => SHIFT2(13),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(110),
         D4 => DATA_TO_OSERDES_REG(111),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_14S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 

      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(14),
         SHIFTOUT2 => SHIFT2(14),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(118),
         D4 => DATA_TO_OSERDES_REG(119),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   OSERDES_TX_DATA_15S : OSERDES 
      GENERIC MAP(
        DATA_RATE_OQ => "DDR", DATA_RATE_TQ => "DDR",  DATA_WIDTH => 8, 
        INIT_OQ => '0', INIT_TQ => '0', SERDES_MODE => "SLAVE", 
        SRVAL_OQ => '0', SRVAL_TQ => '0', TRISTATE_WIDTH => 1) 
      PORT MAP (
         OQ => open,
         SHIFTOUT1 => SHIFT1(15),
         SHIFTOUT2 => SHIFT2(15),
         TQ => open,
         CLK => TXCLK,
         CLKDIV => TXCLKDIV,
         D1 => '0',
         D2 => '0',
         D3 => DATA_TO_OSERDES_REG(126),
         D4 => DATA_TO_OSERDES_REG(127),
         D5 => '0',
         D6 => '0',
         OCE => '1',
         REV => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         SR => RESET,
         T1 => '0',
         T2 => '0',
         T3 => '0',
         T4 => '0',
         TCE => '0');   
   
   
   --OUTPUT BUFFERS	

   OBUFDS_TX_DATA_00 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(00),
         OB => DATA_TX_N(00),
         I => TX_DATA_PREBUF(00));   
   
   OBUFDS_TX_DATA_01 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(01),
         OB => DATA_TX_N(01),
         I => TX_DATA_PREBUF(01));   
   
   OBUFDS_TX_DATA_02 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(02),
         OB => DATA_TX_N(02),
         I => TX_DATA_PREBUF(02));   
   
   OBUFDS_TX_DATA_03 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(03),
         OB => DATA_TX_N(03),
         I => TX_DATA_PREBUF(03));   
   
   OBUFDS_TX_DATA_04 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(04),
         OB => DATA_TX_N(04),
         I => TX_DATA_PREBUF(04));   
   
   OBUFDS_TX_DATA_05 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(05),
         OB => DATA_TX_N(05),
         I => TX_DATA_PREBUF(05));   
   
   OBUFDS_TX_DATA_06 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(06),
         OB => DATA_TX_N(06),
         I => TX_DATA_PREBUF(06));   
   
   OBUFDS_TX_DATA_07 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(07),
         OB => DATA_TX_N(07),
         I => TX_DATA_PREBUF(07));   
   
   OBUFDS_TX_DATA_08 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(08),
         OB => DATA_TX_N(08),
         I => TX_DATA_PREBUF(08));   
   
   OBUFDS_TX_DATA_09 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(09),
         OB => DATA_TX_N(09),
         I => TX_DATA_PREBUF(09));   
   
   OBUFDS_TX_DATA_10 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(10),
         OB => DATA_TX_N(10),
         I => TX_DATA_PREBUF(10));   
   
   OBUFDS_TX_DATA_11 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(11),
         OB => DATA_TX_N(11),
         I => TX_DATA_PREBUF(11));   
   
   OBUFDS_TX_DATA_12 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(12),
         OB => DATA_TX_N(12),
         I => TX_DATA_PREBUF(12));   
   
   OBUFDS_TX_DATA_13 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(13),
         OB => DATA_TX_N(13),
         I => TX_DATA_PREBUF(13));   
   
   OBUFDS_TX_DATA_14 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(14),
         OB => DATA_TX_N(14),
         I => TX_DATA_PREBUF(14));   

   OBUFDS_TX_DATA_15 : OBUFDS_LVDSEXT_25 
      PORT MAP (
         O => DATA_TX_P(15),
         OB => DATA_TX_N(15),
         I => TX_DATA_PREBUF(15));   
   

END translated;
