--
--/////////////////////////////////////////////////////////////////////////////
--
--    File Name:  DDR_8TO1_16CHAN_RX.vhd
--      Version:  1.0
--         Date:  05/19/06
--        Model:  XAPP855 LVDS Receiver Module
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
-- The DDR_8TO1_16CHAN_RX module contains all logic in the XAPP855 LVDS Receiver,
-- including 16 channels of LVDS data, one channel of LVDS clock, a clock/data 
-- alignment algorithm, control circuit to share the alignment machine among
-- all 16 data channels, and tap counters that keep track of the IDELAY tap
-- setting of all data channels.
--  
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

ENTITY DDR_8TO1_16CHAN_RX IS
   PORT (
      DATA_RX_P               : IN std_logic_vector(15 DOWNTO 0);   -- SERIAL SIDE RX DATA (P)
      DATA_RX_N               : IN std_logic_vector(15 DOWNTO 0);   -- SERIAL SIDE RX DATA (N)
      CLOCK_RX_P              : IN std_logic;   -- FORWARDED CLOCK FROM TX (P)
      CLOCK_RX_N              : IN std_logic;   -- FORWARDED CLOCK FROM TX (N)
      INC_PAD                 : IN std_logic;   -- MANUAL INCREMENT TO DATA DELAY
      DEC_PAD                 : IN std_logic;   -- MANUAL DECREMENT TO DATA DELAY
      DATA_FROM_ISERDES       : OUT std_logic_vector(127 DOWNTO 0);   -- PARALLEL SIDE RX DATA
      RESET                   : IN std_logic;   -- RX DOMAIN RESET
      IDLY_RESET              : IN std_logic;   -- IDELAY TAP RESET
      IDELAYCTRL_RESET        : IN std_logic;   -- IDELAYCTRL CIRCUIT RESET
      BITSLIP_PAD             : IN std_logic;   -- MANUAL BITSLIP TO DATA
      CLK200                  : IN std_logic;   -- 200 MHZ REFERENCE CLOCK TO IDELAYCTRL				
      TAP_00                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_01                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_02                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_03                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_04                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_05                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_06                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_07                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_08                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_09                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_10                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_11                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_12                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_13                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_14                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_15                  : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT (0-63)
      TAP_CLK                 : OUT std_logic_vector(5 DOWNTO 0);   -- IDELAY TAP COUNT ON CLK CHANNEL (0-63)
      TRAINING_DONE           : OUT std_logic;   -- ALIGNMENT OF ALL CHANNELS COMPLETE
      RXCLK                   : OUT std_logic;   -- FORWARDED CLOCK FROM TX (BUFIO OUTPUT)
      RXCLKDIV                : OUT std_logic;   -- PARALLEL SIDE RX CLOCK (DIVIDED FROM RXCLK)
      IDELAY_READY            : OUT std_logic);   -- FLAG INDICATING THAT IDELAYCTRL IS LOCKED
END DDR_8TO1_16CHAN_RX;

ARCHITECTURE translated OF DDR_8TO1_16CHAN_RX IS

   COMPONENT BIT_ALIGN_MACHINE
      PORT (
         RXCLKDIV                : IN  std_logic;
         RXDATA                  : IN  std_logic_vector(7 DOWNTO 0);
         RST                     : IN  std_logic;
         USE_BITSLIP             : IN  std_logic;
         SAP                     : IN  std_logic;
         INC                     : OUT std_logic;
         ICE                     : OUT std_logic;
         BITSLIP                 : OUT std_logic;
         DATA_ALIGNED            : OUT std_logic);
   END COMPONENT;

   COMPONENT COUNT_TO_64
      PORT (
         clk                     : IN  std_logic;
         rst                     : IN  std_logic;
         count                   : IN  std_logic;
         ud                      : IN  std_logic;
         counter_value           : OUT std_logic_vector(5 DOWNTO 0));
   END COMPONENT;

   COMPONENT RESOURCE_SHARING_CONTROL
      PORT (
         CHAN_SEL                : OUT std_logic_vector(3 DOWNTO 0);
         ALL_CHANNELS_ALIGNED    : OUT std_logic;
         DATA_ALIGNED            : IN  std_logic;
         START_ALIGN             : OUT std_logic;
         CLK                     : IN  std_logic;
         RST                     : IN  std_logic);
   END COMPONENT;

  component IODELAY 
  generic(

      DELAY_SRC		: string	:= "I";
      IDELAY_TYPE	: string	:= "DEFAULT";
      IDELAY_VALUE	: integer	:= 0;
      ODELAY_VALUE	: integer	:= 0;
      REFCLK_FREQUENCY	: real		:= 200.0;
      HIGH_PERFORMANCE_MODE	: string		:= "TRUE"
      );
  port(
      DATAOUT	: out std_logic;

      C		: in  std_logic;
      CE	: in  std_logic;
      DATAIN	: in  std_logic;
      IDATAIN	: in  std_logic;
      INC	: in  std_logic;
      ODATAIN	: in  std_logic;
      RST	: in  std_logic;
      T		: in  std_logic
      );
end component;


   component ISERDES_NODELAY 
   generic(
      BITSLIP_ENABLE	: boolean	:= false;
      DATA_RATE		: string	:= "DDR";
      DATA_WIDTH	: integer	:= 4;
      INIT_Q1		: std_logic		:= '0';
      INIT_Q2		: std_logic		:= '0';
      INIT_Q3		: std_logic		:= '0';
      INIT_Q4		: std_logic		:= '0';
      INTERFACE_TYPE	: string	:= "MEMORY";
      NUM_CE		: integer	:= 2;
      SERDES_MODE	: string	:= "MASTER"
      );
  port(
      Q1		: out std_logic;
      Q2		: out std_logic;
      Q3		: out std_logic;
      Q4		: out std_logic;
      Q5		: out std_logic;
      Q6		: out std_logic;
      SHIFTOUT1		: out std_logic;
      SHIFTOUT2		: out std_logic;
      BITSLIP		: in std_logic;
      CE1		: in std_logic;
      CE2		: in std_logic;
      CLK		: in std_logic;
      CLKB		: in std_logic;
      CLKDIV		: in std_logic;
      D			: in std_logic;
      OCLK		: in std_logic;
      RST		: in std_logic;
      SHIFTIN1		: in std_logic;
      SHIFTIN2		: in std_logic
    );
   end component;


   SIGNAL CLOCK_RX_BUF             :  std_logic;   
   SIGNAL DATA_RX_BUF              :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL DATA_RX_IDLY             :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL CLOCK_RX_ISERDES_OUT     :  std_logic;   
   SIGNAL BITSLIP_FROM_MACHINE     :  std_logic;   
   SIGNAL ICE_FROM_MACHINE         :  std_logic;   
   SIGNAL INC_FROM_MACHINE         :  std_logic;   
   SIGNAL DATA_ALIGNED             :  std_logic;   
   SIGNAL SHIFT1                   :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL SHIFT2                   :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL CHAN_SEL                 :  std_logic_vector(3 DOWNTO 0);   
   SIGNAL INC_CAPTURE              :  std_logic_vector(3 DOWNTO 0);   
   SIGNAL DEC_CAPTURE              :  std_logic_vector(3 DOWNTO 0);   
   SIGNAL BITSLIP_CAPTURE          :  std_logic_vector(3 DOWNTO 0);   
   SIGNAL INC_PULSE                :  std_logic;   
   SIGNAL DEC_PULSE                :  std_logic;   
   SIGNAL BITSLIP_PULSE            :  std_logic;   
   SIGNAL RESET_SM                 :  std_logic_vector(20 DOWNTO 0);   
   SIGNAL BITSLIP_TO_ISERDES       :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL ICE_TO_ISERDES           :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL INC_TO_ISERDES           :  std_logic_vector(15 DOWNTO 0);   
   SIGNAL DATA_TO_MACHINE          :  std_logic_vector(7 DOWNTO 0);   
   SIGNAL I                        :  integer;   
   SIGNAL  TEMP_TAP_RST_00, TEMP_TAP_RST_01, TEMP_TAP_RST_02,
           TEMP_TAP_RST_03, TEMP_TAP_RST_04, TEMP_TAP_RST_05,
           TEMP_TAP_RST_06, TEMP_TAP_RST_07, TEMP_TAP_RST_08,
           TEMP_TAP_RST_09, TEMP_TAP_RST_10, TEMP_TAP_RST_11,
           TEMP_TAP_RST_12, TEMP_TAP_RST_13, TEMP_TAP_RST_14, 
           TEMP_TAP_RST_15         :  std_logic;
   SIGNAL  TEMP_TAP_CNT_00, TEMP_TAP_CNT_01, TEMP_TAP_CNT_02,
           TEMP_TAP_CNT_03, TEMP_TAP_CNT_04, TEMP_TAP_CNT_05,
           TEMP_TAP_CNT_06, TEMP_TAP_CNT_07, TEMP_TAP_CNT_08,
           TEMP_TAP_CNT_09, TEMP_TAP_CNT_10, TEMP_TAP_CNT_11,
           TEMP_TAP_CNT_12, TEMP_TAP_CNT_13, TEMP_TAP_CNT_14,
           TEMP_TAP_CNT_15         :  std_logic;
   SIGNAL  TEMP_TAP_UD_00, TEMP_TAP_UD_01, TEMP_TAP_UD_02,
           TEMP_TAP_UD_03, TEMP_TAP_UD_04, TEMP_TAP_UD_05,
           TEMP_TAP_UD_06, TEMP_TAP_UD_07, TEMP_TAP_UD_08,
           TEMP_TAP_UD_09, TEMP_TAP_UD_10, TEMP_TAP_UD_11,
           TEMP_TAP_UD_12, TEMP_TAP_UD_13, TEMP_TAP_UD_14,
           TEMP_TAP_UD_15          :  std_logic;
   SIGNAL  TEMP_CE_00, TEMP_CE_01, TEMP_CE_02, TEMP_CE_03,
           TEMP_CE_04, TEMP_CE_05, TEMP_CE_06, TEMP_CE_07,
           TEMP_CE_08, TEMP_CE_09, TEMP_CE_10, TEMP_CE_11,
           TEMP_CE_12, TEMP_CE_13, TEMP_CE_14, TEMP_CE_15 :  std_logic;
   SIGNAL  TEMP_INC_00, TEMP_INC_01, TEMP_INC_02, TEMP_INC_03,
           TEMP_INC_04, TEMP_INC_05, TEMP_INC_06, TEMP_INC_07,
           TEMP_INC_08, TEMP_INC_09, TEMP_INC_10, TEMP_INC_11,
           TEMP_INC_12, TEMP_INC_13, TEMP_INC_14, TEMP_INC_15 :  std_logic;
   SIGNAL  TEMP_RST_00, TEMP_RST_01, TEMP_RST_02, TEMP_RST_03,
           TEMP_RST_04, TEMP_RST_05, TEMP_RST_06, TEMP_RST_07,
           TEMP_RST_08, TEMP_RST_09, TEMP_RST_10, TEMP_RST_11,
           TEMP_RST_12, TEMP_RST_13, TEMP_RST_14, TEMP_RST_15 :  std_logic;
   SIGNAL  TEMP_BITSLIP00, TEMP_BITSLIP01, TEMP_BITSLIP02,
           TEMP_BITSLIP03, TEMP_BITSLIP04, TEMP_BITSLIP05,
           TEMP_BITSLIP06, TEMP_BITSLIP07, TEMP_BITSLIP08,
           TEMP_BITSLIP09, TEMP_BITSLIP10, TEMP_BITSLIP11,
           TEMP_BITSLIP12, TEMP_BITSLIP13, TEMP_BITSLIP14,
           TEMP_BITSLIP15             :  std_logic;
   SIGNAL  TEMP_BITSLIP00S, TEMP_BITSLIP01S, TEMP_BITSLIP02S,
           TEMP_BITSLIP03S, TEMP_BITSLIP04S, TEMP_BITSLIP05S,
           TEMP_BITSLIP06S, TEMP_BITSLIP07S, TEMP_BITSLIP08S,
           TEMP_BITSLIP09S, TEMP_BITSLIP10S, TEMP_BITSLIP11S,
           TEMP_BITSLIP12S, TEMP_BITSLIP13S, TEMP_BITSLIP14S,
           TEMP_BITSLIP15S             :  std_logic;
   SIGNAL TEMP_RSTx_01			:  std_logic;
   SIGNAL DATA_FROM_ISERDES_INT        :  std_logic_vector(127 DOWNTO 0);   
   SIGNAL ICE_DELAY                :  std_logic;   
   SIGNAL INC_DELAY                :  std_logic;   
   SIGNAL START_ALIGN              :  std_logic;   
   SIGNAL RXCLKDIV_INT             :  std_logic;   
   SIGNAL RXCLK_INT                :  std_logic;   
   SIGNAL RXCLK_INT_N              :  std_logic;   

BEGIN
   INC_DELAY <= INC_PULSE ;
   ICE_DELAY <= INC_PULSE OR DEC_PULSE ;
   TAP_CLK <= "000000" ;
   RXCLKDIV <= RXCLKDIV_INT;
   RXCLK    <= RXCLK_INT;
   DATA_FROM_ISERDES <= DATA_FROM_ISERDES_INT (127 DOWNTO 0);

   --IDELAYCTRL MODULE

   RX_IDELAYCTRL : IDELAYCTRL 
      PORT MAP (
         RDY => IDELAY_READY,
         REFCLK => CLK200,
         RST => IDELAYCTRL_RESET);   
   
   
   --SOURCE SYNCHRONOUS CLOCK INPUT

   SOURCE_SYNC_CLOCK_IN : IBUFDS
      GENERIC MAP(
    	   DIFF_TERM => TRUE,
    	   IOSTANDARD => "LVDS_25")

      PORT MAP (
         O => CLOCK_RX_BUF,
         I => CLOCK_RX_P,
         IB => CLOCK_RX_N);   
   
   
   --IDELAY IN CLOCK PATH

   ISERDES_CLOCK_RX : IODELAY 
      GENERIC MAP(
    	   IDELAY_TYPE => "FIXED",
    	   IDELAY_VALUE => 0,
    	   ODELAY_VALUE => 0,
    	   REFCLK_FREQUENCY => 200.00,
    	   HIGH_PERFORMANCE_MODE => "TRUE")
      PORT MAP (
         DATAOUT => CLOCK_RX_ISERDES_OUT,
         IDATAIN => CLOCK_RX_BUF,
         ODATAIN => '0',
         DATAIN => '0',
         T => '0',
         CE => '0',
         INC => '0',
         C => '0',
         RST => RESET);   
   
   
   --CLOCK BUFFER FOR SERIAL SIDE CLOCK	

   RX_CLK_BUFIO : BUFIO 
      PORT MAP (
         O => RXCLK_INT,
         I => CLOCK_RX_ISERDES_OUT);   
   
   
   --CLOCK BUFFER/DIVIDER FOR PARALLEL SIDE CLOCK

   RX_CLK_BUFR : BUFR
      GENERIC MAP( 
         BUFR_DIVIDE => "4" )
      PORT MAP (
         O => RXCLKDIV_INT,
         CE => '1',
         CLR => '0',
         I => CLOCK_RX_ISERDES_OUT);   
   

   --CHANNEL SELECT LOGIC TO SHARE ALIGNMENT MACHINE RESOURCES IN ROUND ROBIN FASHION
   
   PROCESS (RXCLKDIV_INT)
   BEGIN
      IF (RXCLKDIV_INT'EVENT AND RXCLKDIV_INT = '1') THEN
         CASE CHAN_SEL IS
            WHEN "0000" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(7 DOWNTO 0);    
                     INC_TO_ISERDES <= "000000000000000" & INC_FROM_MACHINE;    
                     ICE_TO_ISERDES <= "000000000000000" & ICE_FROM_MACHINE;    
                     BITSLIP_TO_ISERDES <= "000000000000000" & BITSLIP_FROM_MACHINE;    
            WHEN "0001" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(15 DOWNTO 8);    
                     INC_TO_ISERDES <= "00000000000000" & INC_FROM_MACHINE & '0';    
                     ICE_TO_ISERDES <= "00000000000000" & ICE_FROM_MACHINE & '0';    
                     BITSLIP_TO_ISERDES <= "00000000000000" & BITSLIP_FROM_MACHINE & '0';    
            WHEN "0010" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(23 DOWNTO 16);    
                     INC_TO_ISERDES <= "0000000000000" & INC_FROM_MACHINE & "00";    
                     ICE_TO_ISERDES <= "0000000000000" & ICE_FROM_MACHINE & "00";    
                     BITSLIP_TO_ISERDES <= "0000000000000" & BITSLIP_FROM_MACHINE & "00";    
            WHEN "0011" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(31 DOWNTO 24);    
                     INC_TO_ISERDES <= "000000000000" & INC_FROM_MACHINE & "000";    
                     ICE_TO_ISERDES <= "000000000000" & ICE_FROM_MACHINE & "000";    
                     BITSLIP_TO_ISERDES <= "000000000000" & BITSLIP_FROM_MACHINE & "000";    
            WHEN "0100" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(39 DOWNTO 32);    
                     INC_TO_ISERDES <= "00000000000" & INC_FROM_MACHINE & "0000";    
                     ICE_TO_ISERDES <= "00000000000" & ICE_FROM_MACHINE & "0000";    
                     BITSLIP_TO_ISERDES <= "00000000000" & BITSLIP_FROM_MACHINE & "0000";    
            WHEN "0101" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(47 DOWNTO 40);    
                     INC_TO_ISERDES <= "0000000000" & INC_FROM_MACHINE & "00000";    
                     ICE_TO_ISERDES <= "0000000000" & ICE_FROM_MACHINE & "00000";    
                     BITSLIP_TO_ISERDES <= "0000000000" & BITSLIP_FROM_MACHINE & "00000";    
            WHEN "0110" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(55 DOWNTO 48);    
                     INC_TO_ISERDES <= "000000000" & INC_FROM_MACHINE & "000000";    
                     ICE_TO_ISERDES <= "000000000" & ICE_FROM_MACHINE & "000000";    
                     BITSLIP_TO_ISERDES <= "000000000" & BITSLIP_FROM_MACHINE & "000000";    
            WHEN "0111" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(63 DOWNTO 56);    
                     INC_TO_ISERDES <= "00000000" & INC_FROM_MACHINE & "0000000";    
                     ICE_TO_ISERDES <= "00000000" & ICE_FROM_MACHINE & "0000000";    
                     BITSLIP_TO_ISERDES <= "00000000" & BITSLIP_FROM_MACHINE & "0000000";    
            WHEN "1000" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(71 DOWNTO 64);    
                     INC_TO_ISERDES <= "0000000" & INC_FROM_MACHINE & "00000000";    
                     ICE_TO_ISERDES <= "0000000" & ICE_FROM_MACHINE & "00000000";    
                     BITSLIP_TO_ISERDES <= "0000000" & BITSLIP_FROM_MACHINE & "00000000";    
            WHEN "1001" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(79 DOWNTO 72);    
                     INC_TO_ISERDES <= "000000" & INC_FROM_MACHINE & "000000000";    
                     ICE_TO_ISERDES <= "000000" & ICE_FROM_MACHINE & "000000000";    
                     BITSLIP_TO_ISERDES <= "000000" & BITSLIP_FROM_MACHINE & "000000000";    
            WHEN "1010" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(87 DOWNTO 80);    
                     INC_TO_ISERDES <= "00000" & INC_FROM_MACHINE & "0000000000";    
                     ICE_TO_ISERDES <= "00000" & ICE_FROM_MACHINE & "0000000000";    
                     BITSLIP_TO_ISERDES <= "00000" & BITSLIP_FROM_MACHINE & "0000000000";    
            WHEN "1011" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(95 DOWNTO 88);    
                     INC_TO_ISERDES <= "0000" & INC_FROM_MACHINE & "00000000000";    
                     ICE_TO_ISERDES <= "0000" & ICE_FROM_MACHINE & "00000000000";    
                     BITSLIP_TO_ISERDES <= "0000" & BITSLIP_FROM_MACHINE & "00000000000";    
            WHEN "1100" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(103 DOWNTO 96);    
                     INC_TO_ISERDES <= "000" & INC_FROM_MACHINE & "000000000000";    
                     ICE_TO_ISERDES <= "000" & ICE_FROM_MACHINE & "000000000000";    
                     BITSLIP_TO_ISERDES <= "000" & BITSLIP_FROM_MACHINE & "000000000000";    
            WHEN "1101" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(111 
DOWNTO 104);    
                     INC_TO_ISERDES <= "00" & INC_FROM_MACHINE & "0000000000000";    
                     ICE_TO_ISERDES <= "00" & ICE_FROM_MACHINE & "0000000000000";    
                     BITSLIP_TO_ISERDES <= "00" & BITSLIP_FROM_MACHINE & "0000000000000";    
            WHEN "1110" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(119 DOWNTO 112);    
                     INC_TO_ISERDES <= '0' & INC_FROM_MACHINE & "00000000000000";    
                     ICE_TO_ISERDES <= '0' & ICE_FROM_MACHINE & "00000000000000";    
                     BITSLIP_TO_ISERDES <= '0' & BITSLIP_FROM_MACHINE & "00000000000000";    
            WHEN "1111" =>
                     DATA_TO_MACHINE <= DATA_FROM_ISERDES_INT(127 DOWNTO 120);    
                     INC_TO_ISERDES <= INC_FROM_MACHINE & "000000000000000";    
                     ICE_TO_ISERDES <= ICE_FROM_MACHINE & "000000000000000";    
                     BITSLIP_TO_ISERDES <= BITSLIP_FROM_MACHINE & "000000000000000";    
            WHEN OTHERS =>
                     NULL;
            
         END CASE;
      END IF;
   END PROCESS;
   
   --MACHINE THAT ALLOCATES BIT_ALIGN_MACHINE TO EACH OF THE 16 DATA CHANNELS, ONE AT A TIME	
   RESOURCE_SHARING_CONTROL_0 : RESOURCE_SHARING_CONTROL 
      PORT MAP (
         CHAN_SEL => CHAN_SEL,
         ALL_CHANNELS_ALIGNED => TRAINING_DONE,
         DATA_ALIGNED => DATA_ALIGNED,
         START_ALIGN => START_ALIGN,
         CLK => RXCLKDIV_INT,
         RST => RESET);   
   
   BIT_ALIGN_MACHINE_0 : BIT_ALIGN_MACHINE 
      PORT MAP (
         RXCLKDIV => RXCLKDIV_INT,
         RXDATA => DATA_TO_MACHINE,
         RST => TEMP_RSTx_01,
         USE_BITSLIP => '1',
         SAP => START_ALIGN,
         INC => INC_FROM_MACHINE,
         ICE => ICE_FROM_MACHINE,
         BITSLIP => BITSLIP_FROM_MACHINE,
         DATA_ALIGNED => DATA_ALIGNED);   
   
   TEMP_RSTx_01 <= RESET OR RESET_SM(15);

   --SHORTEN EACH EXTERNAL INC AND DEC PULSE TO ONE RXCLKDIV CYCLE
   
   PROCESS (RXCLKDIV_INT)
   BEGIN
      IF (RXCLKDIV_INT'EVENT AND RXCLKDIV_INT = '1') THEN
         INC_CAPTURE(0) <= INC_PAD;    -- ASYNCHRONOUS ENTRY POINT
         DEC_CAPTURE(0) <= DEC_PAD;    
         BITSLIP_CAPTURE(0) <= BITSLIP_PAD;    
         FOR I IN 0 TO 3 - 1 LOOP
            INC_CAPTURE(I + 1) <= INC_CAPTURE(I);    -- METASTABLE FLIP-FLOPS
            DEC_CAPTURE(I + 1) <= DEC_CAPTURE(I);    
            BITSLIP_CAPTURE(I + 1) <= BITSLIP_CAPTURE(I);    
         END LOOP;
         INC_PULSE <= INC_CAPTURE(2) AND NOT INC_CAPTURE(3);    -- STABLE, SINGLE PULSE
         DEC_PULSE <= DEC_CAPTURE(2) AND NOT DEC_CAPTURE(3);    
         BITSLIP_PULSE <= BITSLIP_CAPTURE(2) AND NOT BITSLIP_CAPTURE(3); 
      END IF;
   END PROCESS;

--//KEEP TRACK OF CURRENT TAP SETTING OF IDELAY IN DATA PATH OF CHANNELS 0-15

   TEMP_TAP_RST_00 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_00 <= ICE_DELAY OR ICE_TO_ISERDES(00);
   TEMP_TAP_UD_00 <= INC_DELAY OR INC_TO_ISERDES(00);
   TAP_COUNTER_00 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_00,
         count => TEMP_TAP_CNT_00,
         ud => TEMP_TAP_UD_00,
         counter_value => TAP_00);   
   
   TEMP_TAP_RST_01 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_01 <= ICE_DELAY OR ICE_TO_ISERDES(01);
   TEMP_TAP_UD_01 <= INC_DELAY OR INC_TO_ISERDES(01);
   TAP_COUNTER_01 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_01,
         count => TEMP_TAP_CNT_01,
         ud => TEMP_TAP_UD_01,
         counter_value => TAP_01);   
   
   TEMP_TAP_RST_02 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_02 <= ICE_DELAY OR ICE_TO_ISERDES(02);
   TEMP_TAP_UD_02 <= INC_DELAY OR INC_TO_ISERDES(02);
   TAP_COUNTER_02 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_02,
         count => TEMP_TAP_CNT_02,
         ud => TEMP_TAP_UD_02,
         counter_value => TAP_02);   
   
   TEMP_TAP_RST_03 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_03 <= ICE_DELAY OR ICE_TO_ISERDES(03);
   TEMP_TAP_UD_03 <= INC_DELAY OR INC_TO_ISERDES(03);
   TAP_COUNTER_03 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_03,
         count => TEMP_TAP_CNT_03,
         ud => TEMP_TAP_UD_03,
         counter_value => TAP_03);   
   
   TEMP_TAP_RST_04 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_04 <= ICE_DELAY OR ICE_TO_ISERDES(04);
   TEMP_TAP_UD_04 <= INC_DELAY OR INC_TO_ISERDES(04);
   TAP_COUNTER_04 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_04,
         count => TEMP_TAP_CNT_04,
         ud => TEMP_TAP_UD_04,
         counter_value => TAP_04);   
   
   TEMP_TAP_RST_05 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_05 <= ICE_DELAY OR ICE_TO_ISERDES(05);
   TEMP_TAP_UD_05 <= INC_DELAY OR INC_TO_ISERDES(05);
   TAP_COUNTER_05 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_05,
         count => TEMP_TAP_CNT_05,
         ud => TEMP_TAP_UD_05,
         counter_value => TAP_05);   
   
   TEMP_TAP_RST_06 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_06 <= ICE_DELAY OR ICE_TO_ISERDES(06);
   TEMP_TAP_UD_06 <= INC_DELAY OR INC_TO_ISERDES(06);
   TAP_COUNTER_06 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_06,
         count => TEMP_TAP_CNT_06,
         ud => TEMP_TAP_UD_06,
         counter_value => TAP_06);   
   
   TEMP_TAP_RST_07 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_07 <= ICE_DELAY OR ICE_TO_ISERDES(07);
   TEMP_TAP_UD_07 <= INC_DELAY OR INC_TO_ISERDES(07);
   TAP_COUNTER_07 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_07,
         count => TEMP_TAP_CNT_07,
         ud => TEMP_TAP_UD_07,
         counter_value => TAP_07);   
   
   TEMP_TAP_RST_08 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_08 <= ICE_DELAY OR ICE_TO_ISERDES(08);
   TEMP_TAP_UD_08 <= INC_DELAY OR INC_TO_ISERDES(08);
   TAP_COUNTER_08 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_08,
         count => TEMP_TAP_CNT_08,
         ud => TEMP_TAP_UD_08,
         counter_value => TAP_08);   
   
   TEMP_TAP_RST_09 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_09 <= ICE_DELAY OR ICE_TO_ISERDES(09);
   TEMP_TAP_UD_09 <= INC_DELAY OR INC_TO_ISERDES(09);
   TAP_COUNTER_09 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_09,
         count => TEMP_TAP_CNT_09,
         ud => TEMP_TAP_UD_09,
         counter_value => TAP_09);   
   
   TEMP_TAP_RST_10 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_10 <= ICE_DELAY OR ICE_TO_ISERDES(10);
   TEMP_TAP_UD_10 <= INC_DELAY OR INC_TO_ISERDES(10);
   TAP_COUNTER_10 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_10,
         count => TEMP_TAP_CNT_10,
         ud => TEMP_TAP_UD_10,
         counter_value => TAP_10);   
   
   TEMP_TAP_RST_11 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_11 <= ICE_DELAY OR ICE_TO_ISERDES(11);
   TEMP_TAP_UD_11 <= INC_DELAY OR INC_TO_ISERDES(11);
   TAP_COUNTER_11 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_11,
         count => TEMP_TAP_CNT_11,
         ud => TEMP_TAP_UD_11,
         counter_value => TAP_11);   
   
   TEMP_TAP_RST_12 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_12 <= ICE_DELAY OR ICE_TO_ISERDES(12);
   TEMP_TAP_UD_12 <= INC_DELAY OR INC_TO_ISERDES(12);
   TAP_COUNTER_12 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_12,
         count => TEMP_TAP_CNT_12,
         ud => TEMP_TAP_UD_12,
         counter_value => TAP_12);   
   
   TEMP_TAP_RST_13 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_13 <= ICE_DELAY OR ICE_TO_ISERDES(13);
   TEMP_TAP_UD_13 <= INC_DELAY OR INC_TO_ISERDES(13);
   TAP_COUNTER_13 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_13,
         count => TEMP_TAP_CNT_13,
         ud => TEMP_TAP_UD_13,
         counter_value => TAP_13);   
   
   TEMP_TAP_RST_14 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_14 <= ICE_DELAY OR ICE_TO_ISERDES(14);
   TEMP_TAP_UD_14 <= INC_DELAY OR INC_TO_ISERDES(14);
   TAP_COUNTER_14 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_14,
         count => TEMP_TAP_CNT_14,
         ud => TEMP_TAP_UD_14,
         counter_value => TAP_14);   
   
   TEMP_TAP_RST_15 <= IDLY_RESET OR RESET;
   TEMP_TAP_CNT_15 <= ICE_DELAY OR ICE_TO_ISERDES(15);
   TEMP_TAP_UD_15 <= INC_DELAY OR INC_TO_ISERDES(15);
   TAP_COUNTER_15 : COUNT_TO_64 
      PORT MAP (
         clk => RXCLKDIV_INT,
         rst => TEMP_TAP_RST_15,
         count => TEMP_TAP_CNT_15,
         ud => TEMP_TAP_UD_15,
         counter_value => TAP_15);   
   
--//CIRCUIT TO PRODUCE RESET DELAYED BY 20 CYCLES FOR BIT_ALIGN_MACHINE

   PROCESS (RXCLKDIV_INT)
   BEGIN
      IF (RXCLKDIV_INT'EVENT AND RXCLKDIV_INT = '1') THEN
         RESET_SM(0) <= RESET;    
         FOR K IN 0 TO 20 - 1 LOOP
            RESET_SM(K + 1) <= RESET_SM(K);    
         END LOOP;
      END IF;
   END PROCESS;
   
   --DATA INPUT BUFFERS

   RX_DATA_IN_00 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 
      PORT MAP (
         O => DATA_RX_BUF(00),
         I => DATA_RX_P(00),
         IB => DATA_RX_N(00));   
   
   RX_DATA_IN_01 : IBUFDS 
      GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 
      PORT MAP (
         O => DATA_RX_BUF(01),
         I => DATA_RX_P(01),
         IB => DATA_RX_N(01));   
   
   RX_DATA_IN_02 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 


      PORT MAP (
         O => DATA_RX_BUF(02),
         I => DATA_RX_P(02),
         IB => DATA_RX_N(02));   
   
   RX_DATA_IN_03 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 


      PORT MAP (
         O => DATA_RX_BUF(03),
         I => DATA_RX_P(03),
         IB => DATA_RX_N(03));   
   
   RX_DATA_IN_04 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 


      PORT MAP (
         O => DATA_RX_BUF(04),
         I => DATA_RX_P(04),
         IB => DATA_RX_N(04));   
   
   RX_DATA_IN_05 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 


      PORT MAP (
         O => DATA_RX_BUF(05),
         I => DATA_RX_P(05),
         IB => DATA_RX_N(05));   
   
   RX_DATA_IN_06 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 


      PORT MAP (
         O => DATA_RX_BUF(06),
         I => DATA_RX_P(06),
         IB => DATA_RX_N(06));   
   
   RX_DATA_IN_07 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(07),
         I => DATA_RX_P(07),
         IB => DATA_RX_N(07));   
   
   RX_DATA_IN_08 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(08),
         I => DATA_RX_P(08),
         IB => DATA_RX_N(08));   
   

   RX_DATA_IN_09 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(09),
         I => DATA_RX_P(09),
         IB => DATA_RX_N(09));   
   
   RX_DATA_IN_10 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(10),
         I => DATA_RX_P(10),
         IB => DATA_RX_N(10));   
   
   RX_DATA_IN_11 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(11),
         I => DATA_RX_P(11),
         IB => DATA_RX_N(11));   
   
   RX_DATA_IN_12 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(12),
         I => DATA_RX_P(12),
         IB => DATA_RX_N(12));   
   
   RX_DATA_IN_13 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(13),
         I => DATA_RX_P(13),
         IB => DATA_RX_N(13));   
     
   RX_DATA_IN_14 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 

      PORT MAP (
         O => DATA_RX_BUF(14),
         I => DATA_RX_P(14),
         IB => DATA_RX_N(14));   
      
   RX_DATA_IN_15 : IBUFDS 
   GENERIC MAP(
         DIFF_TERM => TRUE, IOSTANDARD =>"LVDS_25") 
      PORT MAP (
         O => DATA_RX_BUF(15),
         I => DATA_RX_P(15),
         IB => DATA_RX_N(15));   
   
   TEMP_CE_00 <= ICE_DELAY OR ICE_TO_ISERDES(00);
   TEMP_INC_00 <= INC_DELAY OR INC_TO_ISERDES(00);
   TEMP_RST_00 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_00 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(00),
         IDATAIN => DATA_RX_BUF(00),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_00,
         INC => TEMP_INC_00,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_00);   
   
   TEMP_CE_01 <= ICE_DELAY OR ICE_TO_ISERDES(01);
   TEMP_INC_01 <= INC_DELAY OR INC_TO_ISERDES(01);
   TEMP_RST_01 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_01 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(01),
         IDATAIN => DATA_RX_BUF(01),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_01,
         INC => TEMP_INC_01,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_01);   
   
   TEMP_CE_02 <= ICE_DELAY OR ICE_TO_ISERDES(02);
   TEMP_INC_02 <= INC_DELAY OR INC_TO_ISERDES(02);
   TEMP_RST_02 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_02 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(02),
         IDATAIN => DATA_RX_BUF(02),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_02,
         INC => TEMP_INC_02,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_02);   
   
   TEMP_CE_03 <= ICE_DELAY OR ICE_TO_ISERDES(03);
   TEMP_INC_03 <= INC_DELAY OR INC_TO_ISERDES(03);
   TEMP_RST_03 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_03 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(03),
         IDATAIN => DATA_RX_BUF(03),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_03,
         INC => TEMP_INC_03,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_03);   
   
   TEMP_CE_04 <= ICE_DELAY OR ICE_TO_ISERDES(04);
   TEMP_INC_04 <= INC_DELAY OR INC_TO_ISERDES(04);
   TEMP_RST_04 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_04 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(04),
         IDATAIN => DATA_RX_BUF(04),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_04,
         INC => TEMP_INC_04,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_04);   
   
   TEMP_CE_05 <= ICE_DELAY OR ICE_TO_ISERDES(05);
   TEMP_INC_05 <= INC_DELAY OR INC_TO_ISERDES(05);
   TEMP_RST_05 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_05 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(05),
         IDATAIN => DATA_RX_BUF(05),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_05,
         INC => TEMP_INC_05,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_05);   
   
   TEMP_CE_06 <= ICE_DELAY OR ICE_TO_ISERDES(06);
   TEMP_INC_06 <= INC_DELAY OR INC_TO_ISERDES(06);
   TEMP_RST_06 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_06 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(06),
         IDATAIN => DATA_RX_BUF(06),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_06,
         INC => TEMP_INC_06,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_06);   
   
   TEMP_CE_07 <= ICE_DELAY OR ICE_TO_ISERDES(07);
   TEMP_INC_07 <= INC_DELAY OR INC_TO_ISERDES(07);
   TEMP_RST_07 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_07 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(07),
         IDATAIN => DATA_RX_BUF(07),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_07,
         INC => TEMP_INC_07,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_07);   
   
   TEMP_CE_08 <= ICE_DELAY OR ICE_TO_ISERDES(08);
   TEMP_INC_08 <= INC_DELAY OR INC_TO_ISERDES(08);
   TEMP_RST_08 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_08 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(08),
         IDATAIN => DATA_RX_BUF(08),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_08,
         INC => TEMP_INC_08,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_08);   
   
   TEMP_CE_09 <= ICE_DELAY OR ICE_TO_ISERDES(09);
   TEMP_INC_09 <= INC_DELAY OR INC_TO_ISERDES(09);
   TEMP_RST_09 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_09 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(09),
         IDATAIN => DATA_RX_BUF(09),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_09,
         INC => TEMP_INC_09,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_09);   
   
   TEMP_CE_10 <= ICE_DELAY OR ICE_TO_ISERDES(10);
   TEMP_INC_10 <= INC_DELAY OR INC_TO_ISERDES(10);
   TEMP_RST_10 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_10 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(10),
         IDATAIN => DATA_RX_BUF(10),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_10,
         INC => TEMP_INC_10,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_10);   
   
   TEMP_CE_11 <= ICE_DELAY OR ICE_TO_ISERDES(11);
   TEMP_INC_11 <= INC_DELAY OR INC_TO_ISERDES(11);
   TEMP_RST_11 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_11 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(11),
         IDATAIN => DATA_RX_BUF(11),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_11,
         INC => TEMP_INC_11,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_11);   
   
   TEMP_CE_12 <= ICE_DELAY OR ICE_TO_ISERDES(12);
   TEMP_INC_12 <= INC_DELAY OR INC_TO_ISERDES(12);
   TEMP_RST_12 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_12 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(12),
         IDATAIN => DATA_RX_BUF(12),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_12,
         INC => TEMP_INC_12,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_12);   
   
   TEMP_CE_13 <= ICE_DELAY OR ICE_TO_ISERDES(13);
   TEMP_INC_13 <= INC_DELAY OR INC_TO_ISERDES(13);
   TEMP_RST_13 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_13 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(13),
         IDATAIN => DATA_RX_BUF(13),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_13,
         INC => TEMP_INC_13,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_13);   
   
   TEMP_CE_14 <= ICE_DELAY OR ICE_TO_ISERDES(14);
   TEMP_INC_14 <= INC_DELAY OR INC_TO_ISERDES(14);
   TEMP_RST_14 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_14 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 

      PORT MAP (
         DATAOUT => DATA_RX_IDLY(14),
         IDATAIN => DATA_RX_BUF(14),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_14,
         INC => TEMP_INC_14,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_14);   
   
   TEMP_CE_15 <= ICE_DELAY OR ICE_TO_ISERDES(15);
   TEMP_INC_15 <= INC_DELAY OR INC_TO_ISERDES(15);
   TEMP_RST_15 <= IDLY_RESET OR RESET;

   IODELAY_RX_DATA_15 : IODELAY 
GENERIC MAP(
         IDELAY_TYPE => "VARIABLE", IDELAY_VALUE => 0, 
         ODELAY_VALUE => 0, REFCLK_FREQUENCY => 200.00,
         HIGH_PERFORMANCE_MODE => "TRUE") 
      PORT MAP (
         DATAOUT => DATA_RX_IDLY(15),
         IDATAIN => DATA_RX_BUF(15),
         ODATAIN => '0',
         DATAIN => '0',
         T => '1',
         CE => TEMP_CE_15,
         INC => TEMP_INC_15,
         C => RXCLKDIV_INT,
         RST => TEMP_RST_15);   
   
   TEMP_BITSLIP00 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(00);
   
   RXCLK_INT_N <= not RXCLK_INT;

   ISERDES_RX_DATA_00 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")

      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(007),
         Q2 => DATA_FROM_ISERDES_INT(006),
         Q3 => DATA_FROM_ISERDES_INT(005),
         Q4 => DATA_FROM_ISERDES_INT(004),
         Q5 => DATA_FROM_ISERDES_INT(003),
         Q6 => DATA_FROM_ISERDES_INT(002),
         SHIFTOUT1 => SHIFT1(00),
         SHIFTOUT2 => SHIFT2(00),
         BITSLIP => TEMP_BITSLIP00,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(00),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP01 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(01);

   ISERDES_RX_DATA_01 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(015),
         Q2 => DATA_FROM_ISERDES_INT(014),
         Q3 => DATA_FROM_ISERDES_INT(013),
         Q4 => DATA_FROM_ISERDES_INT(012),
         Q5 => DATA_FROM_ISERDES_INT(011),
         Q6 => DATA_FROM_ISERDES_INT(010),
         SHIFTOUT1 => SHIFT1(01),
         SHIFTOUT2 => SHIFT2(01),
         BITSLIP => TEMP_BITSLIP01,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(01),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP02 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(02);

   ISERDES_RX_DATA_02 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(023),
         Q2 => DATA_FROM_ISERDES_INT(022),
         Q3 => DATA_FROM_ISERDES_INT(021),
         Q4 => DATA_FROM_ISERDES_INT(020),
         Q5 => DATA_FROM_ISERDES_INT(019),
         Q6 => DATA_FROM_ISERDES_INT(018),
         SHIFTOUT1 => SHIFT1(02),
         SHIFTOUT2 => SHIFT2(02),
         BITSLIP => TEMP_BITSLIP02,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(02),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP03 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(03);

   ISERDES_RX_DATA_03 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(031),
         Q2 => DATA_FROM_ISERDES_INT(030),
         Q3 => DATA_FROM_ISERDES_INT(029),
         Q4 => DATA_FROM_ISERDES_INT(028),
         Q5 => DATA_FROM_ISERDES_INT(027),
         Q6 => DATA_FROM_ISERDES_INT(026),
         SHIFTOUT1 => SHIFT1(03),
         SHIFTOUT2 => SHIFT2(03),
         BITSLIP => TEMP_BITSLIP03,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(03),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP04 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(04);

   ISERDES_RX_DATA_04 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(039),
         Q2 => DATA_FROM_ISERDES_INT(038),
         Q3 => DATA_FROM_ISERDES_INT(037),
         Q4 => DATA_FROM_ISERDES_INT(036),
         Q5 => DATA_FROM_ISERDES_INT(035),
         Q6 => DATA_FROM_ISERDES_INT(034),
         SHIFTOUT1 => SHIFT1(04),
         SHIFTOUT2 => SHIFT2(04),
         BITSLIP => TEMP_BITSLIP04,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(04),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP05 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(05);

   ISERDES_RX_DATA_05 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(047),
         Q2 => DATA_FROM_ISERDES_INT(046),
         Q3 => DATA_FROM_ISERDES_INT(045),
         Q4 => DATA_FROM_ISERDES_INT(044),
         Q5 => DATA_FROM_ISERDES_INT(043),
         Q6 => DATA_FROM_ISERDES_INT(042),
         SHIFTOUT1 => SHIFT1(05),
         SHIFTOUT2 => SHIFT2(05),
         BITSLIP => TEMP_BITSLIP05,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(05),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP06 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(06);

   ISERDES_RX_DATA_06 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(055),
         Q2 => DATA_FROM_ISERDES_INT(054),
         Q3 => DATA_FROM_ISERDES_INT(053),
         Q4 => DATA_FROM_ISERDES_INT(052),
         Q5 => DATA_FROM_ISERDES_INT(051),
         Q6 => DATA_FROM_ISERDES_INT(050),
         SHIFTOUT1 => SHIFT1(06),
         SHIFTOUT2 => SHIFT2(06),
         BITSLIP => TEMP_BITSLIP06,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(06),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);
   
   TEMP_BITSLIP07 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(07);

   ISERDES_RX_DATA_07 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(063),
         Q2 => DATA_FROM_ISERDES_INT(062),
         Q3 => DATA_FROM_ISERDES_INT(061),
         Q4 => DATA_FROM_ISERDES_INT(060),
         Q5 => DATA_FROM_ISERDES_INT(059),
         Q6 => DATA_FROM_ISERDES_INT(058),
         SHIFTOUT1 => SHIFT1(07),
         SHIFTOUT2 => SHIFT2(07),
         BITSLIP => TEMP_BITSLIP07,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(07),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP08 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(08);

   ISERDES_RX_DATA_08 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(071),
         Q2 => DATA_FROM_ISERDES_INT(070),
         Q3 => DATA_FROM_ISERDES_INT(069),
         Q4 => DATA_FROM_ISERDES_INT(068),
         Q5 => DATA_FROM_ISERDES_INT(067),
         Q6 => DATA_FROM_ISERDES_INT(066),
         SHIFTOUT1 => SHIFT1(08),
         SHIFTOUT2 => SHIFT2(08),
         BITSLIP => TEMP_BITSLIP08,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(08),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP09 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(09);

   ISERDES_RX_DATA_09 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(079),
         Q2 => DATA_FROM_ISERDES_INT(078),
         Q3 => DATA_FROM_ISERDES_INT(077),
         Q4 => DATA_FROM_ISERDES_INT(076),
         Q5 => DATA_FROM_ISERDES_INT(075),
         Q6 => DATA_FROM_ISERDES_INT(074),
         SHIFTOUT1 => SHIFT1(09),
         SHIFTOUT2 => SHIFT2(09),
         BITSLIP => TEMP_BITSLIP09,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(09),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP10 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(10);

   ISERDES_RX_DATA_10 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(087),
         Q2 => DATA_FROM_ISERDES_INT(086),
         Q3 => DATA_FROM_ISERDES_INT(085),
         Q4 => DATA_FROM_ISERDES_INT(084),
         Q5 => DATA_FROM_ISERDES_INT(083),
         Q6 => DATA_FROM_ISERDES_INT(082),
         SHIFTOUT1 => SHIFT1(10),
         SHIFTOUT2 => SHIFT2(10),
         BITSLIP => TEMP_BITSLIP10,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(10),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP11 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(11);

   ISERDES_RX_DATA_11 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(095),
         Q2 => DATA_FROM_ISERDES_INT(094),
         Q3 => DATA_FROM_ISERDES_INT(093),
         Q4 => DATA_FROM_ISERDES_INT(092),
         Q5 => DATA_FROM_ISERDES_INT(091),
         Q6 => DATA_FROM_ISERDES_INT(090),
         SHIFTOUT1 => SHIFT1(11),
         SHIFTOUT2 => SHIFT2(11),
         BITSLIP => TEMP_BITSLIP11,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(11),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP12 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(12);

   ISERDES_RX_DATA_12 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(103),
         Q2 => DATA_FROM_ISERDES_INT(102),
         Q3 => DATA_FROM_ISERDES_INT(101),
         Q4 => DATA_FROM_ISERDES_INT(100),
         Q5 => DATA_FROM_ISERDES_INT(099),
         Q6 => DATA_FROM_ISERDES_INT(098),
         SHIFTOUT1 => SHIFT1(12),
         SHIFTOUT2 => SHIFT2(12),
         BITSLIP => TEMP_BITSLIP12,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(12),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP13 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(13);

   ISERDES_RX_DATA_13 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(111),
         Q2 => DATA_FROM_ISERDES_INT(110),
         Q3 => DATA_FROM_ISERDES_INT(109),
         Q4 => DATA_FROM_ISERDES_INT(108),
         Q5 => DATA_FROM_ISERDES_INT(107),
         Q6 => DATA_FROM_ISERDES_INT(106),
         SHIFTOUT1 => SHIFT1(13),
         SHIFTOUT2 => SHIFT2(13),
         BITSLIP => TEMP_BITSLIP13,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(13),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP14 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(14);

   ISERDES_RX_DATA_14 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(119),
         Q2 => DATA_FROM_ISERDES_INT(118),
         Q3 => DATA_FROM_ISERDES_INT(117),
         Q4 => DATA_FROM_ISERDES_INT(116),
         Q5 => DATA_FROM_ISERDES_INT(115),
         Q6 => DATA_FROM_ISERDES_INT(114),
         SHIFTOUT1 => SHIFT1(14),
         SHIFTOUT2 => SHIFT2(14),
         BITSLIP => TEMP_BITSLIP14,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(14),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);   
   
   TEMP_BITSLIP15 <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(15);

   ISERDES_RX_DATA_15 : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"MASTER")


      PORT MAP (
         Q1 => DATA_FROM_ISERDES_INT(127),
         Q2 => DATA_FROM_ISERDES_INT(126),
         Q3 => DATA_FROM_ISERDES_INT(125),
         Q4 => DATA_FROM_ISERDES_INT(124),
         Q5 => DATA_FROM_ISERDES_INT(123),
         Q6 => DATA_FROM_ISERDES_INT(122),
         SHIFTOUT1 => SHIFT1(15),
         SHIFTOUT2 => SHIFT2(15),
         BITSLIP => TEMP_BITSLIP15,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => DATA_RX_IDLY(15),
         OCLK => '0',
         SHIFTIN1 => '0',
         SHIFTIN2 => '0',
         RST => RESET);
   

-- //SLAVE ISERDES IN DATA PATH

   TEMP_BITSLIP00S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(00);

   ISERDES_RX_DATA_00S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")
      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(001),
         Q4 => DATA_FROM_ISERDES_INT(000),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP00S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(00),
         SHIFTIN2 => SHIFT2(00),
         RST => RESET);   
   
   TEMP_BITSLIP01S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(01);

   ISERDES_RX_DATA_01S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(009),
         Q4 => DATA_FROM_ISERDES_INT(008),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP01S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(01),
         SHIFTIN2 => SHIFT2(01),
         RST => RESET);   
   
   TEMP_BITSLIP02S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(02);

   ISERDES_RX_DATA_02S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(017),
         Q4 => DATA_FROM_ISERDES_INT(016),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP02S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(02),
         SHIFTIN2 => SHIFT2(02),
         RST => RESET);   
   
   TEMP_BITSLIP03S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(03);

   ISERDES_RX_DATA_03S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(025),
         Q4 => DATA_FROM_ISERDES_INT(024),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP03S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(03),
         SHIFTIN2 => SHIFT2(03),
         RST => RESET);   
   
   TEMP_BITSLIP04S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(04);

   ISERDES_RX_DATA_04S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(033),
         Q4 => DATA_FROM_ISERDES_INT(032),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP04S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(04),
         SHIFTIN2 => SHIFT2(04),
         RST => RESET);   
   
   TEMP_BITSLIP05S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(05);

   ISERDES_RX_DATA_05S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(041),
         Q4 => DATA_FROM_ISERDES_INT(040),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP05S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(05),
         SHIFTIN2 => SHIFT2(05),
         RST => RESET);   
   
   TEMP_BITSLIP06S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(06);

   ISERDES_RX_DATA_06S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(049),
         Q4 => DATA_FROM_ISERDES_INT(048),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP06S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(06),
         SHIFTIN2 => SHIFT2(06),
         RST => RESET);   
   
   TEMP_BITSLIP07S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(07);

   ISERDES_RX_DATA_07S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(057),
         Q4 => DATA_FROM_ISERDES_INT(056),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP07S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(07),
         SHIFTIN2 => SHIFT2(07),
         RST => RESET);   
   
   TEMP_BITSLIP08S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(08);

   ISERDES_RX_DATA_08S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(065),
         Q4 => DATA_FROM_ISERDES_INT(064),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP08S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(08),
         SHIFTIN2 => SHIFT2(08),
         RST => RESET);   
   
   TEMP_BITSLIP09S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(09);

   ISERDES_RX_DATA_09S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(073),
         Q4 => DATA_FROM_ISERDES_INT(072),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP09S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(09),
         SHIFTIN2 => SHIFT2(09),
         RST => RESET);   
   
   TEMP_BITSLIP10S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(10);

   ISERDES_RX_DATA_10S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(081),
         Q4 => DATA_FROM_ISERDES_INT(080),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP10S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(10),
         SHIFTIN2 => SHIFT2(10),
         RST => RESET);   
   
   TEMP_BITSLIP11S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(11);

   ISERDES_RX_DATA_11S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(089),
         Q4 => DATA_FROM_ISERDES_INT(088),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP11S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(11),
         SHIFTIN2 => SHIFT2(11),
         RST => RESET);   
   
   TEMP_BITSLIP12S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(12);

   ISERDES_RX_DATA_12S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(097),
         Q4 => DATA_FROM_ISERDES_INT(096),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP12S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(12),
         SHIFTIN2 => SHIFT2(12),
         RST => RESET);   
   
   TEMP_BITSLIP13S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(13);

   ISERDES_RX_DATA_13S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(105),
         Q4 => DATA_FROM_ISERDES_INT(104),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP13S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(13),
         SHIFTIN2 => SHIFT2(13),
         RST => RESET);   
   
   TEMP_BITSLIP14S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(14);

   ISERDES_RX_DATA_14S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(113),
         Q4 => DATA_FROM_ISERDES_INT(112),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP14S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(14),
         SHIFTIN2 => SHIFT2(14),
         RST => RESET);   
   
   TEMP_BITSLIP15S <= BITSLIP_PULSE OR BITSLIP_TO_ISERDES(15);

   ISERDES_RX_DATA_15S : ISERDES_NODELAY 
   GENERIC MAP(
         BITSLIP_ENABLE => TRUE, DATA_RATE => "DDR", DATA_WIDTH => 8, 
         INTERFACE_TYPE => "NETWORKING", NUM_CE => 1, SERDES_MODE =>"SLAVE")

      PORT MAP (
         Q1 => open,
         Q2 => open,
         Q3 => DATA_FROM_ISERDES_INT(121),
         Q4 => DATA_FROM_ISERDES_INT(120),
         Q5 => open,
         Q6 => open,
         SHIFTOUT1 => open,
         SHIFTOUT2 => open,
         BITSLIP => TEMP_BITSLIP15S,
         CE1 => '1',
         CE2 => '0',
         CLK => RXCLK_INT,
         CLKB => RXCLK_INT_N,
         CLKDIV => RXCLKDIV_INT,
         D => '0',
         OCLK => '0',
         SHIFTIN1 => SHIFT1(15),
         SHIFTIN2 => SHIFT2(15),
         RST => RESET);   
   

END translated;
