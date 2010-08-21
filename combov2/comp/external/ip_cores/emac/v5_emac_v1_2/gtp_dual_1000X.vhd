-------------------------------------------------------------------------------
-- Title      : 1000BASE-X RocketIO wrapper
-- Project    : Virtex-5 Ethernet MAC Wrappers
-------------------------------------------------------------------------------
-- File       : gtp_dual_1000X.vhd
-- Author     : Xilinx
-------------------------------------------------------------------------------
-- Copyright (c) 2004-2007 by Xilinx, Inc. All rights reserved.
-- This text/file contains proprietary, confidential
-- information of Xilinx, Inc., is distributed under license
-- from Xilinx, Inc., and may be used, copied and/or
-- disclosed only pursuant to the terms of a valid license
-- agreement with Xilinx, Inc. Xilinx hereby grants you
-- a license to use this text/file solely for design, simulation,
-- implementation and creation of design files limited
-- to Xilinx devices or technologies. Use with non-Xilinx
-- devices or technologies is expressly prohibited and
-- immediately terminates your license unless covered by
-- a separate agreement.
--
-- Xilinx is providing this design, code, or information
-- "as is" solely for use in developing programs and
-- solutions for Xilinx devices. By providing this design,
-- code, or information as one possible implementation of
-- this feature, application or standard, Xilinx is making no
-- representation that this implementation is free from any
-- claims of infringement. You are responsible for
-- obtaining any rights you may require for your implementation.
-- Xilinx expressly disclaims any warranty whatsoever with
-- respect to the adequacy of the implementation, including
-- but not limited to any warranties or representations that this
-- implementation is free from claims of infringement, implied
-- warranties of merchantability or fitness for a particular
-- purpose.
--
-- Xilinx products are not intended for use in life support
-- appliances, devices, or systems. Use in such applications are
-- expressly prohibited.
--
-- This copyright and support notice must be retained as part
-- of this text at all times. (c) Copyright 2004-2007 Xilinx, Inc.
-- All rights reserved.

------------------------------------------------------------------------
-- Description:  This is the VHDL instantiation of a Virtex-5 GTP    
--               RocketIO tile for the Embedded Ethernet MAC.
--
--               Two GTP's must be instantiated regardless of how many  
--               GTPs are used in the MGT tile. 
------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.ALL;
use ieee.numeric_std.ALL;

library UNISIM;
use UNISIM.Vcomponents.ALL;


entity GTP_dual_1000X is
   port (
          RESETDONE_0           : out   std_logic;
          ENMCOMMAALIGN_0       : in    std_logic; 
          ENPCOMMAALIGN_0       : in    std_logic; 
          LOOPBACK_0            : in    std_logic; 
          RXUSRCLK_0            : in    std_logic;
          RXUSRCLK2_0           : in    std_logic;
          RXRESET_0             : in    std_logic;          
          TXCHARDISPMODE_0      : in    std_logic; 
          TXCHARDISPVAL_0       : in    std_logic; 
          TXCHARISK_0           : in    std_logic; 
          TXDATA_0              : in    std_logic_vector (7 downto 0); 
          TXUSRCLK_0            : in    std_logic; 
          TXUSRCLK2_0           : in    std_logic; 
          TXRESET_0             : in    std_logic; 
          RXCHARISCOMMA_0       : out   std_logic; 
          RXCHARISK_0           : out   std_logic;
          RXCLKCORCNT_0         : out   std_logic_vector (2 downto 0);           
          RXCOMMADET_0          : out   std_logic; 
          RXDATA_0              : out   std_logic_vector (7 downto 0); 
          RXDISPERR_0           : out   std_logic; 
          RXNOTINTABLE_0        : out   std_logic;
          RXREALIGN_0           : out   std_logic; 
          RXRUNDISP_0           : out   std_logic; 
          RXBUFERR_0            : out   std_logic;
          TXBUFERR_0            : out   std_logic; 
          PLLLKDET_0            : out   std_logic; 
          TXOUTCLK_0            : out   std_logic; 
          TXRUNDISP_0           : out   std_logic; 
          RXELECIDLE_0    	: out   std_logic;
          TX1N_0                : out   std_logic; 
          TX1P_0                : out   std_logic;
          RX1N_0                : in    std_logic; 
          RX1P_0                : in    std_logic;

          RESETDONE_1           : out   std_logic;
          ENMCOMMAALIGN_1       : in    std_logic; 
          ENPCOMMAALIGN_1       : in    std_logic; 
          LOOPBACK_1            : in    std_logic; 
          RXUSRCLK_1            : in    std_logic; 
          RXUSRCLK2_1           : in    std_logic; 
          RXRESET_1             : in    std_logic;          
          TXCHARDISPMODE_1      : in    std_logic; 
          TXCHARDISPVAL_1       : in    std_logic; 
          TXCHARISK_1           : in    std_logic; 
          TXDATA_1              : in    std_logic_vector (7 downto 0); 
          TXUSRCLK_1            : in    std_logic; 
          TXUSRCLK2_1           : in    std_logic; 
          TXRESET_1             : in    std_logic;
          RXCHARISCOMMA_1       : out   std_logic; 
          RXCHARISK_1           : out   std_logic;
          RXCLKCORCNT_1         : out   std_logic_vector (2 downto 0);           
          RXCOMMADET_1          : out   std_logic; 
          RXDATA_1              : out   std_logic_vector (7 downto 0); 
          RXDISPERR_1           : out   std_logic; 
          RXNOTINTABLE_1        : out   std_logic;
          RXREALIGN_1           : out   std_logic; 
          RXRUNDISP_1           : out   std_logic; 
          RXBUFERR_1            : out   std_logic;
          TXBUFERR_1            : out   std_logic; 
          PLLLKDET_1            : out   std_logic; 
          TXOUTCLK_1            : out   std_logic; 
          TXRUNDISP_1           : out   std_logic; 
          RXELECIDLE_1    	: out   std_logic;
          TX1N_1                : out   std_logic; 
          TX1P_1                : out   std_logic;
          RX1N_1                : in    std_logic; 
          RX1P_1                : in    std_logic;


          CLK_DS                : in    std_logic;
          REFCLKOUT             : out   std_logic;
          PMARESET              : in    std_logic;
          DCM_LOCKED            : in    std_logic;

          STATUS_INFO           : out   std_logic_vector(19 downto 0)
          );
end GTP_dual_1000X;


architecture structural of GTP_dual_1000X is

   ----- component GTP_DUAL -----
   component GTP_DUAL
      generic (
         AC_CAP_DIS_0 : boolean := TRUE;
         AC_CAP_DIS_1 : boolean := TRUE;
         ALIGN_COMMA_WORD_0 : integer := 1;
         ALIGN_COMMA_WORD_1 : integer := 1;
         CHAN_BOND_1_MAX_SKEW_0 : integer := 7;
         CHAN_BOND_1_MAX_SKEW_1 : integer := 7;
         CHAN_BOND_2_MAX_SKEW_0 : integer := 1;
         CHAN_BOND_2_MAX_SKEW_1 : integer := 1;
         CHAN_BOND_LEVEL_0 : integer := 0;
         CHAN_BOND_LEVEL_1 : integer := 0;
         CHAN_BOND_MODE_0 : string := "OFF";
         CHAN_BOND_MODE_1 : string := "OFF";
         CHAN_BOND_SEQ_1_1_0 : bit_vector := "0001001010";
         CHAN_BOND_SEQ_1_1_1 : bit_vector := "0001001010";
         CHAN_BOND_SEQ_1_2_0 : bit_vector := "0001001010";
         CHAN_BOND_SEQ_1_2_1 : bit_vector := "0001001010";
         CHAN_BOND_SEQ_1_3_0 : bit_vector := "0001001010";
         CHAN_BOND_SEQ_1_3_1 : bit_vector := "0001001010";
         CHAN_BOND_SEQ_1_4_0 : bit_vector := "0110111100";
         CHAN_BOND_SEQ_1_4_1 : bit_vector := "0110111100";
         CHAN_BOND_SEQ_1_ENABLE_0 : bit_vector := "1111";
         CHAN_BOND_SEQ_1_ENABLE_1 : bit_vector := "1111";
         CHAN_BOND_SEQ_2_1_0 : bit_vector := "0110111100";
         CHAN_BOND_SEQ_2_1_1 : bit_vector := "0110111100";
         CHAN_BOND_SEQ_2_2_0 : bit_vector := "0100111100";
         CHAN_BOND_SEQ_2_2_1 : bit_vector := "0100111100";
         CHAN_BOND_SEQ_2_3_0 : bit_vector := "0100111100";
         CHAN_BOND_SEQ_2_3_1 : bit_vector := "0100111100";
         CHAN_BOND_SEQ_2_4_0 : bit_vector := "0100111100";
         CHAN_BOND_SEQ_2_4_1 : bit_vector := "0100111100";
         CHAN_BOND_SEQ_2_ENABLE_0 : bit_vector := "1111";
         CHAN_BOND_SEQ_2_ENABLE_1 : bit_vector := "1111";
         CHAN_BOND_SEQ_2_USE_0 : boolean := TRUE;
         CHAN_BOND_SEQ_2_USE_1 : boolean := TRUE;
         CHAN_BOND_SEQ_LEN_0 : integer := 4;
         CHAN_BOND_SEQ_LEN_1 : integer := 4;
         CLK25_DIVIDER : integer := 4;
         CLKINDC_B : boolean := TRUE;
         CLK_CORRECT_USE_0 : boolean := TRUE;
         CLK_CORRECT_USE_1 : boolean := TRUE;
         CLK_COR_ADJ_LEN_0 : integer := 1;
         CLK_COR_ADJ_LEN_1 : integer := 1;
         CLK_COR_DET_LEN_0 : integer := 1;
         CLK_COR_DET_LEN_1 : integer := 1;
         CLK_COR_INSERT_IDLE_FLAG_0 : boolean := FALSE;
         CLK_COR_INSERT_IDLE_FLAG_1 : boolean := FALSE;
         CLK_COR_KEEP_IDLE_0 : boolean := FALSE;
         CLK_COR_KEEP_IDLE_1 : boolean := FALSE;
         CLK_COR_MAX_LAT_0 : integer := 18;
         CLK_COR_MAX_LAT_1 : integer := 18;
         CLK_COR_MIN_LAT_0 : integer := 16;
         CLK_COR_MIN_LAT_1 : integer := 16;
         CLK_COR_PRECEDENCE_0 : boolean := TRUE;
         CLK_COR_PRECEDENCE_1 : boolean := TRUE;
         CLK_COR_REPEAT_WAIT_0 : integer := 5;
         CLK_COR_REPEAT_WAIT_1 : integer := 5;
         CLK_COR_SEQ_1_1_0 : bit_vector := "0100011100";
         CLK_COR_SEQ_1_1_1 : bit_vector := "0100011100";
         CLK_COR_SEQ_1_2_0 : bit_vector := "0000000000";
         CLK_COR_SEQ_1_2_1 : bit_vector := "0000000000";
         CLK_COR_SEQ_1_3_0 : bit_vector := "0000000000";
         CLK_COR_SEQ_1_3_1 : bit_vector := "0000000000";
         CLK_COR_SEQ_1_4_0 : bit_vector := "0000000000";
         CLK_COR_SEQ_1_4_1 : bit_vector := "0000000000";
         CLK_COR_SEQ_1_ENABLE_0 : bit_vector := "1111";
         CLK_COR_SEQ_1_ENABLE_1 : bit_vector := "1111";
         CLK_COR_SEQ_2_1_0 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_1_1 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_2_0 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_2_1 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_3_0 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_3_1 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_4_0 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_4_1 : bit_vector := "0000000000";
         CLK_COR_SEQ_2_ENABLE_0 : bit_vector := "1111";
         CLK_COR_SEQ_2_ENABLE_1 : bit_vector := "1111";
         CLK_COR_SEQ_2_USE_0 : boolean := FALSE;
         CLK_COR_SEQ_2_USE_1 : boolean := FALSE;
         COMMA_10B_ENABLE_0 : bit_vector := "1111111111";
         COMMA_10B_ENABLE_1 : bit_vector := "1111111111";
         COMMA_DOUBLE_0 : boolean := FALSE;
         COMMA_DOUBLE_1 : boolean := FALSE;
         COM_BURST_VAL_0 : bit_vector := "1111";
         COM_BURST_VAL_1 : bit_vector := "1111";
         DEC_MCOMMA_DETECT_0 : boolean := TRUE;
         DEC_MCOMMA_DETECT_1 : boolean := TRUE;
         DEC_PCOMMA_DETECT_0 : boolean := TRUE;
         DEC_PCOMMA_DETECT_1 : boolean := TRUE;
         DEC_VALID_COMMA_ONLY_0 : boolean := TRUE;
         DEC_VALID_COMMA_ONLY_1 : boolean := TRUE;
         MCOMMA_10B_VALUE_0 : bit_vector := "1010000011";
         MCOMMA_10B_VALUE_1 : bit_vector := "1010000011";
         MCOMMA_DETECT_0 : boolean := TRUE;
         MCOMMA_DETECT_1 : boolean := TRUE;
         OOBDETECT_THRESHOLD_0 : bit_vector := "001";
         OOBDETECT_THRESHOLD_1 : bit_vector := "001";
         OOB_CLK_DIVIDER : integer := 4;
         OVERSAMPLE_MODE : boolean := FALSE;
         PCI_EXPRESS_MODE_0 : boolean := TRUE;
         PCI_EXPRESS_MODE_1 : boolean := TRUE;
         PCOMMA_10B_VALUE_0 : bit_vector := "0101111100";
         PCOMMA_10B_VALUE_1 : bit_vector := "0101111100";
         PCOMMA_DETECT_0 : boolean := TRUE;
         PCOMMA_DETECT_1 : boolean := TRUE;
         PLL_DIVSEL_FB : integer := 5;
         PLL_DIVSEL_REF : integer := 2;
         PLL_RXDIVSEL_OUT_0 : integer := 1;
         PLL_RXDIVSEL_OUT_1 : integer := 1;
         PLL_SATA_0 : boolean := FALSE;
         PLL_SATA_1 : boolean := FALSE;
         PLL_TXDIVSEL_COMM_OUT : integer := 1;
         PLL_TXDIVSEL_OUT_0 : integer := 1;
         PLL_TXDIVSEL_OUT_1 : integer := 1;
         PMA_CDR_SCAN_0 : bit_vector := X"6c08040";
         PMA_CDR_SCAN_1 : bit_vector := X"6c08040";
         PMA_RX_CFG_0 : bit_vector := X"0dce089";
         PMA_RX_CFG_1 : bit_vector := X"0dce089";
         PRBS_ERR_THRESHOLD_0 : bit_vector := X"00000001";
         PRBS_ERR_THRESHOLD_1 : bit_vector := X"00000001";
         RCV_TERM_GND_0 : boolean := TRUE;
         RCV_TERM_GND_1 : boolean := TRUE;
         RCV_TERM_MID_0 : boolean := FALSE;
         RCV_TERM_MID_1 : boolean := FALSE;
         RCV_TERM_VTTRX_0 : boolean := FALSE;
         RCV_TERM_VTTRX_1 : boolean := FALSE;
         RX_BUFFER_USE_0 : boolean := TRUE;
         RX_BUFFER_USE_1 : boolean := TRUE;
         RX_DECODE_SEQ_MATCH_0 : boolean := TRUE;
         RX_DECODE_SEQ_MATCH_1 : boolean := TRUE;
         RX_LOSS_OF_SYNC_FSM_0 : boolean := FALSE;
         RX_LOSS_OF_SYNC_FSM_1 : boolean := FALSE;
         RX_LOS_INVALID_INCR_0 : integer := 8;
         RX_LOS_INVALID_INCR_1 : integer := 8;
         RX_LOS_THRESHOLD_0 : integer := 128;
         RX_LOS_THRESHOLD_1 : integer := 128;
         RX_SLIDE_MODE_0 : string := "PCS";
         RX_SLIDE_MODE_1 : string := "PCS";
         RX_STATUS_FMT_0 : string := "PCIE";
         RX_STATUS_FMT_1 : string := "PCIE";
         RX_XCLK_SEL_0 : string := "RXREC";
         RX_XCLK_SEL_1 : string := "RXREC";
         SATA_BURST_VAL_0 : bit_vector := "100";
         SATA_BURST_VAL_1 : bit_vector := "100";
         SATA_IDLE_VAL_0 : bit_vector := "011";
         SATA_IDLE_VAL_1 : bit_vector := "011";
         SATA_MAX_BURST_0 : integer := 7;
         SATA_MAX_BURST_1 : integer := 7;
         SATA_MAX_INIT_0 : integer := 22;
         SATA_MAX_INIT_1 : integer := 22;
         SATA_MAX_WAKE_0 : integer := 7;
         SATA_MAX_WAKE_1 : integer := 7;
         SATA_MIN_BURST_0 : integer := 4;
         SATA_MIN_BURST_1 : integer := 4;
         SATA_MIN_INIT_0 : integer := 12;
         SATA_MIN_INIT_1 : integer := 12;
         SATA_MIN_WAKE_0 : integer := 4;
         SATA_MIN_WAKE_1 : integer := 4;
         SIM_GTPRESET_SPEEDUP : integer := 0;
         SIM_PLL_PERDIV2 : bit_vector := X"190";
         SIM_RECEIVER_DETECT_PASS0 : boolean := FALSE;
         SIM_RECEIVER_DETECT_PASS1 : boolean := FALSE;
         TERMINATION_CTRL : bit_vector := "10100";
         TERMINATION_IMP_0 : integer := 50;
         TERMINATION_IMP_1 : integer := 50;
         TERMINATION_OVRD : boolean := FALSE;
         TRANS_TIME_FROM_P2_0 : bit_vector := X"003c";
         TRANS_TIME_FROM_P2_1 : bit_vector := X"003c";
         TRANS_TIME_NON_P2_0 : bit_vector := X"0019";
         TRANS_TIME_NON_P2_1 : bit_vector := X"0019";
         TRANS_TIME_TO_P2_0 : bit_vector := X"0064";
         TRANS_TIME_TO_P2_1 : bit_vector := X"0064";
         TXRX_INVERT_0 : bit_vector := "00000";
         TXRX_INVERT_1 : bit_vector := "00000";
         TX_BUFFER_USE_0 : boolean := TRUE;
         TX_BUFFER_USE_1 : boolean := TRUE;
         TX_DIFF_BOOST_0 : boolean := FALSE;
         TX_DIFF_BOOST_1 : boolean := FALSE;
         TX_SYNC_FILTERB : integer := 1;
         TX_XCLK_SEL_0 : string := "TXUSR";
         TX_XCLK_SEL_1 : string := "TXUSR"
      );
      port (
         DO : out std_logic_vector(15 downto 0);
         DRDY : out std_ulogic;
         PHYSTATUS0 : out std_ulogic;
         PHYSTATUS1 : out std_ulogic;
         PLLLKDET : out std_ulogic;
         REFCLKOUT : out std_ulogic;
         RESETDONE0 : out std_ulogic;
         RESETDONE1 : out std_ulogic;
         RXBUFSTATUS0 : out std_logic_vector(2 downto 0);
         RXBUFSTATUS1 : out std_logic_vector(2 downto 0);
         RXBYTEISALIGNED0 : out std_ulogic;
         RXBYTEISALIGNED1 : out std_ulogic;
         RXBYTEREALIGN0 : out std_ulogic;
         RXBYTEREALIGN1 : out std_ulogic;
         RXCHANBONDSEQ0 : out std_ulogic;
         RXCHANBONDSEQ1 : out std_ulogic;
         RXCHANISALIGNED0 : out std_ulogic;
         RXCHANISALIGNED1 : out std_ulogic;
         RXCHANREALIGN0 : out std_ulogic;
         RXCHANREALIGN1 : out std_ulogic;
         RXCHARISCOMMA0 : out std_logic_vector(1 downto 0);
         RXCHARISCOMMA1 : out std_logic_vector(1 downto 0);
         RXCHARISK0 : out std_logic_vector(1 downto 0);
         RXCHARISK1 : out std_logic_vector(1 downto 0);
         RXCHBONDO0 : out std_logic_vector(2 downto 0);
         RXCHBONDO1 : out std_logic_vector(2 downto 0);
         RXCLKCORCNT0 : out std_logic_vector(2 downto 0);
         RXCLKCORCNT1 : out std_logic_vector(2 downto 0);
         RXCOMMADET0 : out std_ulogic;
         RXCOMMADET1 : out std_ulogic;
         RXDATA0 : out std_logic_vector(15 downto 0);
         RXDATA1 : out std_logic_vector(15 downto 0);
         RXDISPERR0 : out std_logic_vector(1 downto 0);
         RXDISPERR1 : out std_logic_vector(1 downto 0);
         RXELECIDLE0 : out std_ulogic;
         RXELECIDLE1 : out std_ulogic;
         RXLOSSOFSYNC0 : out std_logic_vector(1 downto 0);
         RXLOSSOFSYNC1 : out std_logic_vector(1 downto 0);
         RXNOTINTABLE0 : out std_logic_vector(1 downto 0);
         RXNOTINTABLE1 : out std_logic_vector(1 downto 0);
         RXOVERSAMPLEERR0 : out std_ulogic;
         RXOVERSAMPLEERR1 : out std_ulogic;
         RXPRBSERR0 : out std_ulogic;
         RXPRBSERR1 : out std_ulogic;
         RXRECCLK0 : out std_ulogic;
         RXRECCLK1 : out std_ulogic;
         RXRUNDISP0 : out std_logic_vector(1 downto 0);
         RXRUNDISP1 : out std_logic_vector(1 downto 0);
         RXSTATUS0 : out std_logic_vector(2 downto 0);
         RXSTATUS1 : out std_logic_vector(2 downto 0);
         RXVALID0 : out std_ulogic;
         RXVALID1 : out std_ulogic;
         TXBUFSTATUS0 : out std_logic_vector(1 downto 0);
         TXBUFSTATUS1 : out std_logic_vector(1 downto 0);
         TXKERR0 : out std_logic_vector(1 downto 0);
         TXKERR1 : out std_logic_vector(1 downto 0);
         TXN0 : out std_ulogic;
         TXN1 : out std_ulogic;
         TXOUTCLK0 : out std_ulogic;
         TXOUTCLK1 : out std_ulogic;
         TXP0 : out std_ulogic;
         TXP1 : out std_ulogic;
         TXRUNDISP0 : out std_logic_vector(1 downto 0);
         TXRUNDISP1 : out std_logic_vector(1 downto 0);
         CLKIN : in std_ulogic;
         DADDR : in std_logic_vector(6 downto 0);
         DCLK : in std_ulogic;
         DEN : in std_ulogic;
         DI : in std_logic_vector(15 downto 0);
         DWE : in std_ulogic;
         GTPRESET : in std_ulogic;
         GTPTEST : in std_logic_vector(3 downto 0);
         INTDATAWIDTH : in std_ulogic;
         LOOPBACK0 : in std_logic_vector(2 downto 0);
         LOOPBACK1 : in std_logic_vector(2 downto 0);
         PLLLKDETEN : in std_ulogic;
         PLLPOWERDOWN : in std_ulogic;
         PRBSCNTRESET0 : in std_ulogic;
         PRBSCNTRESET1 : in std_ulogic;
         REFCLKPWRDNB : in std_ulogic;
         RXBUFRESET0 : in std_ulogic;
         RXBUFRESET1 : in std_ulogic;
         RXCDRRESET0 : in std_ulogic;
         RXCDRRESET1 : in std_ulogic;
         RXCHBONDI0 : in std_logic_vector(2 downto 0);
         RXCHBONDI1 : in std_logic_vector(2 downto 0);
         RXCOMMADETUSE0 : in std_ulogic;
         RXCOMMADETUSE1 : in std_ulogic;
         RXDATAWIDTH0 : in std_ulogic;
         RXDATAWIDTH1 : in std_ulogic;
         RXDEC8B10BUSE0 : in std_ulogic;
         RXDEC8B10BUSE1 : in std_ulogic;
         RXELECIDLERESET0 : in std_ulogic;
         RXELECIDLERESET1 : in std_ulogic;
         RXENCHANSYNC0 : in std_ulogic;
         RXENCHANSYNC1 : in std_ulogic;
         RXENELECIDLERESETB : in std_ulogic;
         RXENEQB0 : in std_ulogic;
         RXENEQB1 : in std_ulogic;
         RXENMCOMMAALIGN0 : in std_ulogic;
         RXENMCOMMAALIGN1 : in std_ulogic;
         RXENPCOMMAALIGN0 : in std_ulogic;
         RXENPCOMMAALIGN1 : in std_ulogic;
         RXENPRBSTST0 : in std_logic_vector(1 downto 0);
         RXENPRBSTST1 : in std_logic_vector(1 downto 0);
         RXENSAMPLEALIGN0 : in std_ulogic;
         RXENSAMPLEALIGN1 : in std_ulogic;
         RXEQMIX0 : in std_logic_vector(1 downto 0);
         RXEQMIX1 : in std_logic_vector(1 downto 0);
         RXEQPOLE0 : in std_logic_vector(3 downto 0);
         RXEQPOLE1 : in std_logic_vector(3 downto 0);
         RXN0 : in std_ulogic;
         RXN1 : in std_ulogic;
         RXP0 : in std_ulogic;
         RXP1 : in std_ulogic;
         RXPMASETPHASE0 : in std_ulogic;
         RXPMASETPHASE1 : in std_ulogic;
         RXPOLARITY0 : in std_ulogic;
         RXPOLARITY1 : in std_ulogic;
         RXPOWERDOWN0 : in std_logic_vector(1 downto 0);
         RXPOWERDOWN1 : in std_logic_vector(1 downto 0);
         RXRESET0 : in std_ulogic;
         RXRESET1 : in std_ulogic;
         RXSLIDE0 : in std_ulogic;
         RXSLIDE1 : in std_ulogic;
         RXUSRCLK0 : in std_ulogic;
         RXUSRCLK1 : in std_ulogic;
         RXUSRCLK20 : in std_ulogic;
         RXUSRCLK21 : in std_ulogic;
         TXBUFDIFFCTRL0 : in std_logic_vector(2 downto 0);
         TXBUFDIFFCTRL1 : in std_logic_vector(2 downto 0);
         TXBYPASS8B10B0 : in std_logic_vector(1 downto 0);
         TXBYPASS8B10B1 : in std_logic_vector(1 downto 0);
         TXCHARDISPMODE0 : in std_logic_vector(1 downto 0);
         TXCHARDISPMODE1 : in std_logic_vector(1 downto 0);
         TXCHARDISPVAL0 : in std_logic_vector(1 downto 0);
         TXCHARDISPVAL1 : in std_logic_vector(1 downto 0);
         TXCHARISK0 : in std_logic_vector(1 downto 0);
         TXCHARISK1 : in std_logic_vector(1 downto 0);
         TXCOMSTART0 : in std_ulogic;
         TXCOMSTART1 : in std_ulogic;
         TXCOMTYPE0 : in std_ulogic;
         TXCOMTYPE1 : in std_ulogic;
         TXDATA0 : in std_logic_vector(15 downto 0);
         TXDATA1 : in std_logic_vector(15 downto 0);
         TXDATAWIDTH0 : in std_ulogic;
         TXDATAWIDTH1 : in std_ulogic;
         TXDETECTRX0 : in std_ulogic;
         TXDETECTRX1 : in std_ulogic;
         TXDIFFCTRL0 : in std_logic_vector(2 downto 0);
         TXDIFFCTRL1 : in std_logic_vector(2 downto 0);
         TXELECIDLE0 : in std_ulogic;
         TXELECIDLE1 : in std_ulogic;
         TXENC8B10BUSE0 : in std_ulogic;
         TXENC8B10BUSE1 : in std_ulogic;
         TXENPMAPHASEALIGN : in std_ulogic;
         TXENPRBSTST0 : in std_logic_vector(1 downto 0);
         TXENPRBSTST1 : in std_logic_vector(1 downto 0);
         TXINHIBIT0 : in std_ulogic;
         TXINHIBIT1 : in std_ulogic;
         TXPMASETPHASE : in std_ulogic;
         TXPOLARITY0 : in std_ulogic;
         TXPOLARITY1 : in std_ulogic;
         TXPOWERDOWN0 : in std_logic_vector(1 downto 0);
         TXPOWERDOWN1 : in std_logic_vector(1 downto 0);
         TXPREEMPHASIS0 : in std_logic_vector(2 downto 0);
         TXPREEMPHASIS1 : in std_logic_vector(2 downto 0);
         TXRESET0 : in std_ulogic;
         TXRESET1 : in std_ulogic;
         TXUSRCLK0 : in std_ulogic;
         TXUSRCLK1 : in std_ulogic;
         TXUSRCLK20 : in std_ulogic;
         TXUSRCLK21 : in std_ulogic
      );
   end component;
   
   attribute BOX_TYPE : string;
   attribute BOX_TYPE of
      GTP_DUAL : component is "PRIMITIVE";
      
  component rx_elastic_buffer
   port (
      -- Signals received from the RocketIO on RXRECCLK.
      rxrecclk                  : in  std_logic;
      reset                     : in  std_logic;
      rxchariscomma_rec         : in  std_logic;
      rxcharisk_rec             : in  std_logic;
      rxdisperr_rec             : in  std_logic;
      rxnotintable_rec          : in  std_logic;
      rxrundisp_rec             : in  std_logic;
      rxdata_rec                : in  std_logic_vector(7 downto 0);

      -- Signals reclocked onto RXUSRCLK2.
      rxusrclk2                 : in  std_logic;
      rxreset                   : in  std_logic;
      rxchariscomma_usr         : out std_logic;
      rxcharisk_usr             : out std_logic;
      rxdisperr_usr             : out std_logic;
      rxnotintable_usr          : out std_logic;
      rxrundisp_usr             : out std_logic;
      rxclkcorcnt_usr           : out std_logic_vector(2 downto 0);
      rxbuferr                  : out std_logic;
      rxdata_usr                : out std_logic_vector(7 downto 0)
   );
  end component;


  ----------------------------------------------------------------------
  -- Signal declarations for GTP
  ----------------------------------------------------------------------

   signal GND_BUS               : std_logic_vector (55 downto 0);
   signal PLLLOCK               : std_logic;

            
   signal RXNOTINTABLE_0_INT    : std_logic;   
   signal RXDATA_0_INT          : std_logic_vector (7 downto 0);
   signal RXCHARISK_0_INT       : std_logic;   
   signal RXDISPERR_0_INT       : std_logic;
   signal RXRUNDISP_0_INT       : std_logic;
         
   signal RXCHARISCOMMA_float0  : std_logic;
   signal RXCHARISK_float0      : std_logic;
   signal RXDATA_float0         : std_logic_vector (7 downto 0);
   signal RXDISPERR_float0      : std_logic;
   signal RXNOTINTABLE_float0   : std_logic;
   signal RXRUNDISP_float0      : std_logic;
   signal TXKERR_float0         : std_logic;
   signal TXRUNDISP_float0      : std_logic;
   signal RXBUFSTATUS_float0    : std_logic_vector(1 downto 0);
   signal TXBUFSTATUS_float0    : std_logic;

   signal gt_txoutclk1_0        : std_logic;

   signal rxelecidlereset0_i    : std_logic;
   signal rxelecidle0_i         : std_logic;
   signal resetdone0_i          : std_logic;
   signal rxenelecidleresetb_i  : std_logic;


   signal RXNOTINTABLE_1_INT    : std_logic;   
   signal RXDATA_1_INT          : std_logic_vector (7 downto 0);
   signal RXCHARISK_1_INT       : std_logic;   
   signal RXDISPERR_1_INT       : std_logic;
   signal RXRUNDISP_1_INT       : std_logic;

   signal RXCHARISCOMMA_float1  : std_logic;
   signal RXCHARISK_float1      : std_logic;
   signal RXDATA_float1         : std_logic_vector (7 downto 0);
   signal RXDISPERR_float1      : std_logic;
   signal RXNOTINTABLE_float1   : std_logic;
   signal RXRUNDISP_float1      : std_logic;
   signal TXKERR_float1         : std_logic;
   signal TXRUNDISP_float1      : std_logic;
   signal RXBUFSTATUS_float1    : std_logic_vector(1 downto 0);
   signal TXBUFSTATUS_float1    : std_logic;

   signal gt_txoutclk1_1        : std_logic;

   signal rxelecidlereset1_i    : std_logic;
   signal rxelecidle1_i         : std_logic;
   signal resetdone1_i          : std_logic;

   signal pma_reset_i   : std_logic;
   signal reset_r       : std_logic_vector(3 downto 0);
   signal refclk_out    : std_logic;
   attribute ASYNC_REG                        : string;
   attribute ASYNC_REG of reset_r             : signal is "TRUE";

   signal sig_status_info       : std_logic_vector(19 downto 0);
   signal sig_rxbuferr_0        : std_logic;
   signal sig_rxbuferr_1        : std_logic;

begin

   GND_BUS(55 downto 0) <= (others => '0');

   ----------------------------------------------------------------------
   -- Wait for both PLL's to lock   
   ----------------------------------------------------------------------

   
   PLLLKDET_0        <=   PLLLOCK;

   PLLLKDET_1        <=   PLLLOCK;


   ----------------------------------------------------------------------
   -- Wire internal signals to outputs   
   ----------------------------------------------------------------------

   RXNOTINTABLE_0  <=   RXNOTINTABLE_0_INT;
   RXDISPERR_0     <=   RXDISPERR_0_INT;
   TXOUTCLK_0      <=   gt_txoutclk1_0;

   rxelecidlereset0_i   <= rxelecidle0_i and resetdone0_i;
   RESETDONE_0          <= resetdone0_i;
   RXELECIDLE_0         <= rxelecidle0_i;

  
   RXNOTINTABLE_1  <=   RXNOTINTABLE_1_INT;
   RXDISPERR_1     <=   RXDISPERR_1_INT;
   TXOUTCLK_1      <=   gt_txoutclk1_1;

   rxelecidlereset1_i   <= rxelecidle1_i and resetdone1_i;
   rxenelecidleresetb_i <= not(rxelecidlereset0_i or rxelecidlereset1_i);
   RESETDONE_1          <= resetdone1_i;
   RXELECIDLE_1         <= rxelecidle1_i;

 

   REFCLKOUT <= refclk_out;

   --------------------------------------------------------------------
   -- RocketIO PMA reset circuitry
   --------------------------------------------------------------------
   process(PMARESET, refclk_out)
   begin
     if (PMARESET = '1') then
       reset_r <= "1111";
     elsif refclk_out'event and refclk_out = '1' then
       reset_r <= reset_r(2 downto 0) & PMARESET;
     end if;
   end process;
  
   pma_reset_i <= reset_r(3);

   ----------------------------------------------------------------------
   -- Instantiate the Virtex-5 GTP
   -- EMAC0 connects to GTP 0 and EMAC1 connects to GTP 1
   ----------------------------------------------------------------------

   GTP_1000X : GTP_DUAL
	generic map ( 
		CLK25_DIVIDER         => 5,
		CLK_COR_ADJ_LEN_0     => 2,
		CLK_COR_ADJ_LEN_1     => 2,
		CLK_COR_DET_LEN_0     => 2,
		CLK_COR_DET_LEN_1     => 2,
		CLK_COR_SEQ_1_1_0     => "0110111100",
		CLK_COR_SEQ_1_1_1     => "0110111100",
		CLK_COR_SEQ_1_2_0     => "0001010000",
		CLK_COR_SEQ_1_2_1     => "0001010000",
		CLK_COR_SEQ_2_1_0     => "0110111100",
		CLK_COR_SEQ_2_1_1     => "0110111100",
		CLK_COR_SEQ_2_2_0     => "0010110101",
		CLK_COR_SEQ_2_2_1     => "0010110101",
		CLK_COR_SEQ_2_USE_0   => TRUE,
		CLK_COR_SEQ_2_USE_1   => TRUE,
		COMMA_10B_ENABLE_0    => "0001111111",
		COMMA_10B_ENABLE_1    => "0001111111",
		MCOMMA_10B_VALUE_0    => "1010000011",
		MCOMMA_10B_VALUE_1    => "1010000011",
		PCI_EXPRESS_MODE_0    => FALSE,
		PCI_EXPRESS_MODE_1    => FALSE,
		PCOMMA_10B_VALUE_0    => "0101111100",
		PCOMMA_10B_VALUE_1    => "0101111100",
		PLL_TXDIVSEL_COMM_OUT => 2,
		PLL_DIVSEL_FB         => 2,
		PLL_DIVSEL_REF        => 1,
		PLL_RXDIVSEL_OUT_0    => 2,
		PLL_RXDIVSEL_OUT_1    => 2,
		TXRX_INVERT_0         => "00000",
		TXRX_INVERT_1         => "00000",
		AC_CAP_DIS_0          => TRUE,
		AC_CAP_DIS_1          => TRUE,
		RCV_TERM_GND_0        => FALSE,
		RCV_TERM_GND_1        => FALSE,
		RCV_TERM_MID_0        => FALSE,
		RCV_TERM_MID_1        => FALSE,
		RCV_TERM_VTTRX_0      => FALSE,
		RCV_TERM_VTTRX_1      => FALSE,
                TX_DIFF_BOOST_0       => TRUE,
                TX_DIFF_BOOST_1       => TRUE,
                PLL_SATA_0            => TRUE,
                PLL_SATA_1            => TRUE,
                PMA_RX_CFG_0          => x"0dce110",
                PMA_RX_CFG_1          => x"0dce110")
	port map (
		DO                       => open,
		DRDY                     => open,
		PLLLKDET                 => PLLLOCK,
		REFCLKOUT                => refclk_out,
		CLKIN                    => CLK_DS,
		DADDR                    => "0000000",
		DCLK                     => '0',
		DEN                      => '0',
		DI                       => "0000000000000000",
		DWE                      => '0',
		GTPRESET                 => pma_reset_i,
		INTDATAWIDTH             => '1',
		PLLLKDETEN               => '1',
		PLLPOWERDOWN             => '0',
		REFCLKPWRDNB             => '1',
		TXENPMAPHASEALIGN        => '0',
		TXPMASETPHASE            => '0',
		GTPTEST                  => "0000",
		RXENELECIDLERESETB       => rxenelecidleresetb_i,
		-- Connect 0 to EMAC0
		PHYSTATUS0               => sig_status_info(0),
		RESETDONE0               => resetdone0_i,
		RXBYTEISALIGNED0         => open,
		RXCHANBONDSEQ0           => open,
		RXCHANISALIGNED0         => open,
		RXCHANREALIGN0           => open,
		RXCHBONDO0               => open,
		RXCOMMADET0              => RXCOMMADET_0,
		RXELECIDLE0              => rxelecidle0_i,
		RXLOSSOFSYNC0            => sig_status_info(11 downto 10),
		RXOVERSAMPLEERR0         => open,
		RXRECCLK0                => open,
		RXRUNDISP0(1)            => RXRUNDISP_float0,
		RXRUNDISP0(0)            => RXRUNDISP_0_INT,
		RXNOTINTABLE0(1)         => RXNOTINTABLE_float0,
		RXNOTINTABLE0(0)         => RXNOTINTABLE_0_INT,
		RXDISPERR0(1)            => RXDISPERR_float0,
		RXDISPERR0(0)            => RXDISPERR_0_INT,
		RXDATA0(15 downto 8)     => RXDATA_float0,
		RXDATA0(7 downto 0)      => RXDATA_0_INT,
		RXCHARISK0(1)            => RXCHARISK_float0,
		RXCHARISK0(0)            => RXCHARISK_0_INT,
		RXCHARISCOMMA0(1)        => RXCHARISCOMMA_float0,
		RXCHARISCOMMA0(0)        => RXCHARISCOMMA_0,
		RXBUFSTATUS0(1 downto 0) => RXBUFSTATUS_float0,
		RXBUFSTATUS0(2)          => sig_RXBUFERR_0,
		RXCLKCORCNT0             => RXCLKCORCNT_0,
		RXBYTEREALIGN0           => RXREALIGN_0,
		RXPRBSERR0               => open,
		RXSTATUS0                => sig_status_info(16 downto 14),
		RXVALID0                 => open,
		TXBUFSTATUS0(0)          => TXBUFSTATUS_float0,
		TXBUFSTATUS0(1)          => TXBUFERR_0,
		TXKERR0                  => open,
		TXN0                     => TX1N_0,
		TXOUTCLK0                => gt_txoutclk1_0,
		TXP0                     => TX1P_0,
		TXRUNDISP0(1)            => TXRUNDISP_float0,
		TXRUNDISP0(0)            => TXRUNDISP_0,		
		LOOPBACK0(2 downto 1)    => "00",
		LOOPBACK0(0)             => LOOPBACK_0,
		PRBSCNTRESET0            => '0',		
		RXBUFRESET0              => RXRESET_0,
		RXRESET0                 => RXRESET_0,
		RXENMCOMMAALIGN0         => ENMCOMMAALIGN_0,
		RXENPCOMMAALIGN0         => ENPCOMMAALIGN_0,
		RXUSRCLK0                => RXUSRCLK_0,
		RXUSRCLK20               => RXUSRCLK2_0,
		RXCDRRESET0              => '0',
		RXCHBONDI0               => "000",
		RXCOMMADETUSE0           => '1',
		RXDATAWIDTH0             => '0',
		RXDEC8B10BUSE0           => '1',
		RXENCHANSYNC0            => '0',
		RXENEQB0                 => '1',
		RXENPRBSTST0             => "00",
		RXENSAMPLEALIGN0         => '0',
		RXEQMIX0                 => "00",
		RXEQPOLE0                => "0000",
		RXN0                     => RX1N_0,
		RXP0                     => RX1P_0,
		RXPMASETPHASE0           => '0',
		RXPOLARITY0              => '0',
		RXPOWERDOWN0             => "00",
		RXSLIDE0                 => '0',
		TXBUFDIFFCTRL0           => "000",
		TXBYPASS8B10B0           => "00",
		TXCHARDISPMODE0(1)       => '0',
		TXCHARDISPMODE0(0)       => TXCHARDISPMODE_0,
		TXCHARDISPVAL0(1)        => '0',
		TXCHARDISPVAL0(0)        => TXCHARDISPVAL_0,
		TXCHARISK0(1)            => '0',
		TXCHARISK0(0)            => TXCHARISK_0,
		TXDATA0(15 downto 8)     => "00000000",
		TXDATA0(7 downto 0)      => TXDATA_0,
		TXCOMSTART0              => '0',
		TXCOMTYPE0               => '0',
		TXDATAWIDTH0             => '0',
		TXDETECTRX0              => '0',
		TXDIFFCTRL0              => "000",
		TXELECIDLE0              => '0',
		TXENC8B10BUSE0           => '1',
		TXENPRBSTST0             => "00",
		TXINHIBIT0               => '0',
		TXPOLARITY0              => '0',
		TXPOWERDOWN0             => "00",
		TXPREEMPHASIS0           => "000",
		TXRESET0                 => TXRESET_0,
		TXUSRCLK0                => TXUSRCLK_0,
		TXUSRCLK20               => TXUSRCLK2_0,
                RXELECIDLERESET0         => rxelecidlereset0_i,
        -- Connect 1 to EMAC1
		PHYSTATUS1               => sig_status_info(1),
		RESETDONE1               => resetdone1_i,
		RXBYTEISALIGNED1         => open,
		RXCHANBONDSEQ1           => open,
		RXCHANISALIGNED1         => open,
		RXCHANREALIGN1           => open,
		RXCHBONDO1               => open,
		RXCOMMADET1              => RXCOMMADET_1,
		RXELECIDLE1              => rxelecidle1_i,
		RXLOSSOFSYNC1            => sig_status_info(13 downto 12),
		RXOVERSAMPLEERR1         => open,
		RXRECCLK1                => open,
		RXRUNDISP1(1)            => RXRUNDISP_float1,
		RXRUNDISP1(0)            => RXRUNDISP_1_INT,
		RXNOTINTABLE1(1)         => RXNOTINTABLE_float1,
		RXNOTINTABLE1(0)         => RXNOTINTABLE_1_INT,
		RXDISPERR1(1)            => RXDISPERR_float1,
		RXDISPERR1(0)            => RXDISPERR_1_INT,
		RXDATA1(15 downto 8)     => RXDATA_float1,
		RXDATA1(7 downto 0)      => RXDATA_1_INT,
		RXCHARISK1(1)            => RXCHARISK_float1,
		RXCHARISK1(0)            => RXCHARISK_1_INT,
		RXCHARISCOMMA1(1)        => RXCHARISCOMMA_float1,
		RXCHARISCOMMA1(0)        => RXCHARISCOMMA_1,
		RXBUFSTATUS1(1 downto 0) => RXBUFSTATUS_float1,
		RXBUFSTATUS1(2)          => sig_RXBUFERR_1,
		RXCLKCORCNT1             => RXCLKCORCNT_1,
		RXBYTEREALIGN1           => RXREALIGN_1,
		RXPRBSERR1               => open,
		RXSTATUS1                => sig_status_info(19 downto 17),
		RXVALID1                 => open,
		TXBUFSTATUS1(0)          => TXBUFSTATUS_float1,
		TXBUFSTATUS1(1)          => TXBUFERR_1,
		TXKERR1                  => open,
		TXN1                     => TX1N_1,
		TXOUTCLK1                => gt_txoutclk1_1,
		TXP1                     => TX1P_1,
		TXRUNDISP1(1)            => TXRUNDISP_float1,
		TXRUNDISP1(0)            => TXRUNDISP_1,		
		LOOPBACK1(2 downto 1)    => "00",
		LOOPBACK1(0)             => LOOPBACK_1,
		PRBSCNTRESET1            => '0',		
		RXBUFRESET1              => RXRESET_1,
		RXRESET1                 => RXRESET_1,
		RXENMCOMMAALIGN1         => ENMCOMMAALIGN_1,
		RXENPCOMMAALIGN1         => ENPCOMMAALIGN_1,
		RXUSRCLK1                => RXUSRCLK_1,
		RXUSRCLK21               => RXUSRCLK2_1,
		RXCDRRESET1              => '0',
		RXCHBONDI1               => "000",
		RXCOMMADETUSE1           => '1',
		RXDATAWIDTH1             => '0',
		RXDEC8B10BUSE1           => '1',
		RXENCHANSYNC1            => '0',
		RXENEQB1                 => '1',
		RXENPRBSTST1             => "00",
		RXENSAMPLEALIGN1         => '0',
		RXEQMIX1                 => "00",
		RXEQPOLE1                => "0000",
		RXN1                     => RX1N_1,
		RXP1                     => RX1P_1,
		RXPMASETPHASE1           => '0',
		RXPOLARITY1              => '0',
		RXPOWERDOWN1             => "00",
		RXSLIDE1                 => '0',
		TXBUFDIFFCTRL1           => "000",
		TXBYPASS8B10B1           => "00",
		TXCHARDISPMODE1(1)       => '0',
		TXCHARDISPMODE1(0)       => TXCHARDISPMODE_1,
		TXCHARDISPVAL1(1)        => '0',
		TXCHARDISPVAL1(0)        => TXCHARDISPVAL_1,
		TXCHARISK1(1)            => '0',
		TXCHARISK1(0)            => TXCHARISK_1,
		TXDATA1(15 downto 8)     => "00000000",
		TXDATA1(7 downto 0)      => TXDATA_1,
		TXCOMSTART1              => '0',
		TXCOMTYPE1               => '0',
		TXDATAWIDTH1             => '0',
		TXDETECTRX1              => '0',
		TXDIFFCTRL1              => "000",
		TXELECIDLE1              => '0',
		TXENC8B10BUSE1           => '1',
		TXENPRBSTST1             => "00",
		TXINHIBIT1               => '0',
		TXPOLARITY1              => '0',
		TXPOWERDOWN1             => "00",
		TXPREEMPHASIS1           => "000",
		TXRESET1                 => TXRESET_1,
		TXUSRCLK1                => TXUSRCLK_1,
		TXUSRCLK21               => TXUSRCLK2_1,
                RXELECIDLERESET1         => rxelecidlereset1_i);

                       
      -- sig_status_info(0) <= PHYSTATUS0;
      -- sig_status_info(1) <= PHYSTATUS1;
      sig_status_info(2) <= resetdone0_i;
      sig_status_info(3) <= resetdone1_i;
		sig_status_info(6 downto 4) <= sig_RXBUFERR_0 & RXBUFSTATUS_float0;
         -- RXBUFSTATUS0
		sig_status_info(9 downto 7) <= sig_RXBUFERR_1 & RXBUFSTATUS_float1;
         -- RXBUFSTATUS1
      -- sig_status_info(11 downto 10) <= RXLOSSOFSYNC0;
      -- sig_status_info(13 downto 12) <= RXLOSSOFSYNC1;
      -- sig_status_info(16 downto 14) <= RXSTATUS0
      -- sig_status_info(19 downto 17) <= RXSTATUS1
      STATUS_INFO <= sig_status_info;

      RXBUFERR_0 <= sig_RXBUFERR_0;
      RXBUFERR_1 <= sig_RXBUFERR_1;
   -------------------------------------------------------------------------------
   -- EMAC0 to GTP logic shim
   -------------------------------------------------------------------------------

   -- When the RXNOTINTABLE condition is detected, the Virtex5 RocketIO
   -- GTP outputs the raw 10B code in a bit swapped order to that of the
   -- Virtex-II Pro RocketIO.
   gen_rxdata0 : process (RXNOTINTABLE_0_INT, RXDISPERR_0_INT, RXCHARISK_0_INT, RXDATA_0_INT,
                         RXRUNDISP_0_INT)
   begin
      if RXNOTINTABLE_0_INT = '1' then
         RXDATA_0(0) <= RXDISPERR_0_INT;
         RXDATA_0(1) <= RXCHARISK_0_INT;
         RXDATA_0(2) <= RXDATA_0_INT(7);
         RXDATA_0(3) <= RXDATA_0_INT(6);
         RXDATA_0(4) <= RXDATA_0_INT(5);
         RXDATA_0(5) <= RXDATA_0_INT(4);
         RXDATA_0(6) <= RXDATA_0_INT(3);
         RXDATA_0(7) <= RXDATA_0_INT(2);
         RXRUNDISP_0 <= RXDATA_0_INT(1);
         RXCHARISK_0 <= RXDATA_0_INT(0);

      else
         RXDATA_0    <= RXDATA_0_INT;
         RXRUNDISP_0 <= RXRUNDISP_0_INT;
         RXCHARISK_0 <= RXCHARISK_0_INT;

      end if;
   end process gen_rxdata0;


   -------------------------------------------------------------------------------
   -- EMAC1 to GTP logic shim
   -------------------------------------------------------------------------------

   -- When the RXNOTINTABLE condition is detected, the Virtex5 RocketIO
   -- GTP outputs the raw 10B code in a bit swapped order to that of the
   -- Virtex-II Pro RocketIO.
   gen_rxdata1 : process (RXNOTINTABLE_1_INT, RXDISPERR_1_INT, RXCHARISK_1_INT, RXDATA_1_INT,
                         RXRUNDISP_1_INT)
   begin
      if RXNOTINTABLE_1_INT = '1' then
         RXDATA_1(0) <= RXDISPERR_1_INT;
         RXDATA_1(1) <= RXCHARISK_1_INT;
         RXDATA_1(2) <= RXDATA_1_INT(7);
         RXDATA_1(3) <= RXDATA_1_INT(6);
         RXDATA_1(4) <= RXDATA_1_INT(5);
         RXDATA_1(5) <= RXDATA_1_INT(4);
         RXDATA_1(6) <= RXDATA_1_INT(3);
         RXDATA_1(7) <= RXDATA_1_INT(2);
         RXRUNDISP_1 <= RXDATA_1_INT(1);
         RXCHARISK_1 <= RXDATA_1_INT(0);

      else
         RXDATA_1    <= RXDATA_1_INT;
         RXRUNDISP_1 <= RXRUNDISP_1_INT;
         RXCHARISK_1 <= RXCHARISK_1_INT;

      end if;
   end process gen_rxdata1;

end structural;
