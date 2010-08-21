-------------------------------------------------------------------------------
-- Title      :Block level wrapper
-- Project    : XAUI
-------------------------------------------------------------------------------
-- File       : xaui_gtx_block.vhd
-------------------------------------------------------------------------------
-- Description: This file is a wrapper for the XAUI core. It contains the XAUI
-- core, the transceivers and some transceiver logic.
-------------------------------------------------------------------------------
-- (c) Copyright 2005 - 2009 Xilinx, Inc. All rights reserved.
-- This file contains confidential and proprietary information
-- of Xilinx, Inc. and is protected under U.S. and
-- international copyright and other intellectual property
-- laws.
--
-- DISCLAIMER
-- This disclaimer is not a license and does not grant any
-- rights to the materials distributed herewith. Except as
-- otherwise provided in a valid license issued to you by
-- Xilinx, and to the maximum extent permitted by applicable
-- law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
-- WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
-- AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
-- BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
-- INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
-- (2) Xilinx shall not be liable (whether in contract or tort,
-- including negligence, or under any other theory of
-- liability) for any loss or damage of any kind or nature
-- related to, arising under or in connection with these
-- materials, including for any direct, or any indirect,
-- special, incidental, or consequential loss or damage
-- (including loss of data, profits, goodwill, or any type of
-- loss or damage suffered as a result of any action brought
-- by a third party) even if such damage or loss was
-- reasonably foreseeable or Xilinx had been advised of the
-- possibility of the same.
--
-- CRITICAL APPLICATIONS
-- Xilinx products are not designed or intended to be fail-
-- safe, or for use in any application requiring fail-safe
-- performance, such as life-support or safety devices or
-- systems, Class III medical devices, nuclear facilities,
-- applications related to the deployment of airbags, or any
-- other applications that could lead to death, personal
-- injury, or severe property or environmental damage
-- (individually and collectively, "Critical
-- Applications"). Customer assumes the sole risk and
-- liability of any use of Xilinx products in Critical
-- Applications, subject only to applicable laws and
-- regulations governing limitations on product liability.
--
-- THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
-- PART OF THIS FILE AT ALL TIMES.
-------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity xaui_gtx_block is
    generic (
      CH01_SWAP                    : boolean := false;
      CH23_SWAP                    : boolean := false;
      WRAPPER_SIM_MODE             : string  := "FAST";
      WRAPPER_SIM_GTXRESET_SPEEDUP : integer := 0
      
      );
    port (
      dclk             : in  std_logic;
      clk156           : in  std_logic;
      refclk           : in  std_logic;
      reset            : in  std_logic;
      reset156         : in  std_logic;
      txoutclk         : out std_logic;
      xgmii_txd        : in  std_logic_vector(63 downto 0);
      xgmii_txc        : in  std_logic_vector(7 downto 0);
      xgmii_rxd        : out std_logic_vector(63 downto 0);
      xgmii_rxc        : out std_logic_vector(7 downto 0);
      xaui_tx_l0_p     : out std_logic;
      xaui_tx_l0_n     : out std_logic;
      xaui_tx_l1_p     : out std_logic;
      xaui_tx_l1_n     : out std_logic;
      xaui_tx_l2_p     : out std_logic;
      xaui_tx_l2_n     : out std_logic;
      xaui_tx_l3_p     : out std_logic;
      xaui_tx_l3_n     : out std_logic;
      xaui_rx_l0_p     : in  std_logic;
      xaui_rx_l0_n     : in  std_logic;
      xaui_rx_l1_p     : in  std_logic;
      xaui_rx_l1_n     : in  std_logic;
      xaui_rx_l2_p     : in  std_logic;
      xaui_rx_l2_n     : in  std_logic;
      xaui_rx_l3_p     : in  std_logic;
      xaui_rx_l3_n     : in  std_logic;
      txlock           : out std_logic;
      rxpolarity       : in  std_logic_vector(3 downto 0) := "0000";
      txpolarity       : in  std_logic_vector(3 downto 0) := "0000";
      signal_detect    : in  std_logic_vector(3 downto 0);
      align_status     : out std_logic;
      sync_status      : out std_logic_vector(3 downto 0);
      drp_addr         : in  std_logic_vector(6 downto 0);
      drp_en           : in  std_logic_vector(1 downto 0);
      drp_i            : in  std_logic_vector(15 downto 0);
      drp_o            : out std_logic_vector(31 downto 0);
      drp_rdy          : out std_logic_vector(1 downto 0);
      drp_we           : in  std_logic_vector(1 downto 0);
      mgt_tx_ready     : out std_logic;
      configuration_vector : in  std_logic_vector(6 downto 0);
      status_vector        : out std_logic_vector(7 downto 0)
);
end xaui_gtx_block;

library ieee;
use ieee.numeric_std.all;

library unisim;
use unisim.vcomponents.all;

architecture wrapper of xaui_gtx_block is

----------------------------------------------------------------------------
-- Component Declaration for the XAUI core.
----------------------------------------------------------------------------

   component xaui_gtx
      port (
      reset            : in  std_logic;
      xgmii_txd        : in  std_logic_vector(63 downto 0);
      xgmii_txc        : in  std_logic_vector(7 downto 0);
      xgmii_rxd        : out std_logic_vector(63 downto 0);
      xgmii_rxc        : out std_logic_vector(7 downto 0);
      usrclk           : in  std_logic;
      mgt_txdata       : out std_logic_vector(63 downto 0);
      mgt_txcharisk    : out std_logic_vector(7 downto 0);
      mgt_rxdata       : in  std_logic_vector(63 downto 0);
      mgt_rxcharisk    : in  std_logic_vector(7 downto 0);
      mgt_codevalid    : in  std_logic_vector(7 downto 0);
      mgt_codecomma    : in  std_logic_vector(7 downto 0);
      mgt_enable_align : out std_logic_vector(3 downto 0);
      mgt_enchansync   : out std_logic;
      mgt_syncok       : in  std_logic_vector(3 downto 0);
      mgt_rxlock       : in  std_logic_vector(3 downto 0);
      mgt_loopback     : out std_logic;
      mgt_powerdown    : out std_logic;
      mgt_tx_reset     : in  std_logic_vector(3 downto 0);
      mgt_rx_reset     : in  std_logic_vector(3 downto 0);
      signal_detect    : in  std_logic_vector(3 downto 0);
      align_status     : out std_logic;
      sync_status      : out std_logic_vector(3 downto 0);
      configuration_vector : in  std_logic_vector(6 downto 0);
      status_vector    : out std_logic_vector(7 downto 0));
  end component;

 --------------------------------------------------------------------------
 -- Component declaration for the RocketIO transceiver container
 --------------------------------------------------------------------------

component ROCKETIO_WRAPPER is
generic
(
    CH01_SWAP                       : boolean := false;
    CH23_SWAP                       : boolean := false;
    -- Simulation attributes
    WRAPPER_SIM_MODE                : string    := "FAST"; -- Set to Fast Functional Simulation Model
    WRAPPER_SIM_GTXRESET_SPEEDUP    : integer   := 0;      -- Set to 1 to speed up sim reset
    WRAPPER_SIM_PLL_PERDIV2         : bit_vector:= x"140"  -- Set to the VCO Unit Interval time
);
port
(

    --_________________________________________________________________________
    --_________________________________________________________________________
    --TILE0  (Location)

    ------------------------ Loopback and Powerdown Ports ----------------------
    TILE0_LOOPBACK0_IN             :    in    std_logic_vector(2 downto 0);
    TILE0_LOOPBACK1_IN             :    in    std_logic_vector(2 downto 0);
    TILE0_RXPOWERDOWN0_IN          :    in    std_logic_vector(1 downto 0);
    TILE0_RXPOWERDOWN1_IN          :    in    std_logic_vector(1 downto 0);
    TILE0_TXPOWERDOWN0_IN          :    in    std_logic_vector(1 downto 0);
    TILE0_TXPOWERDOWN1_IN          :    in    std_logic_vector(1 downto 0);
    ----------------------- Receive Ports - 8b10b Decoder ----------------------
    TILE0_RXCHARISCOMMA0_OUT       :    out   std_logic_vector(1 downto 0);
    TILE0_RXCHARISCOMMA1_OUT       :    out   std_logic_vector(1 downto 0);
    TILE0_RXCHARISK0_OUT           :    out   std_logic_vector(1 downto 0);
    TILE0_RXCHARISK1_OUT           :    out   std_logic_vector(1 downto 0);
    TILE0_RXDISPERR0_OUT           :    out   std_logic_vector(1 downto 0);
    TILE0_RXDISPERR1_OUT           :    out   std_logic_vector(1 downto 0);
    TILE0_RXNOTINTABLE0_OUT        :    out   std_logic_vector(1 downto 0);
    TILE0_RXNOTINTABLE1_OUT        :    out   std_logic_vector(1 downto 0);
    ------------------- Receive Ports - Channel Bonding Ports ------------------
    TILE0_RXCHANBONDSEQ0_OUT       :    out   std_logic;
    TILE0_RXCHANBONDSEQ1_OUT       :    out   std_logic;
    TILE0_RXENCHANSYNC0_IN         :    in    std_logic;
    TILE0_RXENCHANSYNC1_IN         :    in    std_logic;
    ------------------- Receive Ports - Clock Correction Ports -----------------
    TILE0_RXCLKCORCNT0_OUT         :    out   std_logic_vector(2 downto 0);
    TILE0_RXCLKCORCNT1_OUT         :    out   std_logic_vector(2 downto 0);
    --------------- Receive Ports - Comma Detection and Alignment --------------
    TILE0_RXBYTEISALIGNED0_OUT     :    out   std_logic;
    TILE0_RXBYTEISALIGNED1_OUT     :    out   std_logic;
    TILE0_RXBYTEREALIGN0_OUT       :    out   std_logic;
    TILE0_RXBYTEREALIGN1_OUT       :    out   std_logic;
    TILE0_RXCOMMADET0_OUT          :    out   std_logic;
    TILE0_RXCOMMADET1_OUT          :    out   std_logic;
    TILE0_RXENMCOMMAALIGN0_IN      :    in    std_logic;
    TILE0_RXENMCOMMAALIGN1_IN      :    in    std_logic;
    TILE0_RXENPCOMMAALIGN0_IN      :    in    std_logic;
    TILE0_RXENPCOMMAALIGN1_IN      :    in    std_logic;
    ------------------- Receive Ports - RX Data Path interface -----------------
    TILE0_RXDATA0_OUT              :    out   std_logic_vector(15 downto 0);
    TILE0_RXDATA1_OUT              :    out   std_logic_vector(15 downto 0);
    TILE0_RXRESET0_IN              :    in    std_logic;
    TILE0_RXRESET1_IN              :    in    std_logic;
    TILE0_RXUSRCLK0_IN             :    in    std_logic;
    TILE0_RXUSRCLK1_IN             :    in    std_logic;
    TILE0_RXUSRCLK20_IN            :    in    std_logic;
    TILE0_RXUSRCLK21_IN            :    in    std_logic;
    ------- Receive Ports - RX Driver,OOB signalling,Coupling and Eq.,CDR ------
    TILE0_RXCDRRESET0_IN           :    in    std_logic;
    TILE0_RXCDRRESET1_IN           :    in    std_logic;
    TILE0_RXELECIDLE0_OUT          :    out   std_logic;
    TILE0_RXELECIDLE1_OUT          :    out   std_logic;
    TILE0_RXN0_IN                  :    in    std_logic;
    TILE0_RXN1_IN                  :    in    std_logic;
    TILE0_RXP0_IN                  :    in    std_logic;
    TILE0_RXP1_IN                  :    in    std_logic;
    -------- Receive Ports - RX Elastic Buffer and Phase Alignment Ports -------
    TILE0_RXBUFRESET0_IN           :    in    std_logic;
    TILE0_RXBUFRESET1_IN           :    in    std_logic;
    TILE0_RXBUFSTATUS0_OUT         :    out   std_logic_vector(2 downto 0);
    TILE0_RXBUFSTATUS1_OUT         :    out   std_logic_vector(2 downto 0);
    TILE0_RXCHANISALIGNED0_OUT     :    out   std_logic;
    TILE0_RXCHANISALIGNED1_OUT     :    out   std_logic;
    TILE0_RXCHANREALIGN0_OUT       :    out   std_logic;
    TILE0_RXCHANREALIGN1_OUT       :    out   std_logic;
    --------------- Receive Ports - RX Loss-of-sync State Machine --------------
    TILE0_RXLOSSOFSYNC0_OUT        :    out   std_logic_vector(1 downto 0);
    TILE0_RXLOSSOFSYNC1_OUT        :    out   std_logic_vector(1 downto 0);
    -------------- Receive Ports - polarity  -----------------------------------
    TILE0_RXPOLARITY0              :    in   std_logic;
    TILE0_RXPOLARITY1              :    in   std_logic;
    ------------- Shared Ports - Dynamic Reconfiguration Port (DRP) ------------
    TILE0_DADDR_IN                 :    in    std_logic_vector(6 downto 0);
    TILE0_DCLK_IN                  :    in    std_logic;
    TILE0_DEN_IN                   :    in    std_logic;
    TILE0_DI_IN                    :    in    std_logic_vector(15 downto 0);
    TILE0_DO_OUT                   :    out   std_logic_vector(15 downto 0);
    TILE0_DRDY_OUT                 :    out   std_logic;
    TILE0_DWE_IN                   :    in    std_logic;
    --------------------- Shared Ports - Tile and PLL Ports --------------------
    TILE0_CLKIN_IN                 :    in    std_logic;
    TILE0_GTXRESET_IN              :    in    std_logic;
    TILE0_PLLLKDET_OUT             :    out   std_logic;
    TILE0_REFCLKOUT_OUT            :    out   std_logic;
    TILE0_RESETDONE0_OUT           :    out   std_logic;
    TILE0_RESETDONE1_OUT           :    out   std_logic;
    ---------------- Transmit Ports - 8b10b Encoder Control Ports --------------
    TILE0_TXCHARISK0_IN            :    in    std_logic_vector(1 downto 0);
    TILE0_TXCHARISK1_IN            :    in    std_logic_vector(1 downto 0);
    ------------------ Transmit Ports - TX Data Path interface -----------------
    TILE0_TXDATA0_IN               :    in    std_logic_vector(15 downto 0);
    TILE0_TXDATA1_IN               :    in    std_logic_vector(15 downto 0);
    TILE0_TXRESET0_IN              :    in    std_logic;
    TILE0_TXRESET1_IN              :    in    std_logic;
    TILE0_TXUSRCLK0_IN             :    in    std_logic;
    TILE0_TXUSRCLK1_IN             :    in    std_logic;
    TILE0_TXUSRCLK20_IN            :    in    std_logic;
    TILE0_TXUSRCLK21_IN            :    in    std_logic;
    --------------- Transmit Ports - TX Driver and OOB signalling --------------
    TILE0_TXN0_OUT                 :    out   std_logic;
    TILE0_TXN1_OUT                 :    out   std_logic;
    TILE0_TXP0_OUT                 :    out   std_logic;
    TILE0_TXP1_OUT                 :    out   std_logic;
    -------- Transmit Ports - TX Elastic Buffer and Phase Alignment Ports ------
    TILE0_TXENPMAPHASEALIGN0_IN    :    in   std_logic;
    TILE0_TXENPMAPHASEALIGN1_IN    :    in   std_logic;
    TILE0_TXPMASETPHASE0_IN        :    in   std_logic;
    TILE0_TXPMASETPHASE1_IN        :    in   std_logic;
    -------------- Transmit Ports - polarity  ----------------------------------
    TILE0_TXPOLARITY0              :    in   std_logic;
    TILE0_TXPOLARITY1              :    in   std_logic;
    ----------------- Transmit Ports - TX Ports for PCI Express ----------------
    TILE0_TXELECIDLE0_IN           :    in   std_logic;
    TILE0_TXELECIDLE1_IN           :    in   std_logic;


    --_________________________________________________________________________
    --_________________________________________________________________________
    --TILE1  (Location)

    ------------------------ Loopback and Powerdown Ports ----------------------
    TILE1_LOOPBACK0_IN             :    in    std_logic_vector(2 downto 0);
    TILE1_LOOPBACK1_IN             :    in    std_logic_vector(2 downto 0);
    TILE1_RXPOWERDOWN0_IN          :    in    std_logic_vector(1 downto 0);
    TILE1_RXPOWERDOWN1_IN          :    in    std_logic_vector(1 downto 0);
    TILE1_TXPOWERDOWN0_IN          :    in    std_logic_vector(1 downto 0);
    TILE1_TXPOWERDOWN1_IN          :    in    std_logic_vector(1 downto 0);
    ----------------------- Receive Ports - 8b10b Decoder ----------------------
    TILE1_RXCHARISCOMMA0_OUT       :    out   std_logic_vector(1 downto 0);
    TILE1_RXCHARISCOMMA1_OUT       :    out   std_logic_vector(1 downto 0);
    TILE1_RXCHARISK0_OUT           :    out   std_logic_vector(1 downto 0);
    TILE1_RXCHARISK1_OUT           :    out   std_logic_vector(1 downto 0);
    TILE1_RXDISPERR0_OUT           :    out   std_logic_vector(1 downto 0);
    TILE1_RXDISPERR1_OUT           :    out   std_logic_vector(1 downto 0);
    TILE1_RXNOTINTABLE0_OUT        :    out   std_logic_vector(1 downto 0);
    TILE1_RXNOTINTABLE1_OUT        :    out   std_logic_vector(1 downto 0);
    ------------------- Receive Ports - Channel Bonding Ports ------------------
    TILE1_RXCHANBONDSEQ0_OUT       :    out   std_logic;
    TILE1_RXCHANBONDSEQ1_OUT       :    out   std_logic;
    TILE1_RXENCHANSYNC0_IN         :    in    std_logic;
    TILE1_RXENCHANSYNC1_IN         :    in    std_logic;
    ------------------- Receive Ports - Clock Correction Ports -----------------
    TILE1_RXCLKCORCNT0_OUT         :    out   std_logic_vector(2 downto 0);
    TILE1_RXCLKCORCNT1_OUT         :    out   std_logic_vector(2 downto 0);
    --------------- Receive Ports - Comma Detection and Alignment --------------
    TILE1_RXBYTEISALIGNED0_OUT     :    out   std_logic;
    TILE1_RXBYTEISALIGNED1_OUT     :    out   std_logic;
    TILE1_RXBYTEREALIGN0_OUT       :    out   std_logic;
    TILE1_RXBYTEREALIGN1_OUT       :    out   std_logic;
    TILE1_RXCOMMADET0_OUT          :    out   std_logic;
    TILE1_RXCOMMADET1_OUT          :    out   std_logic;
    TILE1_RXENMCOMMAALIGN0_IN      :    in    std_logic;
    TILE1_RXENMCOMMAALIGN1_IN      :    in    std_logic;
    TILE1_RXENPCOMMAALIGN0_IN      :    in    std_logic;
    TILE1_RXENPCOMMAALIGN1_IN      :    in    std_logic;
    ------------------- Receive Ports - RX Data Path interface -----------------
    TILE1_RXDATA0_OUT              :    out   std_logic_vector(15 downto 0);
    TILE1_RXDATA1_OUT              :    out   std_logic_vector(15 downto 0);
    TILE1_RXRESET0_IN              :    in    std_logic;
    TILE1_RXRESET1_IN              :    in    std_logic;
    TILE1_RXUSRCLK0_IN             :    in    std_logic;
    TILE1_RXUSRCLK1_IN             :    in    std_logic;
    TILE1_RXUSRCLK20_IN            :    in    std_logic;
    TILE1_RXUSRCLK21_IN            :    in    std_logic;
    ------- Receive Ports - RX Driver,OOB signalling,Coupling and Eq.,CDR ------
    TILE1_RXCDRRESET0_IN           :    in    std_logic;
    TILE1_RXCDRRESET1_IN           :    in    std_logic;
    TILE1_RXELECIDLE0_OUT          :    out   std_logic;
    TILE1_RXELECIDLE1_OUT          :    out   std_logic;
    TILE1_RXN0_IN                  :    in    std_logic;
    TILE1_RXN1_IN                  :    in    std_logic;
    TILE1_RXP0_IN                  :    in    std_logic;
    TILE1_RXP1_IN                  :    in    std_logic;
    -------- Receive Ports - RX Elastic Buffer and Phase Alignment Ports -------
    TILE1_RXBUFRESET0_IN           :    in    std_logic;
    TILE1_RXBUFRESET1_IN           :    in    std_logic;
    TILE1_RXBUFSTATUS0_OUT         :    out   std_logic_vector(2 downto 0);
    TILE1_RXBUFSTATUS1_OUT         :    out   std_logic_vector(2 downto 0);
    TILE1_RXCHANISALIGNED0_OUT     :    out   std_logic;
    TILE1_RXCHANISALIGNED1_OUT     :    out   std_logic;
    TILE1_RXCHANREALIGN0_OUT       :    out   std_logic;
    TILE1_RXCHANREALIGN1_OUT       :    out   std_logic;
    --------------- Receive Ports - RX Loss-of-sync State Machine --------------
    TILE1_RXLOSSOFSYNC0_OUT        :    out   std_logic_vector(1 downto 0);
    TILE1_RXLOSSOFSYNC1_OUT        :    out   std_logic_vector(1 downto 0);
    -------------- Receive Ports - polarity  -----------------------------------
    TILE1_RXPOLARITY0              :    in   std_logic;
    TILE1_RXPOLARITY1              :    in   std_logic;
    ------------- Shared Ports - Dynamic Reconfiguration Port (DRP) ------------
    TILE1_DADDR_IN                 :    in    std_logic_vector(6 downto 0);
    TILE1_DCLK_IN                  :    in    std_logic;
    TILE1_DEN_IN                   :    in    std_logic;
    TILE1_DI_IN                    :    in    std_logic_vector(15 downto 0);
    TILE1_DO_OUT                   :    out   std_logic_vector(15 downto 0);
    TILE1_DRDY_OUT                 :    out   std_logic;
    TILE1_DWE_IN                   :    in    std_logic;
    --------------------- Shared Ports - Tile and PLL Ports --------------------
    TILE1_CLKIN_IN                 :    in    std_logic;
    TILE1_GTXRESET_IN              :    in    std_logic;
    TILE1_PLLLKDET_OUT             :    out   std_logic;
    TILE1_REFCLKOUT_OUT            :    out   std_logic;
    TILE1_RESETDONE0_OUT           :    out   std_logic;
    TILE1_RESETDONE1_OUT           :    out   std_logic;
    ---------------- Transmit Ports - 8b10b Encoder Control Ports --------------
    TILE1_TXCHARISK0_IN            :    in    std_logic_vector(1 downto 0);
    TILE1_TXCHARISK1_IN            :    in    std_logic_vector(1 downto 0);
    ------------------ Transmit Ports - TX Data Path interface -----------------
    TILE1_TXDATA0_IN               :    in    std_logic_vector(15 downto 0);
    TILE1_TXDATA1_IN               :    in    std_logic_vector(15 downto 0);
    TILE1_TXRESET0_IN              :    in    std_logic;
    TILE1_TXRESET1_IN              :    in    std_logic;
    TILE1_TXUSRCLK0_IN             :    in    std_logic;
    TILE1_TXUSRCLK1_IN             :    in    std_logic;
    TILE1_TXUSRCLK20_IN            :    in    std_logic;
    TILE1_TXUSRCLK21_IN            :    in    std_logic;
    --------------- Transmit Ports - TX Driver and OOB signalling --------------
    TILE1_TXN0_OUT                 :    out   std_logic;
    TILE1_TXN1_OUT                 :    out   std_logic;
    TILE1_TXP0_OUT                 :    out   std_logic;
    TILE1_TXP1_OUT                 :    out   std_logic;
    -------- Transmit Ports - TX Elastic Buffer and Phase Alignment Ports ------
    TILE1_TXENPMAPHASEALIGN0_IN    :    in   std_logic;
    TILE1_TXENPMAPHASEALIGN1_IN    :    in   std_logic;
    TILE1_TXPMASETPHASE0_IN        :    in   std_logic;
    TILE1_TXPMASETPHASE1_IN        :    in   std_logic;
    -------------- Transmit Ports - polarity  ----------------------------------
    TILE1_TXPOLARITY0              :    in   std_logic;
    TILE1_TXPOLARITY1              :    in   std_logic;
    ----------------- Transmit Ports - TX Ports for PCI Express ----------------
    TILE1_TXELECIDLE0_IN           :    in   std_logic;
    TILE1_TXELECIDLE1_IN           :    in   std_logic
);
end component;

component TX_SYNC is
generic
(
    PLL_DIVSEL_OUT    : integer := 1;
    CH_SWAP           : boolean := false
);
port
(
   -- User DRP Interface
    USER_DO             : out std_logic_vector(16-1 downto 0);
    USER_DI             : in  std_logic_vector(16-1 downto 0);
    USER_DADDR          : in  std_logic_vector(7-1 downto 0);
    USER_DEN            : in  std_logic;
    USER_DWE            : in  std_logic;
    USER_DRDY           : out std_logic;

    -- GT DRP Interface
    GT_DO               : out std_logic_vector(16-1 downto 0);  -- connects to DI of GTX_DUAL
    GT_DI               : in  std_logic_vector(16-1 downto 0);  -- connects to DO of GTX_DUAL
    GT_DADDR            : out std_logic_vector(7-1 downto 0);
    GT_DEN              : out std_logic;
    GT_DWE              : out std_logic;
    GT_DRDY             : in  std_logic;

    -- Clocks and Reset
    USER_CLK            : in  std_logic;
    DCLK                : in  std_logic;
    RESET               : in  std_logic;
    RESETDONE           : in  std_logic;

    -- GT side MGT Pass through Signals
    TXENPMAPHASEALIGN   : out std_logic;
    TXPMASETPHASE       : out std_logic;
    TXRESET             : out std_logic;

    -- Sync operations
    SYNC_DONE           : out std_logic;
    RESTART_SYNC        : in  std_logic
);
end component;


  component chanbond_monitor is
  port
  (
    CLK                     :  in  std_logic;
    RST                     :  in  std_logic;
    COMMA_ALIGN_DONE        :  in  std_logic;
    CORE_ENCHANSYNC         :  in  std_logic;
    CHANBOND_DONE           :  in  std_logic;
    RXRESET                 :  out std_logic
  );
  end component;

----------------------------------------------------------------------------
-- Signal declarations.
---------------------------------------------------------------------------
  signal clk156_reset_txsync_r1 : std_logic;
  signal clk156_reset_txsync_r2 : std_logic;
  signal clk156_reset_txsync_r3 : std_logic;
  signal GT_TXOUTCLK1       : std_logic;
  signal mgt_txdata         : std_logic_vector(63 downto 0);
  signal mgt_txcharisk      : std_logic_vector(7 downto 0);
  signal mgt_rxdata         : std_logic_vector(63 downto 0);
  signal mgt_rxcharisk      : std_logic_vector(7 downto 0);
  signal mgt_enable_align   : std_logic_vector(3 downto 0);
  signal mgt_enchansync     : std_logic;
  signal mgt_syncok         : std_logic_vector(3 downto 0);
  signal mgt_rxdisperr      : std_logic_vector(7 downto 0);
  signal mgt_rxnotintable   : std_logic_vector(7 downto 0);
  signal mgt_reset_terms    : std_logic;
  signal mgt_codevalid      : std_logic_vector(7 downto 0);
  signal mgt_rxchariscomma  : std_logic_vector(7 downto 0);
  signal mgt_rxdata_reg       : std_logic_vector(63 downto 0);
  signal mgt_rxcharisk_reg    : std_logic_vector(7 downto 0);
  signal mgt_rxelecidle       : std_logic_vector(3 downto 0);
  signal mgt_rxelecidle_i     : std_logic_vector(3 downto 0);
  signal mgt_rxlock_reg       : std_logic_vector(3 downto 0);
  signal mgt_rxlock_r1        : std_logic_vector(3 downto 0);
  signal mgt_rxnotintable_reg : std_logic_vector(7 downto 0);
  signal mgt_rxdisperr_reg    : std_logic_vector(7 downto 0);
  signal mgt_codecomma_reg    : std_logic_vector(7 downto 0);
  signal mgt_rxcdr_reset     : std_logic_vector(3 downto 0) := "0000";
  signal mgt_rx_reset        : std_logic;
  signal mgt_rxlock          : std_logic_vector(3 downto 0);
  signal mgt_tx_fault        : std_logic_vector(3 downto 0);
  signal mgt_loopback       : std_logic;
  signal mgt_powerdown      : std_logic;
  signal mgt_powerdown_2    : std_logic_vector(1 downto 0);
  signal mgt_powerdown_r    : std_logic;
  signal mgt_powerdown_falling : std_logic;
  signal mgt_plllocked      : std_logic_vector(1 downto 0);
  signal mgt_resetdone      : std_logic_vector(3 downto 0);
  signal mgt_rxbuferr       : std_logic_vector(3 downto 0);
  signal mgt_rxbuferr_reg   : std_logic;
  signal mgt_rxbufstatus    : std_logic_vector(11 downto 0);
  signal mgt_rxlossofsync   : std_logic_vector(7 downto 0);
  signal loopback_int       : std_logic_vector(2 downto 0);
  signal lock               : std_logic;
  signal reset_txsync       : std_logic;

  --CHANBOND_MONITOR signals
  signal mgt_rxchanisaligned : std_logic_vector(3 downto 0);
  signal comma_align_done    : std_logic;
  signal chanbond_done       : std_logic;
  signal sync_status_i       : std_logic_vector(3 downto 0);
  signal align_status_i      : std_logic;

  signal gt_do                 : std_logic_vector(31 downto 0);
  signal gt_di                 : std_logic_vector(31 downto 0);
  signal gt_daddr              : std_logic_vector(13 downto 0);
  signal gt_den                : std_logic_vector(1 downto 0);
  signal gt_dwe                : std_logic_vector(1 downto 0);
  signal gt_drdy               : std_logic_vector(1 downto 0);
  signal mgt_txenpmaphasealign : std_logic_vector(1 downto 0);
  signal mgt_txpmasetphase     : std_logic_vector(1 downto 0);
  signal mgt_txreset           : std_logic_vector(1 downto 0);
  signal resetdone             : std_logic_vector(1 downto 0);
  signal sync_txreset          : std_logic_vector(1 downto 0);
  signal tx_sync_done          : std_logic_vector(1 downto 0);
  --ASYNC_REG attributes
  attribute ASYNC_REG : string;
  attribute ASYNC_REG of clk156_reset_txsync_r1  : signal is "TRUE";
  attribute ASYNC_REG of mgt_rxlock_r1           : signal is "TRUE";
----------------------------------------------------------------------------
-- Function declarations.
---------------------------------------------------------------------------
function IsBufError (bufStatus:std_logic_vector(2 downto 0)) return std_logic is
  variable result : std_logic;
begin
  if bufStatus = "101" or bufStatus = "110" then
    result := '1';
  else
    result := '0';
  end if;
  return result;
end;

begin

  xaui_core : xaui_gtx
    port map (
      reset            => reset156,
      xgmii_txd        => xgmii_txd,
      xgmii_txc        => xgmii_txc,
      xgmii_rxd        => xgmii_rxd,
      xgmii_rxc        => xgmii_rxc,
      usrclk           => clk156,
      mgt_txdata       => mgt_txdata,
      mgt_txcharisk    => mgt_txcharisk,
      mgt_rxdata       => mgt_rxdata_reg,
      mgt_rxcharisk    => mgt_rxcharisk_reg,
      mgt_codevalid    => mgt_codevalid,
      mgt_codecomma    => mgt_codecomma_reg,
      mgt_enable_align => mgt_enable_align,
      mgt_enchansync   => mgt_enchansync,
      mgt_syncok       => mgt_syncok,
      mgt_rxlock       => mgt_rxlock_reg,
      mgt_loopback     => mgt_loopback,
      mgt_powerdown    => mgt_powerdown,
      mgt_tx_reset     => mgt_tx_fault,
      mgt_rx_reset     => mgt_rxcdr_reset,
      signal_detect    => signal_detect,
      align_status     => align_status_i,
      sync_status      => sync_status_i,
      configuration_vector => configuration_vector,
      status_vector        => status_vector);

  ----------------------------------------------------------------------
   -- Transceiver instances
   rocketio_wrapper_i : ROCKETIO_WRAPPER
    generic map (
      CH01_SWAP                    => CH01_SWAP,
      CH23_SWAP                    => CH23_SWAP,
      WRAPPER_SIM_MODE             => WRAPPER_SIM_MODE,
      WRAPPER_SIM_GTXRESET_SPEEDUP => WRAPPER_SIM_GTXRESET_SPEEDUP
    )
    port map (
    --_________________________________________________________________________
    --_________________________________________________________________________
    --TILE0  (Location)

    ------------------------ Loopback and Powerdown Ports ----------------------
    TILE0_LOOPBACK0_IN             => loopback_int,
    TILE0_LOOPBACK1_IN             => loopback_int,
    TILE0_RXPOWERDOWN0_IN          => mgt_powerdown_2,
    TILE0_RXPOWERDOWN1_IN          => mgt_powerdown_2,
    TILE0_TXPOWERDOWN0_IN          => mgt_powerdown_2,
    TILE0_TXPOWERDOWN1_IN          => mgt_powerdown_2,
    ----------------------- Receive Ports - 8b10b Decoder ----------------------
    TILE0_RXDISPERR0_OUT           => mgt_rxdisperr(1 downto 0),
    TILE0_RXDISPERR1_OUT           => mgt_rxdisperr(3 downto 2),
    TILE0_RXNOTINTABLE0_OUT        => mgt_rxnotintable(1 downto 0),
    TILE0_RXNOTINTABLE1_OUT        => mgt_rxnotintable(3 downto 2),
    TILE0_RXCHARISCOMMA0_OUT       => mgt_rxchariscomma(1 downto 0),
    TILE0_RXCHARISCOMMA1_OUT       => mgt_rxchariscomma(3 downto 2),
    TILE0_RXCHARISK0_OUT           => mgt_rxcharisk(1 downto 0),
    TILE0_RXCHARISK1_OUT           => mgt_rxcharisk(3 downto 2),
    ------------------- Receive Ports - Channel Bonding Ports ------------------
    TILE0_RXCHANBONDSEQ0_OUT       => open,
    TILE0_RXCHANBONDSEQ1_OUT       => open,
    TILE0_RXENCHANSYNC0_IN         => mgt_enchansync,
    TILE0_RXENCHANSYNC1_IN         => mgt_enchansync,
    ------------------- Receive Ports - Clock Correction Ports -----------------
    TILE0_RXCLKCORCNT0_OUT         => open,
    TILE0_RXCLKCORCNT1_OUT         => open,
    --------------- Receive Ports - Comma Detection and Alignment --------------
    TILE0_RXBYTEISALIGNED0_OUT     => open,
    TILE0_RXBYTEISALIGNED1_OUT     => open,
    TILE0_RXBYTEREALIGN0_OUT       => open,
    TILE0_RXBYTEREALIGN1_OUT       => open,
    TILE0_RXCOMMADET0_OUT          => open,
    TILE0_RXCOMMADET1_OUT          => open,
    TILE0_RXENMCOMMAALIGN0_IN      => mgt_enable_align(0),
    TILE0_RXENMCOMMAALIGN1_IN      => mgt_enable_align(1),
    TILE0_RXENPCOMMAALIGN0_IN      => mgt_enable_align(0),
    TILE0_RXENPCOMMAALIGN1_IN      => mgt_enable_align(1),
    ------------------- Receive Ports - RX Data Path interface -----------------
    TILE0_RXDATA0_OUT              => mgt_rxdata(15 downto 0),
    TILE0_RXDATA1_OUT              => mgt_rxdata(31 downto 16),
    TILE0_RXRESET0_IN              => mgt_rx_reset,
    TILE0_RXRESET1_IN              => mgt_rx_reset,
    TILE0_RXUSRCLK0_IN             => clk156,
    TILE0_RXUSRCLK1_IN             => clk156,
    TILE0_RXUSRCLK20_IN            => clk156,
    TILE0_RXUSRCLK21_IN            => clk156,
    ------- Receive Ports - RX Driver,OOB signalling,Coupling and Eq.,CDR ------
    TILE0_RXCDRRESET0_IN           => mgt_rxcdr_reset(0),
    TILE0_RXCDRRESET1_IN           => mgt_rxcdr_reset(1),
    TILE0_RXELECIDLE0_OUT          => mgt_rxelecidle(0),
    TILE0_RXELECIDLE1_OUT          => mgt_rxelecidle(1),
    TILE0_RXN0_IN                  => xaui_rx_l0_n,
    TILE0_RXN1_IN                  => xaui_rx_l1_n,
    TILE0_RXP0_IN                  => xaui_rx_l0_p,
    TILE0_RXP1_IN                  => xaui_rx_l1_p,
    -------- Receive Ports - RX Elastic Buffer and Phase Alignment Ports -------
    TILE0_RXBUFRESET0_IN           => '0',
    TILE0_RXBUFRESET1_IN           => '0',
    TILE0_RXBUFSTATUS0_OUT         => mgt_rxbufstatus(2 downto 0),
    TILE0_RXBUFSTATUS1_OUT         => mgt_rxbufstatus(5 downto 3),
    TILE0_RXCHANISALIGNED0_OUT     => mgt_rxchanisaligned(0),
    TILE0_RXCHANISALIGNED1_OUT     => mgt_rxchanisaligned(1),
    TILE0_RXCHANREALIGN0_OUT       => open,
    TILE0_RXCHANREALIGN1_OUT       => open,
    --------------- Receive Ports - RX Loss-of-sync State Machine --------------
    TILE0_RXLOSSOFSYNC0_OUT        => mgt_rxlossofsync(1 downto 0),
    TILE0_RXLOSSOFSYNC1_OUT        => mgt_rxlossofsync(3 downto 2),
    -------------- Receive Ports - polarity  -----------------------------------
    TILE0_RXPOLARITY0              => rxpolarity(0),
    TILE0_RXPOLARITY1              => rxpolarity(1),
    ------------- Shared Ports - Dynamic Reconfiguration Port (DRP) ------------
    TILE0_DADDR_IN                 => gt_daddr(6 downto 0),
    TILE0_DCLK_IN                  => dclk,
    TILE0_DEN_IN                   => gt_den(0),
    TILE0_DI_IN                    => gt_di(15 downto 0),
    TILE0_DO_OUT                   => gt_do(15 downto 0),
    TILE0_DRDY_OUT                 => gt_drdy(0),
    TILE0_DWE_IN                   => gt_dwe(0),
    --------------------- Shared Ports - Tile and PLL Ports --------------------
    TILE0_CLKIN_IN                 => refclk,
    TILE0_GTXRESET_IN              => mgt_reset_terms,
    TILE0_PLLLKDET_OUT             => mgt_plllocked(0),
    TILE0_REFCLKOUT_OUT            => GT_TXOUTCLK1,
    TILE0_RESETDONE0_OUT           => mgt_resetdone(0),
    TILE0_RESETDONE1_OUT           => mgt_resetdone(1),
    ---------------- Transmit Ports - 8b10b Encoder Control Ports --------------
    TILE0_TXCHARISK0_IN            => mgt_txcharisk(1 downto 0),
    TILE0_TXCHARISK1_IN            => mgt_txcharisk(3 downto 2),
    ------------------ Transmit Ports - TX Data Path interface -----------------
    TILE0_TXDATA0_IN               => mgt_txdata(15 downto 0),
    TILE0_TXDATA1_IN               => mgt_txdata(31 downto 16),
    TILE0_TXRESET0_IN              => mgt_txreset(0),
    TILE0_TXRESET1_IN              => mgt_txreset(0),
    TILE0_TXUSRCLK0_IN             => clk156,
    TILE0_TXUSRCLK1_IN             => clk156,
    TILE0_TXUSRCLK20_IN            => clk156,
    TILE0_TXUSRCLK21_IN            => clk156,
    --------------- Transmit Ports - TX Driver and OOB signalling --------------
    TILE0_TXN0_OUT                 => xaui_tx_l0_n,
    TILE0_TXN1_OUT                 => xaui_tx_l1_n,
    TILE0_TXP0_OUT                 => xaui_tx_l0_p,
    TILE0_TXP1_OUT                 => xaui_tx_l1_p,
    -------- Transmit Ports - TX Elastic Buffer and Phase Alignment Ports ------
    TILE0_TXENPMAPHASEALIGN0_IN    => mgt_txenpmaphasealign(0),
    TILE0_TXENPMAPHASEALIGN1_IN    => mgt_txenpmaphasealign(0),
    TILE0_TXPMASETPHASE0_IN        => mgt_txpmasetphase(0),
    TILE0_TXPMASETPHASE1_IN        => mgt_txpmasetphase(0),
    -------------- Transmit Ports - polarity  ----------------------------------
    TILE0_TXPOLARITY0              => txpolarity(0),
    TILE0_TXPOLARITY1              => txpolarity(1),
    ----------------- Transmit Ports - TX Ports for PCI Express ----------------
    TILE0_TXELECIDLE0_IN           => mgt_powerdown,
    TILE0_TXELECIDLE1_IN           => mgt_powerdown,

    --_________________________________________________________________________
    --_________________________________________________________________________
    --TILE1  (Location)

    ------------------------ Loopback and Powerdown Ports ----------------------
    TILE1_LOOPBACK0_IN             => loopback_int,
    TILE1_LOOPBACK1_IN             => loopback_int,
    TILE1_RXPOWERDOWN0_IN          => mgt_powerdown_2,
    TILE1_RXPOWERDOWN1_IN          => mgt_powerdown_2,
    TILE1_TXPOWERDOWN0_IN          => mgt_powerdown_2,
    TILE1_TXPOWERDOWN1_IN          => mgt_powerdown_2,
    ----------------------- Receive Ports - 8b10b Decoder ----------------------
    TILE1_RXDISPERR0_OUT           => mgt_rxdisperr(5 downto 4),
    TILE1_RXDISPERR1_OUT           => mgt_rxdisperr(7 downto 6),
    TILE1_RXNOTINTABLE0_OUT        => mgt_rxnotintable(5 downto 4),
    TILE1_RXNOTINTABLE1_OUT        => mgt_rxnotintable(7 downto 6),
    TILE1_RXCHARISCOMMA0_OUT       => mgt_rxchariscomma(5 downto 4),
    TILE1_RXCHARISCOMMA1_OUT       => mgt_rxchariscomma(7 downto 6),
    TILE1_RXCHARISK0_OUT           => mgt_rxcharisk(5 downto 4),
    TILE1_RXCHARISK1_OUT           => mgt_rxcharisk(7 downto 6),
    ------------------- Receive Ports - Channel Bonding Ports ------------------
    TILE1_RXCHANBONDSEQ0_OUT       => open,
    TILE1_RXCHANBONDSEQ1_OUT       => open,
    TILE1_RXENCHANSYNC0_IN         => mgt_enchansync,
    TILE1_RXENCHANSYNC1_IN         => mgt_enchansync,
    ------------------- Receive Ports - Clock Correction Ports -----------------
    TILE1_RXCLKCORCNT0_OUT         => open,
    TILE1_RXCLKCORCNT1_OUT         => open,
    --------------- Receive Ports - Comma Detection and Alignment --------------
    TILE1_RXBYTEISALIGNED0_OUT     => open,
    TILE1_RXBYTEISALIGNED1_OUT     => open,
    TILE1_RXBYTEREALIGN0_OUT       => open,
    TILE1_RXBYTEREALIGN1_OUT       => open,
    TILE1_RXCOMMADET0_OUT          => open,
    TILE1_RXCOMMADET1_OUT          => open,
    TILE1_RXENMCOMMAALIGN0_IN      => mgt_enable_align(2),
    TILE1_RXENMCOMMAALIGN1_IN      => mgt_enable_align(3),
    TILE1_RXENPCOMMAALIGN0_IN      => mgt_enable_align(2),
    TILE1_RXENPCOMMAALIGN1_IN      => mgt_enable_align(3),
    ------------------- Receive Ports - RX Data Path interface -----------------
    TILE1_RXDATA0_OUT              => mgt_rxdata(47 downto 32),
    TILE1_RXDATA1_OUT              => mgt_rxdata(63 downto 48),
    TILE1_RXRESET0_IN              => mgt_rx_reset,
    TILE1_RXRESET1_IN              => mgt_rx_reset,
    TILE1_RXUSRCLK0_IN             => clk156,
    TILE1_RXUSRCLK1_IN             => clk156,
    TILE1_RXUSRCLK20_IN            => clk156,
    TILE1_RXUSRCLK21_IN            => clk156,
    ------- Receive Ports - RX Driver,OOB signalling,Coupling and Eq.,CDR ------
    TILE1_RXCDRRESET0_IN           => mgt_rxcdr_reset(2),
    TILE1_RXCDRRESET1_IN           => mgt_rxcdr_reset(3),
    TILE1_RXELECIDLE0_OUT          => mgt_rxelecidle(2),
    TILE1_RXELECIDLE1_OUT          => mgt_rxelecidle(3),
    TILE1_RXN0_IN                  => xaui_rx_l2_n,
    TILE1_RXN1_IN                  => xaui_rx_l3_n,
    TILE1_RXP0_IN                  => xaui_rx_l2_p,
    TILE1_RXP1_IN                  => xaui_rx_l3_p,
    -------- Receive Ports - RX Elastic Buffer and Phase Alignment Ports -------
    TILE1_RXBUFRESET0_IN           => '0',
    TILE1_RXBUFRESET1_IN           => '0',
    TILE1_RXBUFSTATUS0_OUT         => mgt_rxbufstatus(8 downto 6),
    TILE1_RXBUFSTATUS1_OUT         => mgt_rxbufstatus(11 downto 9),
    TILE1_RXCHANISALIGNED0_OUT     => mgt_rxchanisaligned(2),
    TILE1_RXCHANISALIGNED1_OUT     => mgt_rxchanisaligned(3),
    TILE1_RXCHANREALIGN0_OUT       => open,
    TILE1_RXCHANREALIGN1_OUT       => open,
    --------------- Receive Ports - RX Loss-of-sync State Machine --------------
    TILE1_RXLOSSOFSYNC0_OUT        => mgt_rxlossofsync(5 downto 4),
    TILE1_RXLOSSOFSYNC1_OUT        => mgt_rxlossofsync(7 downto 6),
    -------------- Receive Ports - polarity  -----------------------------------
    TILE1_RXPOLARITY0              => rxpolarity(2),
    TILE1_RXPOLARITY1              => rxpolarity(3),
    ------------- Shared Ports - Dynamic Reconfiguration Port (DRP) ------------
    TILE1_DADDR_IN                 => gt_daddr(13 downto 7),
    TILE1_DCLK_IN                  => dclk,
    TILE1_DEN_IN                   => gt_den(1),
    TILE1_DI_IN                    => gt_di(31 downto 16),
    TILE1_DO_OUT                   => gt_do(31 downto 16),
    TILE1_DRDY_OUT                 => gt_drdy(1),
    TILE1_DWE_IN                   => gt_dwe(1),
    --------------------- Shared Ports - Tile and PLL Ports --------------------
    TILE1_CLKIN_IN                 => refclk,
    TILE1_GTXRESET_IN              => mgt_reset_terms,
    TILE1_PLLLKDET_OUT             => mgt_plllocked(1),
    TILE1_REFCLKOUT_OUT            => open,
    TILE1_RESETDONE0_OUT           => mgt_resetdone(2),
    TILE1_RESETDONE1_OUT           => mgt_resetdone(3),
    ---------------- Transmit Ports - 8b10b Encoder Control Ports --------------
    TILE1_TXCHARISK0_IN            => mgt_txcharisk(5 downto 4),
    TILE1_TXCHARISK1_IN            => mgt_txcharisk(7 downto 6),
    ------------------ Transmit Ports - TX Data Path interface -----------------
    TILE1_TXDATA0_IN               => mgt_txdata(47 downto 32),
    TILE1_TXDATA1_IN               => mgt_txdata(63 downto 48),
    TILE1_TXRESET0_IN              => mgt_txreset(1),
    TILE1_TXRESET1_IN              => mgt_txreset(1),
    TILE1_TXUSRCLK0_IN             => clk156,
    TILE1_TXUSRCLK1_IN             => clk156,
    TILE1_TXUSRCLK20_IN            => clk156,
    TILE1_TXUSRCLK21_IN            => clk156,
    --------------- Transmit Ports - TX Driver and OOB signalling --------------
    TILE1_TXN0_OUT                 => xaui_tx_l2_n,
    TILE1_TXN1_OUT                 => xaui_tx_l3_n,
    TILE1_TXP0_OUT                 => xaui_tx_l2_p,
    TILE1_TXP1_OUT                 => xaui_tx_l3_p,
    -------- Transmit Ports - TX Elastic Buffer and Phase Alignment Ports ------
    TILE1_TXENPMAPHASEALIGN0_IN    => mgt_txenpmaphasealign(1),
    TILE1_TXENPMAPHASEALIGN1_IN    => mgt_txenpmaphasealign(1),
    TILE1_TXPMASETPHASE0_IN        => mgt_txpmasetphase(1),
    TILE1_TXPMASETPHASE1_IN        => mgt_txpmasetphase(1),
    -------------- Transmit Ports - polarity  ----------------------------------
    TILE1_TXPOLARITY0              => txpolarity(2),
    TILE1_TXPOLARITY1              => txpolarity(3),
    ----------------- Transmit Ports - TX Ports for PCI Express ----------------
    TILE1_TXELECIDLE0_IN           => mgt_powerdown,
    TILE1_TXELECIDLE1_IN           => mgt_powerdown
  );

  mgt_syncok <= not (mgt_rxlossofsync(7) & mgt_rxlossofsync(5) & mgt_rxlossofsync(3) & mgt_rxlossofsync(1));
  mgt_powerdown_2 <= mgt_powerdown & mgt_powerdown;

  -- Detect falling edge of mgt_powerdown
  p_powerdown_r : process(clk156)
  begin
    if rising_edge(clk156) then
      mgt_powerdown_r <= mgt_powerdown;
    end if;
  end process;

  p_powerdown_falling : process(clk156)
  begin
    if rising_edge(clk156) then
      if mgt_powerdown_r = '1' and mgt_powerdown = '0' then
        mgt_powerdown_falling <= '1';
      else
        mgt_powerdown_falling <= '0';
      end if;
    end if;
  end process;

  mgt_codevalid <= not (mgt_rxnotintable_reg or mgt_rxdisperr_reg);
  loopback_int  <= "010" when mgt_loopback = '1'
                  else "000";

  RXBUFERR_P: process (mgt_rxbufstatus)
  begin
    for i in 0 to 3 loop
      mgt_rxbuferr(i) <= IsBufError(mgt_rxbufstatus(i*3+2 downto i*3));
    end loop;
  end process;

  txoutclk <= GT_TXOUTCLK1;

  reset_txsync <= mgt_reset_terms or (not lock);

  p_reset_txsync_sync : process(clk156, reset_txsync)
  begin
    if (reset_txsync = '1') then
      clk156_reset_txsync_r1 <= '1';
      clk156_reset_txsync_r2 <= '1';
      clk156_reset_txsync_r3 <= '1';
    elsif rising_edge(clk156) then
      if ( resetdone = "11" ) then
        clk156_reset_txsync_r1 <= '0';
        clk156_reset_txsync_r2 <= clk156_reset_txsync_r1;
        clk156_reset_txsync_r3 <= clk156_reset_txsync_r2;
      end if;
    end if;
  end process;

  -- reset logic
  lock       <= mgt_plllocked(0) and mgt_plllocked(1);
  txlock     <= lock;
  mgt_rxlock <= mgt_plllocked(1) & mgt_plllocked(1) & mgt_plllocked(0) & mgt_plllocked(0);

  mgt_txreset(0) <= '1' when sync_txreset(0) = '1' else
                    '1' when lock = '0' else
                    '0';

  mgt_txreset(1) <= '1' when sync_txreset(1) = '1' else
                    '1' when lock = '0' else
                    '0';

  resetdone(0)  <= '1' when mgt_resetdone(1 downto 0) = "11" else '0';
  resetdone(1)  <= '1' when mgt_resetdone(3 downto 2) = "11" else '0';

  tile0_tx_sync_i :  TX_SYNC
    generic map (
        PLL_DIVSEL_OUT   => 1,
        CH_SWAP          => CH01_SWAP
    )
    port map (
      -- User DRP Interface
      USER_DO           => drp_o(15 downto 0),
      USER_DI           => drp_i,
      USER_DADDR        => drp_addr,
      USER_DEN          => drp_en(0),
      USER_DWE          => drp_we(0),
      USER_DRDY         => drp_rdy(0),
      -- GT DRP Interface
      GT_DO             => gt_di(15 downto 0),
      GT_DI             => gt_do(15 downto 0),
      GT_DADDR          => gt_daddr(6 downto 0),
      GT_DEN            => gt_den(0),
      GT_DWE            => gt_dwe(0),
      GT_DRDY           => gt_drdy(0),
      -- Clocks and Reset
      USER_CLK          => clk156,
      DCLK              => dclk,
      RESET             => clk156_reset_txsync_r3,
      RESETDONE         => resetdone(0),
      -- Phase Alignment ports to GT
      TXENPMAPHASEALIGN => mgt_txenpmaphasealign(0),
      TXPMASETPHASE     => mgt_txpmasetphase(0),
      TXRESET           => sync_txreset(0),
      -- SYNC operations
      SYNC_DONE         => tx_sync_done(0),
      RESTART_SYNC      => '0'
      );

  tile1_tx_sync_i :  TX_SYNC
    generic map (
        PLL_DIVSEL_OUT   => 1,
        CH_SWAP          => CH23_SWAP
    )
    port map (
      -- User DRP Interface
      USER_DO           => drp_o(31 downto 16),
      USER_DI           => drp_i,
      USER_DADDR        => drp_addr,
      USER_DEN          => drp_en(1),
      USER_DWE          => drp_we(1),
      USER_DRDY         => drp_rdy(1),
      -- GT DRP Interface
      GT_DO             => gt_di(31 downto 16),
      GT_DI             => gt_do(31 downto 16),
      GT_DADDR          => gt_daddr(13 downto 7),
      GT_DEN            => gt_den(1),
      GT_DWE            => gt_dwe(1),
      GT_DRDY           => gt_drdy(1),
      -- Clocks and Reset
      USER_CLK          => clk156,
      DCLK              => dclk,
      RESET             => clk156_reset_txsync_r3,
      RESETDONE         => resetdone(1),
      -- Phase Alignment ports to GT
      TXENPMAPHASEALIGN => mgt_txenpmaphasealign(1),
      TXPMASETPHASE     => mgt_txpmasetphase(1),
      TXRESET           => sync_txreset(1),
      -- SYNC operations
      SYNC_DONE         => tx_sync_done(1),
      RESTART_SYNC      => '0'
      );

      mgt_tx_ready <= '1' when tx_sync_done = "11" else '0';
      mgt_tx_fault(3 downto 2) <= "11" when tx_sync_done(1) = '0' else "00";
      mgt_tx_fault(1 downto 0) <= "11" when tx_sync_done(0) = '0' else "00";

  mgt_reset_terms <= reset;

  -- reset the rx side when the buffer overflows / underflows or on a falling
  -- edge of powerdown
  process (clk156)
  begin
    if rising_edge(clk156) then
      if mgt_rxbuferr /= "0000" or mgt_powerdown_falling = '1' then
        mgt_rxcdr_reset <= "1111";
      else
        mgt_rxcdr_reset <= "0000";
      end if;
    end if;
  end process;

  -- disable electrical idle when in loopback
  mgt_rxelecidle_i <= "0000" when mgt_loopback = '1' else mgt_rxelecidle;

  p_mgt_reg : process(clk156)
  begin
    if rising_edge(clk156) then
        mgt_rxlock_reg       <= mgt_rxlock_r1;
        mgt_rxlock_r1        <= mgt_rxlock and (not mgt_rxelecidle_i) ;
        mgt_rxdata_reg       <= mgt_rxdata;
        mgt_rxcharisk_reg    <= mgt_rxcharisk;
        mgt_rxnotintable_reg <= mgt_rxnotintable;
        mgt_rxdisperr_reg    <= mgt_rxdisperr;
        mgt_codecomma_reg    <= mgt_rxchariscomma;
    end if;
  end process p_mgt_reg;

  sync_status      <= sync_status_i;
  align_status     <= align_status_i;
  comma_align_done <= '1' when sync_status_i = "1111" else '0';
  chanbond_done    <= '1' when mgt_rxchanisaligned = "1111" else '0';

  chanbond_monitor_i : chanbond_monitor
  port map (
    CLK                 => clk156,
    RST                 => reset156,
    COMMA_ALIGN_DONE    => comma_align_done,
    CORE_ENCHANSYNC     => mgt_enchansync,
    CHANBOND_DONE       => chanbond_done,
    RXRESET             => mgt_rx_reset
  );


end wrapper;
