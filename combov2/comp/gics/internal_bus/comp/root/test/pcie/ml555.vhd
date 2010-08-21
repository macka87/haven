--
-- ml555.vhd: ML555 entity file
-- Copyright (C) 2007 CESNET
-- Author(s): Viktor Pus 
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

library ieee;
use ieee.std_logic_1164.all;

entity ML555 is
   port(

-- ##       Clock pins
-- ##    PCI/GTP connectivity for LX50T-FF1136 (9/18 revision:)
-- ##        PCIe lanes 0 & 1 connect to GTP X0Y2
-- ##        PCIe lanes 2 & 3 connect to GTP X0Y1
-- ##        PCIe lanes 4 & 5 connect to GTP X0Y3
-- ##        PCIe lanes 6 & 7 connect to GTP X0Y0
-- ###################################################
      PCIE_RCLKP      : in std_logic;
      PCIE_RCLKN      : in std_logic;
      MGT_X0Y1_REFCLKP: inout std_logic;
      MGT_X0Y1_REFCLKN: inout std_logic;
      MGT_X0Y0_REFCLKP: inout std_logic;
      MGT_X0Y0_REFCLKN: inout std_logic;
      SMA_GTPCLK_P    : inout std_logic;
      SMA_GTPCLK_N    : inout std_logic;
      SFP_MGT_REFCLKP : inout std_logic;
      SFP_MGT_REFCLKN : inout std_logic;
      SATA_MGT_REFCLKP: inout std_logic;
      SATA_MGT_REFCLKN: inout std_logic;

-- ##  Global Clock inputs 
      LVPECL_200M_P   : inout std_logic;
      LVPECL_200M_N   : inout std_logic;
      SMA_GCLKP       : inout std_logic;
      SMA_GCLKN       : inout std_logic;
      LVDSCLKMOD1_P   : inout std_logic;
      LVDSCLKMOD1_N   : inout std_logic;
      SATA_MGT_GCLKP  : inout std_logic;
      SATA_MGT_GCLKN  : inout std_logic;
      SFP_MGT_GCLKP   : inout std_logic;  -- 125 MHz clock
      SFP_MGT_GCLKN   : inout std_logic;  -- 125 MHz clock
      FPGA_GCLK_33MHZ : inout std_logic;
      PCIE_GCLK_P     : inout std_logic;
      PCIE_GCLK_N     : inout std_logic;
      SATA_MGT_CLKSEL : out std_logic;

-- ##  ML555 USER Switch and LED pins
-- ##  Turn LED "ON" by driving output to logic "0".
      USER_LED0 : out std_logic;
      USER_LED1 : out std_logic;
      USER_LED2 : out std_logic;
-- ## 4.7K pullups on switches, active LOW when pressed
      USER_SW1  : in  std_logic;
      USER_SW2  : in  std_logic;
      USER_SW3  : in  std_logic;
-- ##    ML555 Platform Flash configuration data pins
      FLASH_D   : inout std_logic_vector(7 downto 0);
-- ##    ML555 FPGA to CPLD interconnect pins 
      CPLD_SPARE1  : inout std_logic;
      CPLD_SPARE2  : inout std_logic;
      CPLD_SPARE3  : inout std_logic;

-- ##    ML555 ICS8442 Clock Synthesizer Interface -- Clock Synthesizer #1
      PLOAD_1  : inout std_logic;
      STROBE_1 : inout std_logic;
      SDATA_1  : inout std_logic;
      SCLOCK_1 : inout std_logic;
-- ##    ML555 ICS8442 Clock Synthesizer Interface -- Clock Synthesizer #2
      PLOAD_2  : inout std_logic;
      STROBE_2 : inout std_logic;
      SDATA_2  : inout std_logic;
      SCLOCK_2 : inout std_logic;
-- ##      Jumper PCI-X Capable Configuration Pin 
      EDGE_PCIXCAP    : inout std_logic;
      FPGA_EDGE_PME_B : inout std_logic;
-- ##    ML555 FPGA PCI/PCI-X Core User I/O Connects
      FORCE        : inout std_logic;
      PCIW_EN      : inout std_logic;
      RTR          : inout std_logic;
      WIDE         : inout std_logic;
-- ##   ML555 PCI Edge Connector pins
      EDGE_DEVSEL_B : inout std_logic;
      EDGE_FRAME_B  : inout std_logic;
      EDGE_GNT_B    : inout std_logic;
      EDGE_IDSEL    : inout std_logic;
      EDGE_INTA_B   : inout std_logic;
      EDGE_INTB_B   : inout std_logic;
      EDGE_INTC_B   : inout std_logic;
      EDGE_INTD_B   : inout std_logic;
      EDGE_IRDY_B   : inout std_logic;
      EDGE_PAR      : inout std_logic;
      EDGE_PERR_B   : inout std_logic;
      EDGE_REQ_B    : inout std_logic;
      EDGE_RST_B    : inout std_logic;
      EDGE_SERR_B   : inout std_logic;
      EDGE_STOP_B   : inout std_logic;
      EDGE_TRDY_B   : inout std_logic;
      EDGE_M66EN    : inout std_logic;
-- ##
      EDGE_AD   : inout std_logic_vector(63 downto 0);
      EDGE_CBE  : inout std_logic_vector( 7 downto 0);
      EDGE_PAR64    : inout std_logic;
      EDGE_REQ64_B  : inout std_logic;
      EDGE_ACK64_B  : inout std_logic;

-- ## PCI Edge Connector Clock pins
      PCIBUSCLK2  : inout std_logic;
      PCIBUSCLK1  : inout std_logic;

-- ##  ML555 DDR2 SODIMM 
      A      : inout std_logic_vector(12 downto 0);
      BA     : inout std_logic_vector(2 downto 0);
      DQ     : inout std_logic_vector(63 downto 0);
      DQS    : inout std_logic_vector(7 downto 0);
      DQS_B  : inout std_logic_vector(7 downto 0);
      DM     : inout std_logic_vector(7 downto 0);
-- ##   ML555 DDR2 SODIMM Control AND Clock pins
      S_B   : inout std_logic;
      ODT   : inout std_logic;
      CAS_B : inout std_logic;
      RAS_B : inout std_logic;
      WE_B  : inout std_logic;
      CK0   : inout std_logic;
      CK0_B : inout std_logic;
      CK1   : inout std_logic;
      CK1_B : inout std_logic;
      CKE   : inout std_logic;

      DDR2_DIMM_LB_BANK17_OUT : inout std_logic;
      DDR2_DIMM_LB_BANK17_IN  : inout std_logic;
      DDR2_DIMM_LB_BANK21_OUT : inout std_logic;
      DDR2_DIMM_LB_BANK21_IN  : inout std_logic;
      DDR2_DIMM_LB_BANK22_OUT : inout std_logic;
      DDR2_DIMM_LB_BANK22_IN  : inout std_logic;
 
-- ## ML555 DDR2 SODIMM SERIAL INTERFACE 
      SCL   : inout std_logic;
      SDA   : inout std_logic;
-- ##  ML555 LVDS Transmitter Interface
      GPIO1_02_P : inout std_logic;
      GPIO1_02_N : inout std_logic;
      GPIO1_03_P : inout std_logic;
      GPIO1_03_N : inout std_logic;
      GPIO1_04_P : inout std_logic;
      GPIO1_04_N : inout std_logic;
      GPIO1_05_P : inout std_logic;
      GPIO1_05_N : inout std_logic;
      GPIO1_06_P : inout std_logic;
      GPIO1_06_N : inout std_logic;
      GPIO1_07_P : inout std_logic;
      GPIO1_07_N : inout std_logic;
      GPIO1_08_P : inout std_logic;
      GPIO1_08_N : inout std_logic;
      GPIO1_09_P : inout std_logic;
      GPIO1_09_N : inout std_logic;
-- ##
      GPIO1_10_P : inout std_logic;
      GPIO1_10_N : inout std_logic;
      GPIO1_11_P : inout std_logic;
      GPIO1_11_N : inout std_logic;
      GPIO1_12_P : inout std_logic;
      GPIO1_12_N : inout std_logic;
      GPIO1_13_P : inout std_logic;
      GPIO1_13_N : inout std_logic;
-- ##
      GPIO1_14_P : inout std_logic;
      GPIO1_14_N : inout std_logic;
      GPIO1_15_P : inout std_logic;
      GPIO1_15_N : inout std_logic;
      GPIO1_16_P : inout std_logic;
      GPIO1_16_N : inout std_logic;
      GPIO1_17_P : inout std_logic;
      GPIO1_17_N : inout std_logic;
      GPIO1_18_P : inout std_logic;
      GPIO1_18_N : inout std_logic;
      GPIO1_19_P : inout std_logic;
      GPIO1_19_N : inout std_logic;
      GPIO1_20_P : inout std_logic;
      GPIO1_20_N : inout std_logic;
      GPIO1_21_P : inout std_logic;
      GPIO1_21_N : inout std_logic;
-- ##  FPGA Bank 1, Vcco = 2.5V
      GPIO1_00_P : inout std_logic;
      GPIO1_00_N : inout std_logic;
      GPIO1_01_P : inout std_logic;
      GPIO1_01_N : inout std_logic;

      GPIO1_22_P : inout std_logic;
      GPIO1_22_N : inout std_logic;
      GPIO1_23_P : inout std_logic;
      GPIO1_23_N : inout std_logic;

-- ##  ML555 LVDS Receiver Interface - Connector P33 
      GPIO2_02_P : inout std_logic;
      GPIO2_02_N : inout std_logic;
      GPIO2_03_P : inout std_logic;
      GPIO2_03_N : inout std_logic;
      GPIO2_04_P : inout std_logic;
      GPIO2_04_N : inout std_logic;
      GPIO2_05_P : inout std_logic;
      GPIO2_05_N : inout std_logic;
      GPIO2_06_P : inout std_logic;
      GPIO2_06_N : inout std_logic;
      GPIO2_07_P : inout std_logic;
      GPIO2_07_N : inout std_logic;
      GPIO2_08_P : inout std_logic;
      GPIO2_08_N : inout std_logic;
      GPIO2_09_P : inout std_logic;
      GPIO2_09_N : inout std_logic;
-- ##
      GPIO2_10_P : inout std_logic;
      GPIO2_10_N : inout std_logic;
      GPIO2_11_P : inout std_logic;
      GPIO2_11_N : inout std_logic;
      GPIO2_12_P : inout std_logic;
      GPIO2_12_N : inout std_logic;
      GPIO2_13_P : inout std_logic;
      GPIO2_13_N : inout std_logic;
-- ##
      GPIO2_14_P : inout std_logic;
      GPIO2_14_N : inout std_logic;
      GPIO2_15_P : inout std_logic;
      GPIO2_15_N : inout std_logic;
      GPIO2_16_P : inout std_logic;
      GPIO2_16_N : inout std_logic;
      GPIO2_17_P : inout std_logic;
      GPIO2_17_N : inout std_logic;
      GPIO2_18_P : inout std_logic;
      GPIO2_18_N : inout std_logic;
      GPIO2_19_P : inout std_logic;
      GPIO2_19_N : inout std_logic;
      GPIO2_20_P : inout std_logic;
      GPIO2_20_N : inout std_logic;
      GPIO2_21_P : inout std_logic;
      GPIO2_21_N : inout std_logic;
-- ##  FPGA Bank 2, Vcco = 2.5V
      GPIO2_00_P : inout std_logic;
      GPIO2_00_N : inout std_logic;
      GPIO2_01_P : inout std_logic;
      GPIO2_01_N : inout std_logic;

      GPIO2_22_P : inout std_logic;
      GPIO2_22_N : inout std_logic;
      GPIO2_23_P : inout std_logic;
      GPIO2_23_N : inout std_logic;

-- ##  External serial configuration interface
      EXT_SEN    : inout std_logic;
      EXT_SDATA  : inout std_logic;
      EXT_SCLK   : inout std_logic;
      EXT_RESET  : inout std_logic;

-- ##  ML555 SFP II2 Configuration Interface 
      IIC_SDA_SFP1 : inout std_logic;
      IIC_SDC_SFP1 : inout std_logic;
      IIC_SDA: inout std_logic;
      IIC_SDC_SFP2 : inout std_logic;
-- ##  ML555 SFP TRANSMIT/RECEIVE INTERFACE
      SFP1_TXP : inout std_logic;
      SFP1_TXN : inout std_logic;
      SFP1_RXP : inout std_logic;
      SFP1_RXN : inout std_logic;
      SFP2_TXP : inout std_logic;
      SFP2_TXN : inout std_logic;
      SFP2_RXP : inout std_logic;
      SFP2_RXN : inout std_logic;
-- ##  ML555 SMA 
      SMA_TXP   : inout std_logic;
      SMA_TXN   : inout std_logic;
      SMA_RXP   : inout std_logic;
      SMA_RXN   : inout std_logic;
-- ## ML555 Serial ATA Disk Interface Connector J5
      SATA_TXP : inout std_logic;
      SATA_TXN : inout std_logic;
      SATA_RXP : inout std_logic;
      SATA_RXN : inout std_logic;
      
-- ##  ML555 Xilinx Generic Interface Header
      ESET_B   : inout std_logic;
-- #Port0 Receiver inputs
      P0_RD_RXD0    : inout std_logic;
      P0_RD_RXD1    : inout std_logic;
      P0_RD_RXD2    : inout std_logic;
      P0_RD_RXD3    : inout std_logic;
      P0_RXD4       : inout std_logic;
      P0_RXD5       : inout std_logic;
      P0_RXD6       : inout std_logic;
      P0_RXD7       : inout std_logic;

      P0_CRS        : inout std_logic;
      P0_RXCTL_RXDV : inout std_logic;
      P0_RCLK1      : inout std_logic;
      P0_RXC_RXCLK  : inout std_logic;
      P0_RXER       : inout std_logic;
-- #
-- #Port0 Transmitter ** FPGA OUTPUTS**
      P0_TD_TXD0    : inout std_logic;
      P0_TD_TXD1    : inout std_logic;
      P0_TD_TXD2    : inout std_logic;
      P0_TD_TXD3    : inout std_logic;
      P0_TXD4       : inout std_logic;
      P0_TXD5       : inout std_logic;
      P0_TXD6       : inout std_logic;
      P0_TXD7       : inout std_logic;
-- #
-- #Port0 control, status, clocks
      P0_COL        : inout std_logic;
      P0_INT        : inout std_logic;
      P0_TXC_GTXCLK : inout std_logic;
      P0_TXCTL_TXEN : inout std_logic;
      P0_TXER       : inout std_logic;
-- #
-- #Port0 PHY MDIO interface
      P0_MDC : inout std_logic;
      P0_MDIO: inout std_logic;

-- #Port1 Receiver inputs
      P1_RD_RXD0    : inout std_logic;
      P1_RD_RXD1    : inout std_logic;
      P1_RD_RXD2    : inout std_logic;
      P1_RD_RXD3    : inout std_logic;
      P1_RXD4       : inout std_logic;
      P1_RXD5       : inout std_logic;
      P1_RXD6       : inout std_logic;
      P1_RXD7       : inout std_logic;
-- #
      P1_CRS        : inout std_logic;
      P1_RXCTL_RXDV : inout std_logic;
      P1_RCLK1      : inout std_logic;
      P1_RXC_RXCLK  : inout std_logic;
      P1_RXER       : inout std_logic;
-- #
-- #Port1 Transmitter outputs
      P1_TD_TXD0    : inout std_logic;
      P1_TD_TXD1    : inout std_logic;
      P1_TD_TXD2    : inout std_logic;
      P1_TD_TXD3    : inout std_logic;
      P1_TXD4       : inout std_logic;
      P1_TXD5       : inout std_logic;
      P1_TXD6       : inout std_logic;
      P1_TXD7       : inout std_logic;
-- #
-- #Port1 control, status, clocks
      P1_COL        : inout std_logic;
      P1_INT        : inout std_logic;
      P1_TXC_GTXCLK : inout std_logic;
      P1_TXCTL_TXEN : inout std_logic;
      P1_TXER       : inout std_logic;
-- #Port1 PHY MDIO interface
      P1_MDC : inout std_logic;
      P1_MDIO: inout std_logic;
-- ##  PCI Express User I/O
      PCIE_RST : inout std_logic; -- ##  Active low reset from PCI Express system unit 
      
-- ## USB Interface
      USB_RST_B     : inout std_logic;
      USB_DSR_B     : inout std_logic;
      USB_RX        : inout std_logic;
      USB_CTS_B     : inout std_logic;
      USB_SUSPEND_B : inout std_logic;
      USB_DTR_B     : inout std_logic;
      USB_TX        : inout std_logic;
      USB_RTS_B     : inout std_logic;
-- ##
      pci_exp_txp   : out std_logic_vector(3 downto 0);
      pci_exp_txn   : out std_logic_vector(3 downto 0);
      pci_exp_rxp   : in  std_logic_vector(3 downto 0);
      pci_exp_rxn   : in  std_logic_vector(3 downto 0)
   );
end ML555;
