-------------------------------------------------------------------------------
-- Title      : Virtex-5 Ethernet MAC Wrapper
-------------------------------------------------------------------------------
-- File       : v5_emac_v1_6.v
-- Author     : Xilinx
-------------------------------------------------------------------------------
-- Copyright (c) 2004-2008 by Xilinx, Inc. All rights reserved.
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
-- of this text at all times. (c) Copyright 2004-2008 Xilinx, Inc.
-- All rights reserved.

--------------------------------------------------------------------------------
-- Description:  This wrapper file instantiates the full Virtex-5 Ethernet 
--               MAC (EMAC) primitive.  For one or both of the two Ethernet MACs
--               (EMAC0/EMAC1):
--
--               * all unused input ports on the primitive will be tied to the
--                 appropriate logic level;
--
--               * all unused output ports on the primitive will be left 
--                 unconnected;
--
--               * the Tie-off Vector will be connected based on the options 
--                 selected from CORE Generator;
--
--               * only used ports will be connected to the ports of this 
--                 wrapper file.
--
--               This simplified wrapper should therefore be used as the 
--               instantiation template for the EMAC in customer designs.
--------------------------------------------------------------------------------

library unisim;
use unisim.vcomponents.all;

library ieee;
use ieee.std_logic_1164.all;

--------------------------------------------------------------------------------
-- The entity declaration for the Virtex-5 Embedded Ethernet MAC wrapper.
--------------------------------------------------------------------------------

entity v5_emac_v1_6 is
    generic(
	INBANDFCS : boolean := true -- true = keep FCS, false = remove FCS
    );
    port(
        -- Client Receiver Interface - EMAC0
        EMAC0CLIENTRXCLIENTCLKOUT       : out std_logic;
        CLIENTEMAC0RXCLIENTCLKIN        : in  std_logic;
        EMAC0CLIENTRXD                  : out std_logic_vector(7 downto 0);
        EMAC0CLIENTRXDVLD               : out std_logic;
        EMAC0CLIENTRXDVLDMSW            : out std_logic;
        EMAC0CLIENTRXGOODFRAME          : out std_logic;
        EMAC0CLIENTRXBADFRAME           : out std_logic;
        EMAC0CLIENTRXFRAMEDROP          : out std_logic;
        EMAC0CLIENTRXSTATS              : out std_logic_vector(6 downto 0);
        EMAC0CLIENTRXSTATSVLD           : out std_logic;
        EMAC0CLIENTRXSTATSBYTEVLD       : out std_logic;

        -- Client Transmitter Interface - EMAC0
        EMAC0CLIENTTXCLIENTCLKOUT       : out std_logic;
        CLIENTEMAC0TXCLIENTCLKIN        : in  std_logic;
        CLIENTEMAC0TXD                  : in  std_logic_vector(7 downto 0);
        CLIENTEMAC0TXDVLD               : in  std_logic;
        CLIENTEMAC0TXDVLDMSW            : in  std_logic;
        EMAC0CLIENTTXACK                : out std_logic;
        CLIENTEMAC0TXFIRSTBYTE          : in  std_logic;
        CLIENTEMAC0TXUNDERRUN           : in  std_logic;
        EMAC0CLIENTTXCOLLISION          : out std_logic;
        EMAC0CLIENTTXRETRANSMIT         : out std_logic;
        CLIENTEMAC0TXIFGDELAY           : in  std_logic_vector(7 downto 0);
        EMAC0CLIENTTXSTATS              : out std_logic;
        EMAC0CLIENTTXSTATSVLD           : out std_logic;
        EMAC0CLIENTTXSTATSBYTEVLD       : out std_logic;

        -- MAC Control Interface - EMAC0
        CLIENTEMAC0PAUSEREQ             : in  std_logic;
        CLIENTEMAC0PAUSEVAL             : in  std_logic_vector(15 downto 0);

        -- Clock Signal - EMAC0
        GTX_CLK_0                       : in  std_logic;
        PHYEMAC0TXGMIIMIICLKIN          : in  std_logic;
        EMAC0PHYTXGMIIMIICLKOUT         : out std_logic;

        -- SGMII Interface - EMAC0
        RXDATA_0                        : in  std_logic_vector(7 downto 0);
        TXDATA_0                        : out std_logic_vector(7 downto 0);
        DCM_LOCKED_0                    : in  std_logic;
        AN_INTERRUPT_0                  : out std_logic;
        SIGNAL_DETECT_0                 : in  std_logic;
        PHYAD_0                         : in  std_logic_vector(4 downto 0);
        ENCOMMAALIGN_0                  : out std_logic;
        LOOPBACKMSB_0                   : out std_logic;
        MGTRXRESET_0                    : out std_logic;
        MGTTXRESET_0                    : out std_logic;
        POWERDOWN_0                     : out std_logic;
        SYNCACQSTATUS_0                 : out std_logic;
        RXCLKCORCNT_0                   : in  std_logic_vector(2 downto 0);
        RXBUFSTATUS_0                   : in  std_logic_vector(1 downto 0);
        RXCHARISCOMMA_0                 : in  std_logic;
        RXCHARISK_0                     : in  std_logic;
        RXDISPERR_0                     : in  std_logic;
        RXNOTINTABLE_0                  : in  std_logic;
        RXREALIGN_0                     : in  std_logic;
        RXRUNDISP_0                     : in  std_logic;
        TXBUFERR_0                      : in  std_logic;
        TXCHARDISPMODE_0                : out std_logic;
        TXCHARDISPVAL_0                 : out std_logic;
        TXCHARISK_0                     : out std_logic;
        TXRUNDISP_0                     : in  std_logic;

        -- MDIO Interface - EMAC0
        MDC_0                           : out std_logic;
        MDIO_0_I                        : in  std_logic;
        MDIO_0_O                        : out std_logic;
        MDIO_0_T                        : out std_logic;
        EMAC0SPEEDIS10100               : out std_logic;

        -- Client Receiver Interface - EMAC1
        EMAC1CLIENTRXCLIENTCLKOUT       : out std_logic;
        CLIENTEMAC1RXCLIENTCLKIN        : in  std_logic;
        EMAC1CLIENTRXD                  : out std_logic_vector(7 downto 0);
        EMAC1CLIENTRXDVLD               : out std_logic;
        EMAC1CLIENTRXDVLDMSW            : out std_logic;
        EMAC1CLIENTRXGOODFRAME          : out std_logic;
        EMAC1CLIENTRXBADFRAME           : out std_logic;
        EMAC1CLIENTRXFRAMEDROP          : out std_logic;
        EMAC1CLIENTRXSTATS              : out std_logic_vector(6 downto 0);
        EMAC1CLIENTRXSTATSVLD           : out std_logic;
        EMAC1CLIENTRXSTATSBYTEVLD       : out std_logic;

        -- Client Transmitter Interface - EMAC1
        EMAC1CLIENTTXCLIENTCLKOUT       : out std_logic;
        CLIENTEMAC1TXCLIENTCLKIN        : in  std_logic;
        CLIENTEMAC1TXD                  : in  std_logic_vector(7 downto 0);
        CLIENTEMAC1TXDVLD               : in  std_logic;
        CLIENTEMAC1TXDVLDMSW            : in  std_logic;
        EMAC1CLIENTTXACK                : out std_logic;
        CLIENTEMAC1TXFIRSTBYTE          : in  std_logic;
        CLIENTEMAC1TXUNDERRUN           : in  std_logic;
        EMAC1CLIENTTXCOLLISION          : out std_logic;
        EMAC1CLIENTTXRETRANSMIT         : out std_logic;
        CLIENTEMAC1TXIFGDELAY           : in  std_logic_vector(7 downto 0);
        EMAC1CLIENTTXSTATS              : out std_logic;
        EMAC1CLIENTTXSTATSVLD           : out std_logic;
        EMAC1CLIENTTXSTATSBYTEVLD       : out std_logic;

        -- MAC Control Interface - EMAC1
        CLIENTEMAC1PAUSEREQ             : in  std_logic;
        CLIENTEMAC1PAUSEVAL             : in  std_logic_vector(15 downto 0);

        -- Clock Signal - EMAC1
        GTX_CLK_1                       : in  std_logic;
        PHYEMAC1TXGMIIMIICLKIN          : in  std_logic;
        EMAC1PHYTXGMIIMIICLKOUT         : out std_logic;

        -- SGMII Interface - EMAC1
        RXDATA_1                        : in  std_logic_vector(7 downto 0);
        TXDATA_1                        : out std_logic_vector(7 downto 0);
        DCM_LOCKED_1                    : in  std_logic;
        AN_INTERRUPT_1                  : out std_logic;
        SIGNAL_DETECT_1                 : in  std_logic;
        PHYAD_1                         : in  std_logic_vector(4 downto 0);
        ENCOMMAALIGN_1                  : out std_logic;
        LOOPBACKMSB_1                   : out std_logic;
        MGTRXRESET_1                    : out std_logic;
        MGTTXRESET_1                    : out std_logic;
        POWERDOWN_1                     : out std_logic;
        SYNCACQSTATUS_1                 : out std_logic;
        RXCLKCORCNT_1                   : in  std_logic_vector(2 downto 0);
        RXBUFSTATUS_1                   : in  std_logic_vector(1 downto 0);
        RXCHARISCOMMA_1                 : in  std_logic;
        RXCHARISK_1                     : in  std_logic;
        RXDISPERR_1                     : in  std_logic;
        RXNOTINTABLE_1                  : in  std_logic;
        RXREALIGN_1                     : in  std_logic;
        RXRUNDISP_1                     : in  std_logic;
        TXBUFERR_1                      : in  std_logic;
        TXCHARDISPMODE_1                : out std_logic;
        TXCHARDISPVAL_1                 : out std_logic;
        TXCHARISK_1                     : out std_logic;
        TXRUNDISP_1                     : in  std_logic;

        -- MDIO Interface - EMAC1
        MDC_1                           : out std_logic;
        MDIO_1_I                        : in  std_logic;
        MDIO_1_O                        : out std_logic;
        MDIO_1_T                        : out std_logic;
        EMAC1SPEEDIS10100               : out std_logic;

        -- Host Interface
        HOSTCLK                         : in  std_logic;
        HOSTOPCODE                      : in  std_logic_vector(1 downto 0);
        HOSTREQ                         : in  std_logic;
        HOSTMIIMSEL                     : in  std_logic;
        HOSTADDR                        : in  std_logic_vector(9 downto 0);
        HOSTWRDATA                      : in  std_logic_vector(31 downto 0);
        HOSTMIIMRDY                     : out std_logic;
        HOSTRDDATA                      : out std_logic_vector(31 downto 0);
        HOSTEMAC1SEL                    : in  std_logic;



        -- Asynchronous Reset
        RESET                           : in  std_logic
        );
end v5_emac_v1_6;



architecture WRAPPER of v5_emac_v1_6 is

    ----------------------------------------------------------------------------
    -- Attribute declarations

    ----------------------------------------------------------------------------
    attribute X_CORE_INFO : string;
    attribute X_CORE_INFO of WRAPPER : architecture is "v5_emac_v1_6, Coregen 11.1";

    --------
    -- EMAC0
    --------
    -- Configure the PCS/PMA logic
    -- PCS/PMA Reset not asserted (normal operating mode)
    constant EMAC0_PHYRESET : boolean := FALSE;  
    -- PCS/PMA Auto-Negotiation Enable (enabled)
    constant EMAC0_PHYINITAUTONEG_ENABLE : boolean := FALSE;  
    -- PCS/PMA Isolate (not enabled)
    constant EMAC0_PHYISOLATE : boolean := FALSE;  
    -- PCS/PMA Powerdown (not in power down: normal operating mode)
    constant EMAC0_PHYPOWERDOWN : boolean := FALSE;  
    -- PCS/PMA Loopback (not enabled)
    constant EMAC0_PHYLOOPBACKMSB : boolean := FALSE;  
    -- Do not allow over/underflow in the GTP during auto-negotiation
    constant EMAC0_CONFIGVEC_79 : boolean := TRUE; 
    -- GT loopback (not enabled)
    constant EMAC0_GTLOOPBACK : boolean := FALSE; 
    -- Do not allow TX without having established a valid link
    constant EMAC0_UNIDIRECTION_ENABLE : boolean := FALSE; 
    constant EMAC0_LINKTIMERVAL : bit_vector := x"032";

    -- Configure the MAC operating mode
    -- MDIO is enabled
    constant EMAC0_MDIO_ENABLE : boolean := TRUE;  
    -- Speed is defaulted to 1000Mb/s
    constant EMAC0_SPEED_LSB : boolean := FALSE;
    constant EMAC0_SPEED_MSB : boolean := TRUE; 
    constant EMAC0_USECLKEN : boolean := FALSE;
    constant EMAC0_BYTEPHY : boolean := FALSE;
   
    constant EMAC0_RGMII_ENABLE : boolean := FALSE;
    -- SGMII is used to connect to PHY
    constant EMAC0_SGMII_ENABLE : boolean := TRUE;  
    constant EMAC0_1000BASEX_ENABLE : boolean := FALSE;
    -- The Host I/F is used to configure the MAC
    constant EMAC0_HOST_ENABLE : boolean := TRUE;  
    -- 8-bit interface for Tx client
    constant EMAC0_TX16BITCLIENT_ENABLE : boolean := FALSE;
    -- 8-bit interface for Rx client  
    constant EMAC0_RX16BITCLIENT_ENABLE : boolean := FALSE;  
    -- The Address Filter (not enabled)
    constant EMAC0_ADDRFILTER_ENABLE : boolean := FALSE;  

    -- MAC configuration defaults
    -- Rx Length/Type checking enabled (standard IEEE operation)
    constant EMAC0_LTCHECK_DISABLE : boolean := FALSE;  
    -- Rx Flow Control (not enabled)
    constant EMAC0_RXFLOWCTRL_ENABLE : boolean := FALSE;  
    -- Tx Flow Control (not enabled)
    constant EMAC0_TXFLOWCTRL_ENABLE : boolean := FALSE;  
    -- Transmitter is not held in reset not asserted (normal operating mode)
    constant EMAC0_TXRESET : boolean := FALSE;  
    -- Transmitter Jumbo Frames (not enabled)
    constant EMAC0_TXJUMBOFRAME_ENABLE : boolean := FALSE;  
    -- Transmitter In-band FCS (not enabled)
    constant EMAC0_TXINBANDFCS_ENABLE : boolean := FALSE;  
    -- Transmitter Enabled
    constant EMAC0_TX_ENABLE : boolean := TRUE;  
    -- Transmitter VLAN mode (not enabled)
    constant EMAC0_TXVLAN_ENABLE : boolean := FALSE;  
    -- Transmitter Half Duplex mode (not enabled)
    constant EMAC0_TXHALFDUPLEX : boolean := FALSE;  
    -- Transmitter IFG Adjust (not enabled)
    constant EMAC0_TXIFGADJUST_ENABLE : boolean := FALSE;  
    -- Receiver is not held in reset not asserted (normal operating mode)
    constant EMAC0_RXRESET : boolean := FALSE;  
    -- Receiver Jumbo Frames (not enabled)
    constant EMAC0_RXJUMBOFRAME_ENABLE : boolean := FALSE;  
    -- Receiver In-band FCS (enabled)
    constant EMAC0_RXINBANDFCS_ENABLE : boolean := INBANDFCS;  
    -- Receiver Enabled
    constant EMAC0_RX_ENABLE : boolean := TRUE;  
    -- Receiver VLAN mode (not enabled)
    constant EMAC0_RXVLAN_ENABLE : boolean := FALSE;  
    -- Receiver Half Duplex mode (not enabled)
    constant EMAC0_RXHALFDUPLEX : boolean := FALSE;  

    -- Set the Pause Address Default
    constant EMAC0_PAUSEADDR : bit_vector := x"FFEEDDCCBBAA";

    constant EMAC0_UNICASTADDR : bit_vector := x"000000000000";
 
    constant EMAC0_DCRBASEADDR : bit_vector := X"00";
    --------
    -- EMAC1
    --------
    -- Configure the PCS/PMA logic
    -- PCS/PMA Reset not asserted (normal operating mode)
    constant EMAC1_PHYRESET : boolean := FALSE;  
    -- PCS/PMA Auto-Negotiation Enable (enabled)
    constant EMAC1_PHYINITAUTONEG_ENABLE : boolean := FALSE;  
    -- PCS/PMA Isolate (not enabled)
    constant EMAC1_PHYISOLATE : boolean := FALSE;  
    -- PCS/PMA Powerdown (not in power down: normal operating mode)
    constant EMAC1_PHYPOWERDOWN : boolean := FALSE;  
    -- PCS/PMA Loopback (not enabled)
    constant EMAC1_PHYLOOPBACKMSB : boolean := FALSE;  
    -- Do not allow over/underflow in the GTP during auto-negotiation
    constant EMAC1_CONFIGVEC_79 : boolean := TRUE; 
    -- GT loopback (not enabled)
    constant EMAC1_GTLOOPBACK : boolean := FALSE; 
    -- Do not allow TX without having established a valid link
    constant EMAC1_UNIDIRECTION_ENABLE : boolean := FALSE; 
    constant EMAC1_LINKTIMERVAL : bit_vector := x"032";

    -- Configure the MAC operating mode
    -- MDIO is enabled
    constant EMAC1_MDIO_ENABLE : boolean := TRUE;  
    -- Speed is defaulted to 1000Mb/s
    constant EMAC1_SPEED_LSB : boolean := FALSE;
    constant EMAC1_SPEED_MSB : boolean := TRUE; 
    constant EMAC1_USECLKEN : boolean := FALSE;
    constant EMAC1_BYTEPHY : boolean := FALSE;
   
    constant EMAC1_RGMII_ENABLE : boolean := FALSE;
    -- SGMII is used to connect to PHY
    constant EMAC1_SGMII_ENABLE : boolean := TRUE;  
    constant EMAC1_1000BASEX_ENABLE : boolean := FALSE;
    -- The Host I/F is used to configure the MAC
    constant EMAC1_HOST_ENABLE : boolean := TRUE;  
    -- 8-bit interface for Tx client
    constant EMAC1_TX16BITCLIENT_ENABLE : boolean := FALSE;
    -- 8-bit interface for Rx client  
    constant EMAC1_RX16BITCLIENT_ENABLE : boolean := FALSE;  
    -- The Address Filter (not enabled)
    constant EMAC1_ADDRFILTER_ENABLE : boolean := FALSE;  

    -- MAC configuration defaults
    -- Rx Length/Type checking enabled (standard IEEE operation)
    constant EMAC1_LTCHECK_DISABLE : boolean := FALSE;  
    -- Rx Flow Control (not enabled)
    constant EMAC1_RXFLOWCTRL_ENABLE : boolean := FALSE;  
    -- Tx Flow Control (not enabled)
    constant EMAC1_TXFLOWCTRL_ENABLE : boolean := FALSE;  
    -- Transmitter is not held in reset not asserted (normal operating mode)
    constant EMAC1_TXRESET : boolean := FALSE;  
    -- Transmitter Jumbo Frames (not enabled)
    constant EMAC1_TXJUMBOFRAME_ENABLE : boolean := FALSE;  
    -- Transmitter In-band FCS (not enabled)
    constant EMAC1_TXINBANDFCS_ENABLE : boolean := FALSE;  
    -- Transmitter Enabled
    constant EMAC1_TX_ENABLE : boolean := TRUE;  
    -- Transmitter VLAN mode (not enabled)
    constant EMAC1_TXVLAN_ENABLE : boolean := FALSE;  
    -- Transmitter Half Duplex mode (not enabled)
    constant EMAC1_TXHALFDUPLEX : boolean := FALSE;  
    -- Transmitter IFG Adjust (not enabled)
    constant EMAC1_TXIFGADJUST_ENABLE : boolean := FALSE;  
    -- Receiver is not held in reset not asserted (normal operating mode)
    constant EMAC1_RXRESET : boolean := FALSE;  
    -- Receiver Jumbo Frames (not enabled)
    constant EMAC1_RXJUMBOFRAME_ENABLE : boolean := FALSE;  
    -- Receiver In-band FCS (enabled)
    constant EMAC1_RXINBANDFCS_ENABLE : boolean := INBANDFCS;  
    -- Receiver Enabled
    constant EMAC1_RX_ENABLE : boolean := TRUE;  
    -- Receiver VLAN mode (not enabled)
    constant EMAC1_RXVLAN_ENABLE : boolean := FALSE;  
    -- Receiver Half Duplex mode (not enabled)
    constant EMAC1_RXHALFDUPLEX : boolean := FALSE;  

    -- Set the Pause Address Default
    constant EMAC1_PAUSEADDR : bit_vector := x"FFEEDDCCBBAA";

    constant EMAC1_UNICASTADDR : bit_vector := x"000000000000";
    constant EMAC1_DCRBASEADDR : bit_vector := X"00";
 

    ----------------------------------------------------------------------------
    -- Signals Declarations
    ----------------------------------------------------------------------------


    signal gnd_v48_i                      : std_logic_vector(47 downto 0);

    signal client_rx_data_0_i             : std_logic_vector(15 downto 0);
    signal client_tx_data_0_i             : std_logic_vector(15 downto 0);
    signal client_tx_data_valid_0_i       : std_logic;
    signal client_tx_data_valid_msb_0_i   : std_logic;

    signal client_rx_data_1_i             : std_logic_vector(15 downto 0);
    signal client_tx_data_1_i             : std_logic_vector(15 downto 0);
    signal client_tx_data_valid_1_i       : std_logic;
    signal client_tx_data_valid_msb_1_i   : std_logic;

begin


    ----------------------------------------------------------------------------
    -- Main Body of Code
    ----------------------------------------------------------------------------


    gnd_v48_i <= "000000000000000000000000000000000000000000000000";

    -- 8-bit client data on EMAC0
    EMAC0CLIENTRXD <= client_rx_data_0_i(7 downto 0);
    client_tx_data_0_i <= "00000000" & CLIENTEMAC0TXD after 4 ns;
    client_tx_data_valid_0_i <= CLIENTEMAC0TXDVLD after 4 ns;
    client_tx_data_valid_msb_0_i <= '0';

    -- 8-bit client data on EMAC1
    EMAC1CLIENTRXD <= client_rx_data_1_i(7 downto 0);
    client_tx_data_1_i <= "00000000" & CLIENTEMAC1TXD after 4 ns;
    client_tx_data_valid_1_i <= CLIENTEMAC1TXDVLD after 4 ns;
    client_tx_data_valid_msb_1_i <= '0';





    ----------------------------------------------------------------------------
    -- Instantiate the Virtex-5 Embedded Ethernet EMAC
    ----------------------------------------------------------------------------
    v5_emac : TEMAC
    generic map (
		EMAC0_1000BASEX_ENABLE      => EMAC0_1000BASEX_ENABLE,
		EMAC0_ADDRFILTER_ENABLE     => EMAC0_ADDRFILTER_ENABLE,
		EMAC0_BYTEPHY               => EMAC0_BYTEPHY,
		EMAC0_CONFIGVEC_79          => EMAC0_CONFIGVEC_79,
		EMAC0_DCRBASEADDR           => EMAC0_DCRBASEADDR,
		EMAC0_GTLOOPBACK            => EMAC0_GTLOOPBACK,
		EMAC0_HOST_ENABLE           => EMAC0_HOST_ENABLE,
		EMAC0_LINKTIMERVAL          => EMAC0_LINKTIMERVAL(3 to 11),
		EMAC0_LTCHECK_DISABLE       => EMAC0_LTCHECK_DISABLE,
		EMAC0_MDIO_ENABLE           => EMAC0_MDIO_ENABLE,
		EMAC0_PAUSEADDR             => EMAC0_PAUSEADDR,
		EMAC0_PHYINITAUTONEG_ENABLE => EMAC0_PHYINITAUTONEG_ENABLE,
		EMAC0_PHYISOLATE            => EMAC0_PHYISOLATE,
		EMAC0_PHYLOOPBACKMSB        => EMAC0_PHYLOOPBACKMSB,
		EMAC0_PHYPOWERDOWN          => EMAC0_PHYPOWERDOWN,
		EMAC0_PHYRESET              => EMAC0_PHYRESET,
		EMAC0_RGMII_ENABLE          => EMAC0_RGMII_ENABLE,
		EMAC0_RX16BITCLIENT_ENABLE  => EMAC0_RX16BITCLIENT_ENABLE,
		EMAC0_RXFLOWCTRL_ENABLE     => EMAC0_RXFLOWCTRL_ENABLE,
		EMAC0_RXHALFDUPLEX          => EMAC0_RXHALFDUPLEX,
		EMAC0_RXINBANDFCS_ENABLE    => EMAC0_RXINBANDFCS_ENABLE,
		EMAC0_RXJUMBOFRAME_ENABLE   => EMAC0_RXJUMBOFRAME_ENABLE,
		EMAC0_RXRESET               => EMAC0_RXRESET,
		EMAC0_RXVLAN_ENABLE         => EMAC0_RXVLAN_ENABLE,
		EMAC0_RX_ENABLE             => EMAC0_RX_ENABLE,
		EMAC0_SGMII_ENABLE          => EMAC0_SGMII_ENABLE,
		EMAC0_SPEED_LSB             => EMAC0_SPEED_LSB,
		EMAC0_SPEED_MSB             => EMAC0_SPEED_MSB,
		EMAC0_TX16BITCLIENT_ENABLE  => EMAC0_TX16BITCLIENT_ENABLE,
		EMAC0_TXFLOWCTRL_ENABLE     => EMAC0_TXFLOWCTRL_ENABLE,
		EMAC0_TXHALFDUPLEX          => EMAC0_TXHALFDUPLEX,
		EMAC0_TXIFGADJUST_ENABLE    => EMAC0_TXIFGADJUST_ENABLE,
		EMAC0_TXINBANDFCS_ENABLE    => EMAC0_TXINBANDFCS_ENABLE,
		EMAC0_TXJUMBOFRAME_ENABLE   => EMAC0_TXJUMBOFRAME_ENABLE,
		EMAC0_TXRESET               => EMAC0_TXRESET,
		EMAC0_TXVLAN_ENABLE         => EMAC0_TXVLAN_ENABLE,
		EMAC0_TX_ENABLE             => EMAC0_TX_ENABLE,
		EMAC0_UNICASTADDR           => EMAC0_UNICASTADDR,
		EMAC0_UNIDIRECTION_ENABLE   => EMAC0_UNIDIRECTION_ENABLE,
		EMAC0_USECLKEN              => EMAC0_USECLKEN,
		EMAC1_1000BASEX_ENABLE      => EMAC1_1000BASEX_ENABLE,
		EMAC1_ADDRFILTER_ENABLE     => EMAC1_ADDRFILTER_ENABLE,
		EMAC1_BYTEPHY               => EMAC1_BYTEPHY,
		EMAC1_CONFIGVEC_79          => EMAC1_CONFIGVEC_79,
		EMAC1_DCRBASEADDR           => EMAC1_DCRBASEADDR,
		EMAC1_GTLOOPBACK            => EMAC1_GTLOOPBACK,
		EMAC1_HOST_ENABLE           => EMAC1_HOST_ENABLE,
		EMAC1_LINKTIMERVAL          => EMAC1_LINKTIMERVAL(3 to 11),
		EMAC1_LTCHECK_DISABLE       => EMAC1_LTCHECK_DISABLE,
		EMAC1_MDIO_ENABLE           => EMAC1_MDIO_ENABLE,
		EMAC1_PAUSEADDR             => EMAC1_PAUSEADDR,
		EMAC1_PHYINITAUTONEG_ENABLE => EMAC1_PHYINITAUTONEG_ENABLE,
		EMAC1_PHYISOLATE            => EMAC1_PHYISOLATE,
		EMAC1_PHYLOOPBACKMSB        => EMAC1_PHYLOOPBACKMSB,
		EMAC1_PHYPOWERDOWN          => EMAC1_PHYPOWERDOWN,
		EMAC1_PHYRESET              => EMAC1_PHYRESET,
		EMAC1_RGMII_ENABLE          => EMAC1_RGMII_ENABLE,
		EMAC1_RX16BITCLIENT_ENABLE  => EMAC1_RX16BITCLIENT_ENABLE,
		EMAC1_RXFLOWCTRL_ENABLE     => EMAC1_RXFLOWCTRL_ENABLE,
		EMAC1_RXHALFDUPLEX          => EMAC1_RXHALFDUPLEX,
		EMAC1_RXINBANDFCS_ENABLE    => EMAC1_RXINBANDFCS_ENABLE,
		EMAC1_RXJUMBOFRAME_ENABLE   => EMAC1_RXJUMBOFRAME_ENABLE,
		EMAC1_RXRESET               => EMAC1_RXRESET,
		EMAC1_RXVLAN_ENABLE         => EMAC1_RXVLAN_ENABLE,
		EMAC1_RX_ENABLE             => EMAC1_RX_ENABLE,
		EMAC1_SGMII_ENABLE          => EMAC1_SGMII_ENABLE,
		EMAC1_SPEED_LSB             => EMAC1_SPEED_LSB,
		EMAC1_SPEED_MSB             => EMAC1_SPEED_MSB,
		EMAC1_TX16BITCLIENT_ENABLE  => EMAC1_TX16BITCLIENT_ENABLE,
		EMAC1_TXFLOWCTRL_ENABLE     => EMAC1_TXFLOWCTRL_ENABLE,
		EMAC1_TXHALFDUPLEX          => EMAC1_TXHALFDUPLEX,
		EMAC1_TXIFGADJUST_ENABLE    => EMAC1_TXIFGADJUST_ENABLE,
		EMAC1_TXINBANDFCS_ENABLE    => EMAC1_TXINBANDFCS_ENABLE,
		EMAC1_TXJUMBOFRAME_ENABLE   => EMAC1_TXJUMBOFRAME_ENABLE,
		EMAC1_TXRESET               => EMAC1_TXRESET,
		EMAC1_TXVLAN_ENABLE         => EMAC1_TXVLAN_ENABLE,
		EMAC1_TX_ENABLE             => EMAC1_TX_ENABLE,
		EMAC1_UNICASTADDR           => EMAC1_UNICASTADDR,
		EMAC1_UNIDIRECTION_ENABLE   => EMAC1_UNIDIRECTION_ENABLE,
		EMAC1_USECLKEN              => EMAC1_USECLKEN
)
    port map (
        RESET                           => RESET,

        -- EMAC0
        EMAC0CLIENTRXCLIENTCLKOUT       => EMAC0CLIENTRXCLIENTCLKOUT,
        CLIENTEMAC0RXCLIENTCLKIN        => CLIENTEMAC0RXCLIENTCLKIN,
        EMAC0CLIENTRXD                  => client_rx_data_0_i,
        EMAC0CLIENTRXDVLD               => EMAC0CLIENTRXDVLD,
        EMAC0CLIENTRXDVLDMSW            => EMAC0CLIENTRXDVLDMSW,
        EMAC0CLIENTRXGOODFRAME          => EMAC0CLIENTRXGOODFRAME,
        EMAC0CLIENTRXBADFRAME           => EMAC0CLIENTRXBADFRAME,
        EMAC0CLIENTRXFRAMEDROP          => EMAC0CLIENTRXFRAMEDROP,
        EMAC0CLIENTRXSTATS              => EMAC0CLIENTRXSTATS,
        EMAC0CLIENTRXSTATSVLD           => EMAC0CLIENTRXSTATSVLD,
        EMAC0CLIENTRXSTATSBYTEVLD       => EMAC0CLIENTRXSTATSBYTEVLD,

        EMAC0CLIENTTXCLIENTCLKOUT       => EMAC0CLIENTTXCLIENTCLKOUT,
        CLIENTEMAC0TXCLIENTCLKIN        => CLIENTEMAC0TXCLIENTCLKIN,
        CLIENTEMAC0TXD                  => client_tx_data_0_i,
        CLIENTEMAC0TXDVLD               => client_tx_data_valid_0_i,
        CLIENTEMAC0TXDVLDMSW            => client_tx_data_valid_msb_0_i,
        EMAC0CLIENTTXACK                => EMAC0CLIENTTXACK,
        CLIENTEMAC0TXFIRSTBYTE          => CLIENTEMAC0TXFIRSTBYTE,
        CLIENTEMAC0TXUNDERRUN           => CLIENTEMAC0TXUNDERRUN,
        EMAC0CLIENTTXCOLLISION          => EMAC0CLIENTTXCOLLISION,
        EMAC0CLIENTTXRETRANSMIT         => EMAC0CLIENTTXRETRANSMIT,
        CLIENTEMAC0TXIFGDELAY           => CLIENTEMAC0TXIFGDELAY,
        EMAC0CLIENTTXSTATS              => EMAC0CLIENTTXSTATS,
        EMAC0CLIENTTXSTATSVLD           => EMAC0CLIENTTXSTATSVLD,
        EMAC0CLIENTTXSTATSBYTEVLD       => EMAC0CLIENTTXSTATSBYTEVLD,

        CLIENTEMAC0PAUSEREQ             => CLIENTEMAC0PAUSEREQ,
        CLIENTEMAC0PAUSEVAL             => CLIENTEMAC0PAUSEVAL,

        PHYEMAC0GTXCLK                  => GTX_CLK_0,
        PHYEMAC0TXGMIIMIICLKIN          => PHYEMAC0TXGMIIMIICLKIN,
        EMAC0PHYTXGMIIMIICLKOUT         => EMAC0PHYTXGMIIMIICLKOUT,
        PHYEMAC0RXCLK                   => '0',
        PHYEMAC0MIITXCLK                => '0',
        PHYEMAC0RXD                     => RXDATA_0,
        PHYEMAC0RXDV                    => RXREALIGN_0,
        PHYEMAC0RXER                    => '0',
        EMAC0PHYTXCLK                   => open,
        EMAC0PHYTXD                     => TXDATA_0,
        EMAC0PHYTXEN                    => open,
        EMAC0PHYTXER                    => open,
        PHYEMAC0COL                     => TXRUNDISP_0,
        PHYEMAC0CRS                     => '0',
        CLIENTEMAC0DCMLOCKED            => DCM_LOCKED_0,
        EMAC0CLIENTANINTERRUPT          => AN_INTERRUPT_0,
        PHYEMAC0SIGNALDET               => SIGNAL_DETECT_0,
        PHYEMAC0PHYAD                   => PHYAD_0,
        EMAC0PHYENCOMMAALIGN            => ENCOMMAALIGN_0,
        EMAC0PHYLOOPBACKMSB             => LOOPBACKMSB_0,
        EMAC0PHYMGTRXRESET              => MGTRXRESET_0,
        EMAC0PHYMGTTXRESET              => MGTTXRESET_0,
        EMAC0PHYPOWERDOWN               => POWERDOWN_0,
        EMAC0PHYSYNCACQSTATUS           => SYNCACQSTATUS_0,
        PHYEMAC0RXCLKCORCNT             => RXCLKCORCNT_0,
        PHYEMAC0RXBUFSTATUS             => RXBUFSTATUS_0,
        PHYEMAC0RXBUFERR                => '0',
        PHYEMAC0RXCHARISCOMMA           => RXCHARISCOMMA_0,
        PHYEMAC0RXCHARISK               => RXCHARISK_0,
        PHYEMAC0RXCHECKINGCRC           => '0',
        PHYEMAC0RXCOMMADET              => '0',
        PHYEMAC0RXDISPERR               => RXDISPERR_0,
        PHYEMAC0RXLOSSOFSYNC            => gnd_v48_i(1 downto 0),
        PHYEMAC0RXNOTINTABLE            => RXNOTINTABLE_0,
        PHYEMAC0RXRUNDISP               => RXRUNDISP_0,
        PHYEMAC0TXBUFERR                => TXBUFERR_0,
        EMAC0PHYTXCHARDISPMODE          => TXCHARDISPMODE_0,
        EMAC0PHYTXCHARDISPVAL           => TXCHARDISPVAL_0,
        EMAC0PHYTXCHARISK               => TXCHARISK_0,

        EMAC0PHYMCLKOUT                 => MDC_0,
        PHYEMAC0MCLKIN                  => '0',
        PHYEMAC0MDIN                    => MDIO_0_I,
        EMAC0PHYMDOUT                   => MDIO_0_O,
        EMAC0PHYMDTRI                   => MDIO_0_T,
        EMAC0SPEEDIS10100               => EMAC0SPEEDIS10100,

        -- EMAC1
        EMAC1CLIENTRXCLIENTCLKOUT       => EMAC1CLIENTRXCLIENTCLKOUT,
        CLIENTEMAC1RXCLIENTCLKIN        => CLIENTEMAC1RXCLIENTCLKIN,
        EMAC1CLIENTRXD                  => client_rx_data_1_i,
        EMAC1CLIENTRXDVLD               => EMAC1CLIENTRXDVLD,
        EMAC1CLIENTRXDVLDMSW            => EMAC1CLIENTRXDVLDMSW,
        EMAC1CLIENTRXGOODFRAME          => EMAC1CLIENTRXGOODFRAME,
        EMAC1CLIENTRXBADFRAME           => EMAC1CLIENTRXBADFRAME,
        EMAC1CLIENTRXFRAMEDROP          => EMAC1CLIENTRXFRAMEDROP,
        EMAC1CLIENTRXSTATS              => EMAC1CLIENTRXSTATS,
        EMAC1CLIENTRXSTATSVLD           => EMAC1CLIENTRXSTATSVLD,
        EMAC1CLIENTRXSTATSBYTEVLD       => EMAC1CLIENTRXSTATSBYTEVLD,

        EMAC1CLIENTTXCLIENTCLKOUT       => EMAC1CLIENTTXCLIENTCLKOUT,
        CLIENTEMAC1TXCLIENTCLKIN        => CLIENTEMAC1TXCLIENTCLKIN,
        CLIENTEMAC1TXD                  => client_tx_data_1_i,
        CLIENTEMAC1TXDVLD               => client_tx_data_valid_1_i,
        CLIENTEMAC1TXDVLDMSW            => client_tx_data_valid_msb_1_i,
        EMAC1CLIENTTXACK                => EMAC1CLIENTTXACK,
        CLIENTEMAC1TXFIRSTBYTE          => CLIENTEMAC1TXFIRSTBYTE,
        CLIENTEMAC1TXUNDERRUN           => CLIENTEMAC1TXUNDERRUN,
        EMAC1CLIENTTXCOLLISION          => EMAC1CLIENTTXCOLLISION,
        EMAC1CLIENTTXRETRANSMIT         => EMAC1CLIENTTXRETRANSMIT,
        CLIENTEMAC1TXIFGDELAY           => CLIENTEMAC1TXIFGDELAY,
        EMAC1CLIENTTXSTATS              => EMAC1CLIENTTXSTATS,
        EMAC1CLIENTTXSTATSVLD           => EMAC1CLIENTTXSTATSVLD,
        EMAC1CLIENTTXSTATSBYTEVLD       => EMAC1CLIENTTXSTATSBYTEVLD,

        CLIENTEMAC1PAUSEREQ             => CLIENTEMAC1PAUSEREQ,
        CLIENTEMAC1PAUSEVAL             => CLIENTEMAC1PAUSEVAL,

        PHYEMAC1GTXCLK                  => GTX_CLK_1,
        PHYEMAC1TXGMIIMIICLKIN          => PHYEMAC1TXGMIIMIICLKIN,
        EMAC1PHYTXGMIIMIICLKOUT         => EMAC1PHYTXGMIIMIICLKOUT,
        PHYEMAC1RXCLK                   => '0',
        PHYEMAC1MIITXCLK                => '0',
        PHYEMAC1RXD                     => RXDATA_1,
        PHYEMAC1RXDV                    => RXREALIGN_1,
        PHYEMAC1RXER                    => '0',
        EMAC1PHYTXCLK                   => open,
        EMAC1PHYTXD                     => TXDATA_1,
        EMAC1PHYTXEN                    => open,
        EMAC1PHYTXER                    => open,
        PHYEMAC1COL                     => TXRUNDISP_1,
        PHYEMAC1CRS                     => '0',
        CLIENTEMAC1DCMLOCKED            => DCM_LOCKED_1,
        EMAC1CLIENTANINTERRUPT          => AN_INTERRUPT_1,
        PHYEMAC1SIGNALDET               => SIGNAL_DETECT_1,
        PHYEMAC1PHYAD                   => PHYAD_1,
        EMAC1PHYENCOMMAALIGN            => ENCOMMAALIGN_1,
        EMAC1PHYLOOPBACKMSB             => LOOPBACKMSB_1,
        EMAC1PHYMGTRXRESET              => MGTRXRESET_1,
        EMAC1PHYMGTTXRESET              => MGTTXRESET_1,
        EMAC1PHYPOWERDOWN               => POWERDOWN_1,
        EMAC1PHYSYNCACQSTATUS           => SYNCACQSTATUS_1,
        PHYEMAC1RXCLKCORCNT             => RXCLKCORCNT_1,
        PHYEMAC1RXBUFSTATUS             => RXBUFSTATUS_1,
        PHYEMAC1RXBUFERR                => '0',
        PHYEMAC1RXCHARISCOMMA           => RXCHARISCOMMA_1,
        PHYEMAC1RXCHARISK               => RXCHARISK_1,
        PHYEMAC1RXCHECKINGCRC           => '0',
        PHYEMAC1RXCOMMADET              => '0',
        PHYEMAC1RXDISPERR               => RXDISPERR_1,
        PHYEMAC1RXLOSSOFSYNC            => gnd_v48_i(1 downto 0),
        PHYEMAC1RXNOTINTABLE            => RXNOTINTABLE_1,
        PHYEMAC1RXRUNDISP               => RXRUNDISP_1,
        PHYEMAC1TXBUFERR                => TXBUFERR_1,
        EMAC1PHYTXCHARDISPMODE          => TXCHARDISPMODE_1,
        EMAC1PHYTXCHARDISPVAL           => TXCHARDISPVAL_1,
        EMAC1PHYTXCHARISK               => TXCHARISK_1,

        EMAC1PHYMCLKOUT                 => MDC_1,
        PHYEMAC1MCLKIN                  => '0',
        PHYEMAC1MDIN                    => MDIO_1_I,
        EMAC1PHYMDOUT                   => MDIO_1_O,
        EMAC1PHYMDTRI                   => MDIO_1_T,
        EMAC1SPEEDIS10100               => EMAC1SPEEDIS10100,

        -- Host Interface
        HOSTCLK                         => HOSTCLK,
        HOSTOPCODE                      => HOSTOPCODE,
        HOSTREQ                         => HOSTREQ,
        HOSTMIIMSEL                     => HOSTMIIMSEL,
        HOSTADDR                        => HOSTADDR,
        HOSTWRDATA                      => HOSTWRDATA,
        HOSTMIIMRDY                     => HOSTMIIMRDY,
        HOSTRDDATA                      => HOSTRDDATA,
        HOSTEMAC1SEL                    => HOSTEMAC1SEL,

        -- DCR Interface
        DCREMACCLK                      => '0',
        DCREMACABUS                     => gnd_v48_i(9 downto 0),
        DCREMACREAD                     => '0',
        DCREMACWRITE                    => '0',
        DCREMACDBUS                     => gnd_v48_i(31 downto 0),
        EMACDCRACK                      => open,
        EMACDCRDBUS                     => open,
        DCREMACENABLE                   => '0',
        DCRHOSTDONEIR                   => open
        );

end WRAPPER;
