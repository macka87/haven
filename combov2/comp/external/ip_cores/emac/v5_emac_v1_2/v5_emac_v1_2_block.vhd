-------------------------------------------------------------------------------
-- Title      : Virtex-5 Ethernet MAC Wrapper Top Level
-- Project    : Virtex-5 Ethernet MAC Wrappers
-------------------------------------------------------------------------------
-- File       : v5_emac_v1_2_block.vhd
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

-------------------------------------------------------------------------------
-- Description:  This is the EMAC block level VHDL design for the Virtex-5 
--               Embedded Ethernet MAC Example Design.  It is intended that
--               this example design can be quickly adapted and downloaded onto
--               an FPGA to provide a real hardware test environment.
--
--               The block level:
--
--               * instantiates all clock management logic required (BUFGs, 
--                 DCMs) to operate the EMAC and its example design;
--
--               * instantiates appropriate PHY interface modules (GMII, MII,
--                 RGMII, SGMII or 1000BASE-X) as required based on the user
--                 configuration.
--
--
--               Please refer to the Datasheet, Getting Started Guide, and
--               the Virtex-5 Embedded Tri-Mode Ethernet MAC User Gude for
--               further information.
-------------------------------------------------------------------------------


library unisim;
use unisim.vcomponents.all;

library ieee;
use ieee.std_logic_1164.all;



-------------------------------------------------------------------------------
-- The entity declaration for the top level design.
-------------------------------------------------------------------------------
entity v5_emac_v1_2_block is
   port(
      -- EMAC0 Clocking
      -- 125MHz clock output from transceiver
      CLK125_OUT                      : out std_logic;                 
      -- 125MHz clock input from BUFG
      CLK125                          : in  std_logic;

      -- Client Receiver Interface - EMAC0
      EMAC0CLIENTRXD                  : out std_logic_vector(7 downto 0);
      EMAC0CLIENTRXDVLD               : out std_logic;
      EMAC0CLIENTRXGOODFRAME          : out std_logic;
      EMAC0CLIENTRXBADFRAME           : out std_logic;
      EMAC0CLIENTRXFRAMEDROP          : out std_logic;
      EMAC0CLIENTRXSTATS              : out std_logic_vector(6 downto 0);
      EMAC0CLIENTRXSTATSVLD           : out std_logic;
      EMAC0CLIENTRXSTATSBYTEVLD       : out std_logic;

      -- Client Transmitter Interface - EMAC0
      CLIENTEMAC0TXD                  : in  std_logic_vector(7 downto 0);
      CLIENTEMAC0TXDVLD               : in  std_logic;
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

      --EMAC-MGT link status
      EMAC0CLIENTSYNCACQSTATUS        : out std_logic;
      -- EMAC0 Interrupt
      EMAC0ANINTERRUPT                : out std_logic;

 
      -- Clock Signals - EMAC0
      -- 1000BASE-X PCS/PMA Interface - EMAC0
      TXP_0                           : out std_logic;
      TXN_0                           : out std_logic;
      RXP_0                           : in  std_logic;
      RXN_0                           : in  std_logic;
      PHYAD_0                         : in  std_logic_vector(4 downto 0);
      RESETDONE_0                     : out std_logic;

      -- EMAC1 Clocking

      -- Client Receiver Interface - EMAC1
      EMAC1CLIENTRXD                  : out std_logic_vector(7 downto 0);
      EMAC1CLIENTRXDVLD               : out std_logic;
      EMAC1CLIENTRXGOODFRAME          : out std_logic;
      EMAC1CLIENTRXBADFRAME           : out std_logic;
      EMAC1CLIENTRXFRAMEDROP          : out std_logic;
      EMAC1CLIENTRXSTATS              : out std_logic_vector(6 downto 0);
      EMAC1CLIENTRXSTATSVLD           : out std_logic;
      EMAC1CLIENTRXSTATSBYTEVLD       : out std_logic;

      -- Client Transmitter Interface - EMAC1
      CLIENTEMAC1TXD                  : in  std_logic_vector(7 downto 0);
      CLIENTEMAC1TXDVLD               : in  std_logic;
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

      --EMAC-MGT link status
      EMAC1CLIENTSYNCACQSTATUS        : out std_logic;
      -- EMAC1 Interrupt
      EMAC1ANINTERRUPT                : out std_logic;

           
      -- Clock Signals - EMAC1
      -- 1000BASE-X PCS/PMA Interface - EMAC1
      TXP_1                           : out std_logic;
      TXN_1                           : out std_logic;
      RXP_1                           : in  std_logic;
      RXN_1                           : in  std_logic;
      PHYAD_1                         : in  std_logic_vector(4 downto 0);
      RESETDONE_1                     : out std_logic;

      -- 1000BASE-X PCS/PMA RocketIO Reference Clock buffer inputs 
      CLK_DS                          : in  std_logic;

        
        
      -- Asynchronous Reset
      RESET                           : in  std_logic;

      RIO_STATUS                      : out std_logic_vector(19 downto 0)
   );
end v5_emac_v1_2_block;


architecture TOP_LEVEL of v5_emac_v1_2_block is

-------------------------------------------------------------------------------
-- Component Declarations for lower hierarchial level entities
-------------------------------------------------------------------------------
  -- Component Declaration for the main EMAC wrapper
  component v5_emac_v1_2 is
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

      -- Clock Signals - EMAC0
      GTX_CLK_0                       : in  std_logic;
      PHYEMAC0TXGMIIMIICLKIN          : in  std_logic;
      EMAC0PHYTXGMIIMIICLKOUT         : out std_logic;

      -- 1000BASE-X PCS/PMA Interface - EMAC0
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
      TXRUNDISP_0                     : in std_logic;

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

      -- Clock Signals - EMAC1
      GTX_CLK_1                       : in  std_logic;
      PHYEMAC1TXGMIIMIICLKIN          : in  std_logic;
      EMAC1PHYTXGMIIMIICLKOUT         : out std_logic;

      -- 1000BASE-X PCS/PMA Interface - EMAC1
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
      TXRUNDISP_1                     : in std_logic;



      -- Asynchronous Reset
      RESET                           : in  std_logic
    );
  end component;


         
  -- Component Declaration for the RocketIO wrapper
  component GTP_dual_1000X
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
  end component;


 

-------------------------------------------------------------------------------
-- Signal Declarations
-------------------------------------------------------------------------------

    --  Power and ground signals
    signal gnd_i                          : std_logic;
    signal vcc_i                          : std_logic;

    -- Asynchronous reset signals
    signal reset_ibuf_i                   : std_logic;
    signal reset_i                        : std_logic;
    signal reset_r                        : std_logic_vector(3 downto 0);

    -- EMAC0 Client Clocking Signals
    signal rx_client_clk_out_0_i          : std_logic;
    signal rx_client_clk_in_0_i           : std_logic;
    signal tx_client_clk_out_0_i          : std_logic;
    signal tx_client_clk_in_0_i           : std_logic;
    -- EMAC0 Physical Interface Signals
    signal emac_locked_0_i                : std_logic;
    signal mgt_rx_data_0_i                : std_logic_vector(7 downto 0);
    signal mgt_tx_data_0_i                : std_logic_vector(7 downto 0);
    signal signal_detect_0_i              : std_logic;
    signal elecidle_0_i                   : std_logic;
    signal encommaalign_0_i               : std_logic;
    signal loopback_0_i                   : std_logic;
    signal mgt_rx_reset_0_i               : std_logic;
    signal mgt_tx_reset_0_i               : std_logic;
    signal powerdown_0_i                  : std_logic;
    signal rxclkcorcnt_0_i                : std_logic_vector(2 downto 0);
    signal rxbuferr_0_i                   : std_logic;
    signal rxchariscomma_0_i              : std_logic;
    signal rxcharisk_0_i                  : std_logic;
    signal rxdisperr_0_i                  : std_logic;
    signal rxlossofsync_0_i               : std_logic_vector(1 downto 0);
    signal rxnotintable_0_i               : std_logic;
    signal rxrundisp_0_i                  : std_logic;
    signal txbuferr_0_i                   : std_logic;
    signal txchardispmode_0_i             : std_logic;
    signal txchardispval_0_i              : std_logic;
    signal txcharisk_0_i                  : std_logic;
    signal gtx_clk_ibufg_0_i              : std_logic;
    signal resetdone_0_i                  : std_logic;
    signal rxbufstatus_0_i                : std_logic_vector(1 downto 0);

    -- EMAC1 Client Clocking Signals
    signal rx_client_clk_out_1_i          : std_logic;
    signal rx_client_clk_in_1_i           : std_logic;
    signal tx_client_clk_out_1_i          : std_logic;
    signal tx_client_clk_in_1_i           : std_logic;
    -- EMAC1 Physical Interface Signals
    signal emac_locked_1_i                : std_logic;
    signal mgt_rx_data_1_i                : std_logic_vector(7 downto 0);
    signal mgt_tx_data_1_i                : std_logic_vector(7 downto 0);
    signal signal_detect_1_i              : std_logic;
    signal elecidle_1_i                   : std_logic;
    signal encommaalign_1_i               : std_logic;
    signal loopback_1_i                   : std_logic;
    signal mgt_rx_reset_1_i               : std_logic;
    signal mgt_tx_reset_1_i               : std_logic;
    signal powerdown_1_i                  : std_logic;
    signal rxclkcorcnt_1_i                : std_logic_vector(2 downto 0);
    signal rxbuferr_1_i                   : std_logic;
    signal rxchariscomma_1_i              : std_logic;
    signal rxcharisk_1_i                  : std_logic;
    signal rxdisperr_1_i                  : std_logic;
    signal rxlossofsync_1_i               : std_logic_vector(1 downto 0);
    signal rxnotintable_1_i               : std_logic;
    signal rxrundisp_1_i                  : std_logic;
    signal txbuferr_1_i                   : std_logic;
    signal txchardispmode_1_i             : std_logic;
    signal txchardispval_1_i              : std_logic;
    signal txcharisk_1_i                  : std_logic;
    signal gtx_clk_ibufg_1_i              : std_logic;
    signal resetdone_1_i                  : std_logic;
    signal rxbufstatus_1_i                : std_logic_vector(1 downto 0);

    signal usrclk2                        : std_logic;   
    signal refclkout                      : std_logic;
    signal dcm_locked_gtp                 : std_logic;  
    signal plllock_0_i                    : std_logic;     
    signal plllock_1_i                    : std_logic;



-------------------------------------------------------------------------------
-- Attribute Declarations 
-------------------------------------------------------------------------------

  attribute ASYNC_REG : string;
  attribute ASYNC_REG of reset_r : signal is "TRUE";


-------------------------------------------------------------------------------
-- Main Body of Code
-------------------------------------------------------------------------------

begin

    gnd_i     <= '0';
    vcc_i     <= '1';

    ---------------------------------------------------------------------------
    -- Main Reset Circuitry
    ---------------------------------------------------------------------------
    reset_ibuf_i <= RESET;

    -- Asserting the reset of the EMAC for four clock cycles
    process(usrclk2, reset_ibuf_i)
    begin
        if (reset_ibuf_i = '1') then
            reset_r <= "1111";
        elsif usrclk2'event and usrclk2 = '1' then
          if (plllock_0_i = '1' and plllock_1_i = '1') then
            reset_r <= reset_r(2 downto 0) & reset_ibuf_i;
          end if;
        end if;
    end process;

    -- The reset pulse is now several clock cycles in duration
    reset_i <= reset_r(3);

 
   
    ---------------------------------------------------------------------------
    -- Instantiate RocketIO tile for SGMII or 1000BASE-X PCS/PMA Physical I/F
    ---------------------------------------------------------------------------


    --EMAC0 and EMAC1 instances
    GTP_DUAL_1000X_inst : GTP_dual_1000X 
      PORT MAP (
         RESETDONE_0           =>   RESETDONE_0,
         ENMCOMMAALIGN_0       =>   encommaalign_0_i,
         ENPCOMMAALIGN_0       =>   encommaalign_0_i,
         LOOPBACK_0            =>   loopback_0_i,
         RXUSRCLK_0            =>   usrclk2,
         RXUSRCLK2_0           =>   usrclk2,
         RXRESET_0             =>   mgt_rx_reset_0_i,
         TXCHARDISPMODE_0      =>   txchardispmode_0_i,
         TXCHARDISPVAL_0       =>   txchardispval_0_i,
         TXCHARISK_0           =>   txcharisk_0_i,
         TXDATA_0              =>   mgt_tx_data_0_i,
         TXUSRCLK_0            =>   usrclk2,
         TXUSRCLK2_0           =>   usrclk2,
         TXRESET_0             =>   mgt_tx_reset_0_i,                                   
         RXCHARISCOMMA_0       =>   rxchariscomma_0_i,
         RXCHARISK_0           =>   rxcharisk_0_i,
         RXCLKCORCNT_0         =>   rxclkcorcnt_0_i,
         RXCOMMADET_0          =>   open,
         RXDATA_0              =>   mgt_rx_data_0_i,
         RXDISPERR_0           =>   rxdisperr_0_i,
         RXNOTINTABLE_0        =>   rxnotintable_0_i,
         RXREALIGN_0           =>   open,
         RXRUNDISP_0           =>   rxrundisp_0_i,
         RXBUFERR_0            =>   rxbuferr_0_i,         
         TXBUFERR_0            =>   txbuferr_0_i,
         TXRUNDISP_0           =>   open,
         PLLLKDET_0            =>   plllock_0_i,
         RXELECIDLE_0          =>   elecidle_0_i,
         RX1P_0                =>   RXP_0,
         RX1N_0                =>   RXN_0,
         TX1N_0                =>   TXN_0,
         TX1P_0                =>   TXP_0,

         RESETDONE_1           =>   RESETDONE_1,
         ENMCOMMAALIGN_1       =>   encommaalign_1_i,
         ENPCOMMAALIGN_1       =>   encommaalign_1_i,
         LOOPBACK_1            =>   loopback_1_i,         
         RXUSRCLK_1            =>   usrclk2,
         RXUSRCLK2_1           =>   usrclk2,
         RXRESET_1             =>   mgt_rx_reset_1_i,         
         TXCHARDISPMODE_1      =>   txchardispmode_1_i,
         TXCHARDISPVAL_1       =>   txchardispval_1_i,
         TXCHARISK_1           =>   txcharisk_1_i,
         TXDATA_1              =>   mgt_tx_data_1_i,
         TXUSRCLK_1            =>   usrclk2,
         TXUSRCLK2_1           =>   usrclk2,
         TXRESET_1             =>   mgt_tx_reset_1_i,                                   
         RXCHARISCOMMA_1       =>   rxchariscomma_1_i,
         RXCHARISK_1           =>   rxcharisk_1_i,
         RXCLKCORCNT_1         =>   rxclkcorcnt_1_i,
         RXCOMMADET_1          =>   open,
         RXDATA_1              =>   mgt_rx_data_1_i,
         RXDISPERR_1           =>   rxdisperr_1_i,
         RXNOTINTABLE_1        =>   rxnotintable_1_i,
         RXREALIGN_1           =>   open,
         RXRUNDISP_1           =>   rxrundisp_1_i,
         RXBUFERR_1            =>   rxbuferr_1_i,
         TXBUFERR_1            =>   txbuferr_1_i,
         TXRUNDISP_1           =>   open,
         PLLLKDET_1            =>   plllock_1_i,
         TXOUTCLK_1            =>   open,         
         RXELECIDLE_1          =>   elecidle_1_i,
         RX1P_1                =>   RXP_1,
         RX1N_1                =>   RXN_1,
         TX1N_1                =>   TXN_1,
         TX1P_1                =>   TXP_1,
         CLK_DS                =>   CLK_DS,
         REFCLKOUT             =>   refclkout,
         TXOUTCLK_0            =>   open,
         PMARESET              =>   reset_ibuf_i,
         DCM_LOCKED            =>   dcm_locked_gtp,

         STATUS_INFO           => RIO_STATUS
    );




    ---------------------------------------------------------------------------
    -- Generate the buffer status input to the EMAC0 from the buffer error 
    -- output of the transceiver
    ---------------------------------------------------------------------------
    rxbufstatus_0_i(1) <= rxbuferr_0_i;

    ---------------------------------------------------------------------------
    -- Detect when there has been a disconnect
    ---------------------------------------------------------------------------
    signal_detect_0_i <= not(elecidle_0_i);


    ---------------------------------------------------------------------------
    -- Generate the buffer status input to the EMAC1 from the buffer error 
    -- output of the transceiver
    ---------------------------------------------------------------------------
    rxbufstatus_1_i(1) <= rxbuferr_1_i;
    
    ---------------------------------------------------------------------------
    -- Detect when there has been a disconnect
    ---------------------------------------------------------------------------
    signal_detect_1_i <= not(elecidle_1_i);
 




    --------------------------------------------------------------------
    -- Virtex5 Rocket I/O Clock Management
    --------------------------------------------------------------------

    -- The RocketIO transceivers are available in pairs with shared
    -- clock resources
    -- 125MHz clock is used for GTP user clocks and used
    -- to clock all Ethernet core logic.
    usrclk2                   <= CLK125;

    dcm_locked_gtp            <= '1';

    -- EMAC0: PLL locks
    emac_locked_0_i           <= plllock_0_i;


    ------------------------------------------------------------------------
    -- GTX_CLK Clock Management for EMAC0 - 125 MHz clock frequency
    -- (Connected to PHYEMAC0GTXCLK of the EMAC primitive)
    ------------------------------------------------------------------------
    gtx_clk_ibufg_0_i         <= usrclk2;


    ------------------------------------------------------------------------
    -- PCS/PMA client side receive clock for EMAC0
    ------------------------------------------------------------------------
    rx_client_clk_in_0_i      <= usrclk2;


    ------------------------------------------------------------------------
    -- PCS/PMA client side transmit clock for EMAC0
    ------------------------------------------------------------------------
    tx_client_clk_in_0_i      <= usrclk2;


    -- EMAC1: PLL locks
    emac_locked_1_i           <= plllock_1_i;


    ------------------------------------------------------------------------
    -- GTX_CLK Clock Management for EMAC1 - 125 MHz clock frequency
    -- (Connected to PHYEMAC1GTXCLK of the EMAC primitive)
    ------------------------------------------------------------------------
    gtx_clk_ibufg_1_i         <= usrclk2;


    ------------------------------------------------------------------------
    -- PCS/PMA client side receive clock for EMAC1
    ------------------------------------------------------------------------
    rx_client_clk_in_1_i      <= usrclk2;


    ------------------------------------------------------------------------
    -- PCS/PMA client side transmit clock for EMAC0
    ------------------------------------------------------------------------
    tx_client_clk_in_1_i      <= usrclk2;


    ------------------------------------------------------------------------
    -- Connect previously derived client clocks to example design output ports
    ------------------------------------------------------------------------
    -- EMAC0 Clocking
    -- 125MHz clock output from transceiver
    CLK125_OUT                <= refclkout;

    -- EMAC1 Clocking

 

    --------------------------------------------------------------------------
    -- Instantiate the EMAC Wrapper (v5_emac_v1_2.vhd)
    --------------------------------------------------------------------------
    v5_emac_wrapper : v5_emac_v1_2
    port map (
        -- Client Receiver Interface - EMAC0
        EMAC0CLIENTRXCLIENTCLKOUT       => rx_client_clk_out_0_i,
        CLIENTEMAC0RXCLIENTCLKIN        => rx_client_clk_in_0_i, 
        EMAC0CLIENTRXD                  => EMAC0CLIENTRXD,
        EMAC0CLIENTRXDVLD               => EMAC0CLIENTRXDVLD,
        EMAC0CLIENTRXDVLDMSW            => open,
        EMAC0CLIENTRXGOODFRAME          => EMAC0CLIENTRXGOODFRAME,
        EMAC0CLIENTRXBADFRAME           => EMAC0CLIENTRXBADFRAME,
        EMAC0CLIENTRXFRAMEDROP          => EMAC0CLIENTRXFRAMEDROP,
        EMAC0CLIENTRXSTATS              => EMAC0CLIENTRXSTATS,
        EMAC0CLIENTRXSTATSVLD           => EMAC0CLIENTRXSTATSVLD,
        EMAC0CLIENTRXSTATSBYTEVLD       => EMAC0CLIENTRXSTATSBYTEVLD,

        -- Client Transmitter Interface - EMAC0
        EMAC0CLIENTTXCLIENTCLKOUT       => tx_client_clk_out_0_i,
        CLIENTEMAC0TXCLIENTCLKIN        => tx_client_clk_in_0_i,
        CLIENTEMAC0TXD                  => CLIENTEMAC0TXD,
        CLIENTEMAC0TXDVLD               => CLIENTEMAC0TXDVLD,
        CLIENTEMAC0TXDVLDMSW            => gnd_i,
        EMAC0CLIENTTXACK                => EMAC0CLIENTTXACK,
        CLIENTEMAC0TXFIRSTBYTE          => CLIENTEMAC0TXFIRSTBYTE,
        CLIENTEMAC0TXUNDERRUN           => CLIENTEMAC0TXUNDERRUN,
        EMAC0CLIENTTXCOLLISION          => EMAC0CLIENTTXCOLLISION,
        EMAC0CLIENTTXRETRANSMIT         => EMAC0CLIENTTXRETRANSMIT,
        CLIENTEMAC0TXIFGDELAY           => CLIENTEMAC0TXIFGDELAY,
        EMAC0CLIENTTXSTATS              => EMAC0CLIENTTXSTATS,
        EMAC0CLIENTTXSTATSVLD           => EMAC0CLIENTTXSTATSVLD,
        EMAC0CLIENTTXSTATSBYTEVLD       => EMAC0CLIENTTXSTATSBYTEVLD,

        -- MAC Control Interface - EMAC0
        CLIENTEMAC0PAUSEREQ             => CLIENTEMAC0PAUSEREQ,
        CLIENTEMAC0PAUSEVAL             => CLIENTEMAC0PAUSEVAL,

        -- Clock Signals - EMAC0
        GTX_CLK_0                       => usrclk2,
        EMAC0PHYTXGMIIMIICLKOUT         => open,
        PHYEMAC0TXGMIIMIICLKIN          => gnd_i,

        -- 1000BASE-X PCS/PMA Interface - EMAC0
        RXDATA_0                        => mgt_rx_data_0_i,
        TXDATA_0                        => mgt_tx_data_0_i,
        DCM_LOCKED_0                    => emac_locked_0_i,
        AN_INTERRUPT_0                  => EMAC0ANINTERRUPT,
        SIGNAL_DETECT_0                 => signal_detect_0_i,
        PHYAD_0                         => PHYAD_0,
        ENCOMMAALIGN_0                  => encommaalign_0_i,
        LOOPBACKMSB_0                   => loopback_0_i,
        MGTRXRESET_0                    => mgt_rx_reset_0_i,
        MGTTXRESET_0                    => mgt_tx_reset_0_i,
        POWERDOWN_0                     => powerdown_0_i,
        SYNCACQSTATUS_0                 => EMAC0CLIENTSYNCACQSTATUS,
        RXCLKCORCNT_0                   => rxclkcorcnt_0_i,
        RXBUFSTATUS_0                   => rxbufstatus_0_i,
        RXCHARISCOMMA_0                 => rxchariscomma_0_i,
        RXCHARISK_0                     => rxcharisk_0_i,
        RXDISPERR_0                     => rxdisperr_0_i,
        RXNOTINTABLE_0                  => rxnotintable_0_i,
        RXREALIGN_0                     => '0',
        RXRUNDISP_0                     => rxrundisp_0_i,
        TXBUFERR_0                      => txbuferr_0_i,
        TXRUNDISP_0                     => '0',
        TXCHARDISPMODE_0                => txchardispmode_0_i,
        TXCHARDISPVAL_0                 => txchardispval_0_i,
        TXCHARISK_0                     => txcharisk_0_i,

        -- Client Receiver Interface - EMAC1
        EMAC1CLIENTRXCLIENTCLKOUT       => rx_client_clk_out_1_i,
        CLIENTEMAC1RXCLIENTCLKIN        => rx_client_clk_in_1_i,
        EMAC1CLIENTRXD                  => EMAC1CLIENTRXD,
        EMAC1CLIENTRXDVLD               => EMAC1CLIENTRXDVLD,
        EMAC1CLIENTRXDVLDMSW            => open,
        EMAC1CLIENTRXGOODFRAME          => EMAC1CLIENTRXGOODFRAME,
        EMAC1CLIENTRXBADFRAME           => EMAC1CLIENTRXBADFRAME,
        EMAC1CLIENTRXFRAMEDROP          => EMAC1CLIENTRXFRAMEDROP,
        EMAC1CLIENTRXSTATS              => EMAC1CLIENTRXSTATS,
        EMAC1CLIENTRXSTATSVLD           => EMAC1CLIENTRXSTATSVLD,
        EMAC1CLIENTRXSTATSBYTEVLD       => EMAC1CLIENTRXSTATSBYTEVLD,

        -- Client Transmitter Interface - EMAC1
        EMAC1CLIENTTXCLIENTCLKOUT       => tx_client_clk_out_1_i,
        CLIENTEMAC1TXCLIENTCLKIN        => tx_client_clk_in_1_i,
        CLIENTEMAC1TXD                  => CLIENTEMAC1TXD,
        CLIENTEMAC1TXDVLD               => CLIENTEMAC1TXDVLD,
        CLIENTEMAC1TXDVLDMSW            => gnd_i,
        EMAC1CLIENTTXACK                => EMAC1CLIENTTXACK,
        CLIENTEMAC1TXFIRSTBYTE          => CLIENTEMAC1TXFIRSTBYTE,
        CLIENTEMAC1TXUNDERRUN           => CLIENTEMAC1TXUNDERRUN,
        EMAC1CLIENTTXCOLLISION          => EMAC1CLIENTTXCOLLISION,
        EMAC1CLIENTTXRETRANSMIT         => EMAC1CLIENTTXRETRANSMIT,
        CLIENTEMAC1TXIFGDELAY           => CLIENTEMAC1TXIFGDELAY,
        EMAC1CLIENTTXSTATS              => EMAC1CLIENTTXSTATS,
        EMAC1CLIENTTXSTATSVLD           => EMAC1CLIENTTXSTATSVLD,
        EMAC1CLIENTTXSTATSBYTEVLD       => EMAC1CLIENTTXSTATSBYTEVLD,

        -- MAC Control Interface - EMAC1
        CLIENTEMAC1PAUSEREQ             => CLIENTEMAC1PAUSEREQ,
        CLIENTEMAC1PAUSEVAL             => CLIENTEMAC1PAUSEVAL,

        -- Clock Signals - EMAC1
        GTX_CLK_1                       => usrclk2,
        EMAC1PHYTXGMIIMIICLKOUT         => open,
        PHYEMAC1TXGMIIMIICLKIN          => gnd_i,
        -- 1000BASE-X PCS/PMA Interface - EMAC1
        RXDATA_1                        => mgt_rx_data_1_i,
        TXDATA_1                        => mgt_tx_data_1_i,
        DCM_LOCKED_1                    => emac_locked_1_i,
        AN_INTERRUPT_1                  => EMAC1ANINTERRUPT,
        SIGNAL_DETECT_1                 => signal_detect_1_i,
        PHYAD_1                         => PHYAD_1,
        ENCOMMAALIGN_1                  => encommaalign_1_i,
        LOOPBACKMSB_1                   => loopback_1_i,
        MGTRXRESET_1                    => mgt_rx_reset_1_i,
        MGTTXRESET_1                    => mgt_tx_reset_1_i,
        POWERDOWN_1                     => powerdown_1_i,
        SYNCACQSTATUS_1                 => EMAC1CLIENTSYNCACQSTATUS,
        RXCLKCORCNT_1                   => rxclkcorcnt_1_i,
        RXBUFSTATUS_1                   => rxbufstatus_1_i,
        RXCHARISCOMMA_1                 => rxchariscomma_1_i,
        RXCHARISK_1                     => rxcharisk_1_i,
        RXDISPERR_1                     => rxdisperr_1_i,
        RXNOTINTABLE_1                  => rxnotintable_1_i,
        RXREALIGN_1                     => '0',
        RXRUNDISP_1                     => rxrundisp_1_i,
        TXBUFERR_1                      => txbuferr_1_i,
        TXRUNDISP_1                     => '0',
        TXCHARDISPMODE_1                => txchardispmode_1_i,
        TXCHARDISPVAL_1                 => txchardispval_1_i,
        TXCHARISK_1                     => txcharisk_1_i,



        -- Asynchronous Reset
        RESET                           => reset_i
        );

  
 


 
end TOP_LEVEL;
