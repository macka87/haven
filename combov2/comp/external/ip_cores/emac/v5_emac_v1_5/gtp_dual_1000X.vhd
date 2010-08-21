-------------------------------------------------------------------------------
-- Title      : 1000BASE-X RocketIO wrapper
-- Project    : Virtex-5 Ethernet MAC Wrappers
-------------------------------------------------------------------------------
-- File       : gtp_dual_1000X.vhd
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
          RXDATA_0              : out   std_logic_vector (7 downto 0); 
          RXDISPERR_0           : out   std_logic; 
          RXNOTINTABLE_0        : out   std_logic;
          RXRUNDISP_0           : out   std_logic; 
          RXBUFERR_0            : out   std_logic;
          TXBUFERR_0            : out   std_logic; 
          PLLLKDET_0            : out   std_logic; 
          TXOUTCLK_0            : out   std_logic; 
          RXELECIDLE_0    	     : out   std_logic;
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
          RXDATA_1              : out   std_logic_vector (7 downto 0); 
          RXDISPERR_1           : out   std_logic; 
          RXNOTINTABLE_1        : out   std_logic;
          RXRUNDISP_1           : out   std_logic; 
          RXBUFERR_1            : out   std_logic;
          TXBUFERR_1            : out   std_logic; 
          PLLLKDET_1            : out   std_logic; 
          TXOUTCLK_1            : out   std_logic; 
          RXELECIDLE_1    	     : out   std_logic;
          TX1N_1                : out   std_logic; 
          TX1P_1                : out   std_logic;
          RX1N_1                : in    std_logic; 
          RX1P_1                : in    std_logic;


          CLK_DS                : in    std_logic;
          REFCLKOUT             : out   std_logic;
          PMARESET              : in    std_logic;
          DCM_LOCKED            : in    std_logic
          );
end GTP_dual_1000X;


architecture structural of GTP_dual_1000X is

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

  component ROCKETIO_WRAPPER_GTP
  generic
  (
    -- Simulation attributes
    WRAPPER_SIM_GTPRESET_SPEEDUP    : integer   := 0; -- Set to 1 to speed up sim reset
    WRAPPER_SIM_PLL_PERDIV2         : bit_vector:= x"190" -- Set to the VCO Unit Interval time
  );
  port
  (

    --_________________________________________________________________________
    --_________________________________________________________________________
    --TILE0  (Location)

    ------------------------ Loopback and Powerdown Ports ----------------------
    TILE0_LOOPBACK0_IN                      : in   std_logic_vector(2 downto 0);
    TILE0_LOOPBACK1_IN                      : in   std_logic_vector(2 downto 0);
    ----------------------- Receive Ports - 8b10b Decoder ----------------------
    TILE0_RXCHARISCOMMA0_OUT                : out  std_logic;
    TILE0_RXCHARISCOMMA1_OUT                : out  std_logic;
    TILE0_RXCHARISK0_OUT                    : out  std_logic;
    TILE0_RXCHARISK1_OUT                    : out  std_logic;
    TILE0_RXDISPERR0_OUT                    : out  std_logic;
    TILE0_RXDISPERR1_OUT                    : out  std_logic;
    TILE0_RXNOTINTABLE0_OUT                 : out  std_logic;
    TILE0_RXNOTINTABLE1_OUT                 : out  std_logic;
    TILE0_RXRUNDISP0_OUT                    : out  std_logic;
    TILE0_RXRUNDISP1_OUT                    : out  std_logic;
    ------------------- Receive Ports - Clock Correction Ports -----------------
    TILE0_RXCLKCORCNT0_OUT                  : out  std_logic_vector(2 downto 0);
    TILE0_RXCLKCORCNT1_OUT                  : out  std_logic_vector(2 downto 0);
    --------------- Receive Ports - Comma Detection and Alignment --------------
    TILE0_RXENMCOMMAALIGN0_IN               : in   std_logic;
    TILE0_RXENMCOMMAALIGN1_IN               : in   std_logic;
    TILE0_RXENPCOMMAALIGN0_IN               : in   std_logic;
    TILE0_RXENPCOMMAALIGN1_IN               : in   std_logic;
    ------------------- Receive Ports - RX Data Path interface -----------------
    TILE0_RXDATA0_OUT                       : out  std_logic_vector(7 downto 0);
    TILE0_RXDATA1_OUT                       : out  std_logic_vector(7 downto 0);
    TILE0_RXRECCLK0_OUT                     : out  std_logic;
    TILE0_RXRECCLK1_OUT                     : out  std_logic;
    TILE0_RXRESET0_IN                       : in   std_logic;
    TILE0_RXRESET1_IN                       : in   std_logic;
    TILE0_RXUSRCLK0_IN                      : in   std_logic;
    TILE0_RXUSRCLK1_IN                      : in   std_logic;
    TILE0_RXUSRCLK20_IN                     : in   std_logic;
    TILE0_RXUSRCLK21_IN                     : in   std_logic;
    ------- Receive Ports - RX Driver,OOB signalling,Coupling and Eq.,CDR ------
    TILE0_RXELECIDLE0_OUT                   : out  std_logic;
    TILE0_RXELECIDLE1_OUT                   : out  std_logic;
    TILE0_RXN0_IN                           : in   std_logic;
    TILE0_RXN1_IN                           : in   std_logic;
    TILE0_RXP0_IN                           : in   std_logic;
    TILE0_RXP1_IN                           : in   std_logic;
    -------- Receive Ports - RX Elastic Buffer and Phase Alignment Ports -------
    TILE0_RXBUFRESET0_IN                    : in   std_logic;
    TILE0_RXBUFRESET1_IN                    : in   std_logic;
    TILE0_RXBUFSTATUS0_OUT                  : out  std_logic_vector(2 downto 0);
    TILE0_RXBUFSTATUS1_OUT                  : out  std_logic_vector(2 downto 0);
    --------------------- Shared Ports - Tile and PLL Ports --------------------
    TILE0_CLKIN_IN                          : in   std_logic;
    TILE0_GTPRESET_IN                       : in   std_logic;
    TILE0_PLLLKDET_OUT                      : out  std_logic;
    TILE0_REFCLKOUT_OUT                     : out  std_logic;
    TILE0_RESETDONE0_OUT                    : out  std_logic;
    TILE0_RESETDONE1_OUT                    : out  std_logic;
    ---------------- Transmit Ports - 8b10b Encoder Control Ports --------------
    TILE0_TXCHARDISPMODE0_IN                : in   std_logic;
    TILE0_TXCHARDISPMODE1_IN                : in   std_logic;
    TILE0_TXCHARDISPVAL0_IN                 : in   std_logic;
    TILE0_TXCHARDISPVAL1_IN                 : in   std_logic;
    TILE0_TXCHARISK0_IN                     : in   std_logic;
    TILE0_TXCHARISK1_IN                     : in   std_logic;
    ------------- Transmit Ports - TX Buffering and Phase Alignment ------------
    TILE0_TXBUFSTATUS0_OUT                  : out  std_logic_vector(1 downto 0);
    TILE0_TXBUFSTATUS1_OUT                  : out  std_logic_vector(1 downto 0);
    ------------------ Transmit Ports - TX Data Path interface -----------------
    TILE0_TXDATA0_IN                        : in   std_logic_vector(7 downto 0);
    TILE0_TXDATA1_IN                        : in   std_logic_vector(7 downto 0);
    TILE0_TXOUTCLK0_OUT                     : out  std_logic;
    TILE0_TXOUTCLK1_OUT                     : out  std_logic;
    TILE0_TXRESET0_IN                       : in   std_logic;
    TILE0_TXRESET1_IN                       : in   std_logic;
    TILE0_TXUSRCLK0_IN                      : in   std_logic;
    TILE0_TXUSRCLK1_IN                      : in   std_logic;
    TILE0_TXUSRCLK20_IN                     : in   std_logic;
    TILE0_TXUSRCLK21_IN                     : in   std_logic;
    --------------- Transmit Ports - TX Driver and OOB signalling --------------
    TILE0_TXN0_OUT                          : out  std_logic;
    TILE0_TXN1_OUT                          : out  std_logic;
    TILE0_TXP0_OUT                          : out  std_logic;
    TILE0_TXP1_OUT                          : out  std_logic

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
         
   signal RXBUFSTATUS_float0    : std_logic_vector(1 downto 0);
   signal TXBUFSTATUS_float0    : std_logic;
   signal gt_txoutclk1_0        : std_logic;

   signal rxelecidle0_i         : std_logic;
   signal resetdone0_i          : std_logic;

   signal RXRECCLK_0            : std_logic;
   signal RXRECCLK_0_BUFR       : std_logic;
   signal RXCHARISCOMMA_0_REC   : std_logic;
   signal RXNOTINTABLE_0_REC    : std_logic;
   signal RXDATA_0_REC          : std_logic_vector(7 downto 0);
   signal RXCHARISK_0_REC       : std_logic;
   signal RXDISPERR_0_REC       : std_logic;
   signal RXRUNDISP_0_REC       : std_logic;

   signal RXRESET_0_REG         : std_logic;
   signal RXRESET_0_REC         : std_logic;
   signal RXRESET_0_USR_REG     : std_logic;
   signal RXRESET_0_USR         : std_logic;
   signal ENPCOMMAALIGN_0_REG   : std_logic;
   signal ENPCOMMAALIGN_0_REC   : std_logic;
   signal ENMCOMMAALIGN_0_REG   : std_logic;
   signal ENMCOMMAALIGN_0_REC   : std_logic;
   signal RXBUFERR_0_REC        : std_logic;
   signal RXBUFERR_0_INT        : std_logic;

   attribute ASYNC_REG                        : string;
   attribute ASYNC_REG of RXRESET_0_REG       : signal is "TRUE";
   attribute ASYNC_REG of RXRESET_0_REC       : signal is "TRUE";
   attribute ASYNC_REG of RXRESET_0_USR_REG   : signal is "TRUE";
   attribute ASYNC_REG of RXRESET_0_USR       : signal is "TRUE";
   attribute ASYNC_REG of ENPCOMMAALIGN_0_REG : signal is "TRUE";
   attribute ASYNC_REG of ENPCOMMAALIGN_0_REC : signal is "TRUE";
   attribute ASYNC_REG of ENMCOMMAALIGN_0_REG : signal is "TRUE";
   attribute ASYNC_REG of ENMCOMMAALIGN_0_REC : signal is "TRUE";


   signal RXNOTINTABLE_1_INT    : std_logic;   
   signal RXDATA_1_INT          : std_logic_vector (7 downto 0);
   signal RXCHARISK_1_INT       : std_logic;   
   signal RXDISPERR_1_INT       : std_logic;
   signal RXRUNDISP_1_INT       : std_logic;

   signal RXBUFSTATUS_float1    : std_logic_vector(1 downto 0);
   signal TXBUFSTATUS_float1    : std_logic;
   signal gt_txoutclk1_1        : std_logic;

   signal rxelecidle1_i         : std_logic;
   signal resetdone1_i          : std_logic;

   signal RXRECCLK_1            : std_logic;
   signal RXRECCLK_1_BUFR       : std_logic;
   signal RXCHARISCOMMA_1_REC   : std_logic;
   signal RXNOTINTABLE_1_REC    : std_logic;
   signal RXDATA_1_REC          : std_logic_vector(7 downto 0);
   signal RXCHARISK_1_REC       : std_logic;
   signal RXDISPERR_1_REC       : std_logic;
   signal RXRUNDISP_1_REC       : std_logic;

   signal RXRESET_1_REG         : std_logic;
   signal RXRESET_1_REC         : std_logic;
   signal RXRESET_1_USR_REG     : std_logic;
   signal RXRESET_1_USR         : std_logic;
   signal ENPCOMMAALIGN_1_REG   : std_logic;
   signal ENPCOMMAALIGN_1_REC   : std_logic;
   signal ENMCOMMAALIGN_1_REG   : std_logic;
   signal ENMCOMMAALIGN_1_REC   : std_logic;
   signal RXBUFERR_1_REC        : std_logic;
   signal RXBUFERR_1_INT        : std_logic;

   attribute ASYNC_REG of RXRESET_1_REG       : signal is "TRUE";
   attribute ASYNC_REG of RXRESET_1_REC       : signal is "TRUE";
   attribute ASYNC_REG of RXRESET_1_USR_REG   : signal is "TRUE";
   attribute ASYNC_REG of RXRESET_1_USR       : signal is "TRUE";
   attribute ASYNC_REG of ENPCOMMAALIGN_1_REG : signal is "TRUE";
   attribute ASYNC_REG of ENPCOMMAALIGN_1_REC : signal is "TRUE";
   attribute ASYNC_REG of ENMCOMMAALIGN_1_REG : signal is "TRUE";
   attribute ASYNC_REG of ENMCOMMAALIGN_1_REC : signal is "TRUE";

   signal pma_reset_i   : std_logic;
   signal reset_r       : std_logic_vector(3 downto 0);
   signal refclk_out    : std_logic;
   attribute ASYNC_REG of reset_r             : signal is "TRUE";

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

   RESETDONE_0          <= resetdone0_i;
   RXELECIDLE_0         <= rxelecidle0_i;

  
   RXNOTINTABLE_1  <=   RXNOTINTABLE_1_INT;
   RXDISPERR_1     <=   RXDISPERR_1_INT;
   TXOUTCLK_1      <=   gt_txoutclk1_1;

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

   -- Direct from the RocketIO Wizard output
   GTP_1000X : ROCKETIO_WRAPPER_GTP
    generic map (
        WRAPPER_SIM_GTPRESET_SPEEDUP   => 1,
        WRAPPER_SIM_PLL_PERDIV2        => x"190"
    )    
    port map (
        ------------------- Shared Ports - Tile and PLL Ports --------------------
        TILE0_CLKIN_IN                 => CLK_DS,
        TILE0_GTPRESET_IN              => pma_reset_i,
        TILE0_PLLLKDET_OUT             => PLLLOCK,
        TILE0_REFCLKOUT_OUT            => refclk_out,
        ---------------------- Loopback and Powerdown Ports ----------------------
	TILE0_LOOPBACK0_IN(2 downto 1) => "00",
        TILE0_LOOPBACK0_IN(0)          => LOOPBACK_0,
        --------------------- Receive Ports - 8b10b Decoder ----------------------
        TILE0_RXCHARISCOMMA0_OUT       => RXCHARISCOMMA_0_REC,
        TILE0_RXCHARISK0_OUT           => RXCHARISK_0_REC,
        TILE0_RXDISPERR0_OUT           => RXDISPERR_0_REC,
        TILE0_RXNOTINTABLE0_OUT        => RXNOTINTABLE_0_REC,
        TILE0_RXRUNDISP0_OUT           => RXRUNDISP_0_REC,
        ----------------- Receive Ports - Clock Correction Ports -----------------
        TILE0_RXCLKCORCNT0_OUT         => open,
        ------------- Receive Ports - Comma Detection and Alignment --------------
        TILE0_RXENMCOMMAALIGN0_IN      => ENMCOMMAALIGN_0_REC,
        TILE0_RXENPCOMMAALIGN0_IN      => ENMCOMMAALIGN_0_REC,
        ----------------- Receive Ports - RX Data Path interface -----------------
        TILE0_RXDATA0_OUT              => RXDATA_0_REC,
        TILE0_RXRECCLK0_OUT            => RXRECCLK_0,
        TILE0_RXRESET0_IN              => RXRESET_0_REC,
        TILE0_RXUSRCLK0_IN             => RXRECCLK_0_BUFR,
        TILE0_RXUSRCLK20_IN            => RXRECCLK_0_BUFR,
        ------ Receive Ports - RX Elastic Buffer and Phase Alignment Ports -------
        TILE0_RXBUFRESET0_IN           => RXRESET_0_REC,
        TILE0_RXBUFSTATUS0_OUT(2)      => RXBUFERR_0_REC,
        TILE0_RXBUFSTATUS0_OUT(1 downto 0) => RXBUFSTATUS_float0,		
        ----- Receive Ports - RX Driver,OOB signalling,Coupling and Eq.,CDR ------
        TILE0_RXELECIDLE0_OUT          => rxelecidle0_i,
        TILE0_RXN0_IN                  => RX1N_0,
        TILE0_RXP0_IN                  => RX1P_0,       
        ------------- ResetDone Ports --------------------------------------------
        TILE0_RESETDONE0_OUT           => resetdone0_i,
        -------------- Transmit Ports - 8b10b Encoder Control Ports --------------
        TILE0_TXCHARDISPMODE0_IN       => TXCHARDISPMODE_0,
        TILE0_TXCHARDISPVAL0_IN        => TXCHARDISPVAL_0,
        TILE0_TXCHARISK0_IN            => TXCHARISK_0,
        ----------- Transmit Ports - TX Buffering and Phase Alignment ------------
        TILE0_TXBUFSTATUS0_OUT(1)      => TXBUFERR_0, 
        TILE0_TXBUFSTATUS0_OUT(0)      => TXBUFSTATUS_float0,
        ---------------- Transmit Ports - TX Data Path interface -----------------
        TILE0_TXDATA0_IN               => TXDATA_0,
        TILE0_TXOUTCLK0_OUT            => gt_txoutclk1_0,
        TILE0_TXRESET0_IN              => TXRESET_0,
        TILE0_TXUSRCLK0_IN             => TXUSRCLK_0,
        TILE0_TXUSRCLK20_IN            => TXUSRCLK2_0,
        ------------- Transmit Ports - TX Driver and OOB signalling --------------
        TILE0_TXN0_OUT                 => TX1N_0,
        TILE0_TXP0_OUT                 => TX1P_0,
        ---------------------- Loopback and Powerdown Ports ----------------------
        TILE0_LOOPBACK1_IN(2 downto 1) => "00",
        TILE0_LOOPBACK1_IN(0)          => LOOPBACK_1,
        --------------------- Receive Ports - 8b10b Decoder ----------------------
        TILE0_RXCHARISCOMMA1_OUT       => RXCHARISCOMMA_1_REC,
        TILE0_RXCHARISK1_OUT           => RXCHARISK_1_REC,
        TILE0_RXDISPERR1_OUT           => RXDISPERR_1_REC,
        TILE0_RXNOTINTABLE1_OUT        => RXNOTINTABLE_1_REC,
        TILE0_RXRUNDISP1_OUT           => RXRUNDISP_1_REC,
        ----------------- Receive Ports - Clock Correction Ports -----------------
        TILE0_RXCLKCORCNT1_OUT         => open,
        ------------- Receive Ports - Comma Detection and Alignment --------------
        TILE0_RXENMCOMMAALIGN1_IN      => ENMCOMMAALIGN_1_REC,
        TILE0_RXENPCOMMAALIGN1_IN      => ENMCOMMAALIGN_1_REC,
        ----------------- Receive Ports - RX Data Path interface -----------------
        TILE0_RXDATA1_OUT              => RXDATA_1_REC,
        TILE0_RXRECCLK1_OUT            => RXRECCLK_1,
        TILE0_RXRESET1_IN              => RXRESET_1_REC,
        TILE0_RXUSRCLK1_IN             => RXRECCLK_1_BUFR,
        TILE0_RXUSRCLK21_IN            => RXRECCLK_1_BUFR,
        ------ Receive Ports - RX Elastic Buffer and Phase Alignment Ports -------
        TILE0_RXBUFRESET1_IN           => RXRESET_1_REC,
        TILE0_RXBUFSTATUS1_OUT(2)      => RXBUFERR_1_REC,
        TILE0_RXBUFSTATUS1_OUT(1 downto 0) => RXBUFSTATUS_float1,		
        ----- Receive Ports - RX Driver,OOB signalling,Coupling and Eq.,CDR ------
        TILE0_RXELECIDLE1_OUT          => rxelecidle1_i,
        TILE0_RXN1_IN                  => RX1N_1,
        TILE0_RXP1_IN                  => RX1P_1,       
        ------------- ResetDone Ports --------------------------------------------
        TILE0_RESETDONE1_OUT           => resetdone1_i,
        -------------- Transmit Ports - 8b10b Encoder Control Ports --------------
        TILE0_TXCHARDISPMODE1_IN       => TXCHARDISPMODE_1,
        TILE0_TXCHARDISPVAL1_IN        => TXCHARDISPVAL_1,
        TILE0_TXCHARISK1_IN            => TXCHARISK_1,
        ----------- Transmit Ports - TX Buffering and Phase Alignment ------------
        TILE0_TXBUFSTATUS1_OUT(1)      => TXBUFERR_1, 
        TILE0_TXBUFSTATUS1_OUT(0)      => TXBUFSTATUS_float1,
        ---------------- Transmit Ports - TX Data Path interface -----------------
        TILE0_TXDATA1_IN               => TXDATA_1,
        TILE0_TXOUTCLK1_OUT            => gt_txoutclk1_1,
        TILE0_TXRESET1_IN              => TXRESET_1,
        TILE0_TXUSRCLK1_IN             => TXUSRCLK_1,
        TILE0_TXUSRCLK21_IN            => TXUSRCLK2_1,
        ------------- Transmit Ports - TX Driver and OOB signalling --------------
        TILE0_TXN1_OUT                 => TX1N_1,
        TILE0_TXP1_OUT                 => TX1P_1
   );


   -- Route RXRECLK0 through a regional clock buffer
   rxrecclk0bufr : BUFR port map (I => RXRECCLK_0, O => RXRECCLK_0_BUFR,
                                   CE => '1', CLR => '0');

   -- Instantiate the RX elastic buffer. This performs clock
   -- correction on the incoming data to cope with differences
   -- between the user clock and the clock recovered from the data.
   rx_elastic_buffer_inst_0 : rx_elastic_buffer port map (
    -- Signals from the GTP on RXRECCLK.
    rxrecclk          => RXRECCLK_0_BUFR,
    reset             => RXRESET_0_REC,
    rxchariscomma_rec => RXCHARISCOMMA_0_REC,
    rxcharisk_rec     => RXCHARISK_0_REC,
    rxdisperr_rec     => RXDISPERR_0_REC,
    rxnotintable_rec  => RXNOTINTABLE_0_REC,
    rxrundisp_rec     => RXRUNDISP_0_REC,
    rxdata_rec        => RXDATA_0_REC,

    -- Signals reclocked onto USRCLK.
    rxusrclk2         => RXUSRCLK2_0,
    rxreset           => RXRESET_0_USR,
    rxchariscomma_usr => RXCHARISCOMMA_0,
    rxcharisk_usr     => RXCHARISK_0_INT,
    rxdisperr_usr     => RXDISPERR_0_INT,
    rxnotintable_usr  => RXNOTINTABLE_0_INT,
    rxrundisp_usr     => RXRUNDISP_0_INT,
    rxclkcorcnt_usr   => RXCLKCORCNT_0,
    rxbuferr          => RXBUFERR_0_INT,
    rxdata_usr        => RXDATA_0_INT
  );

  RXBUFERR_0 <= RXBUFERR_0_INT or RXBUFERR_0_REC;

  -- Resynchronise the RXRESET onto the RXRECCLK domain
  rxrstreclock0 : process(RXRECCLK_0_BUFR, PMARESET)
  begin
    if PMARESET = '1' then
        RXRESET_0_REG  <= '1';
        RXRESET_0_REC  <= '1';
    elsif RXRECCLK_0_BUFR'event and RXRECCLK_0_BUFR = '1' then
        RXRESET_0_REG  <= '0';
        RXRESET_0_REC  <= RXRESET_0_REG;
    end if;
  end process rxrstreclock0;

  -- Resynchronise the RXRESET onto the RXUSRCLK2_0 domain
  rxrstusrreclock0 : process(RXUSRCLK2_0, RXRESET_0)
  begin
    if RXRESET_0 = '1' then
        RXRESET_0_USR_REG  <= '1';
        RXRESET_0_USR      <= '1';
    elsif RXUSRCLK2_0'event and RXUSRCLK2_0 = '1' then
        RXRESET_0_USR_REG  <= '0';
        RXRESET_0_USR      <= RXRESET_0_USR_REG;
    end if;
  end process rxrstusrreclock0;

  -- Re-align signals from the USRCLK domain into the
  -- RXRECCLK domain
  rxrecclkreclock0 : process (RXRECCLK_0_BUFR, RXRESET_0_REC)
  begin
    if RXRESET_0_REC = '1' then
      ENPCOMMAALIGN_0_REG <= '0';
      ENPCOMMAALIGN_0_REC <= '0';
      ENMCOMMAALIGN_0_REG <= '0';
      ENMCOMMAALIGN_0_REC <= '0';
    elsif RXRECCLK_0_BUFR'event and RXRECCLK_0_BUFR = '1' then
      ENPCOMMAALIGN_0_REG <= ENPCOMMAALIGN_0;
      ENPCOMMAALIGN_0_REC <= ENPCOMMAALIGN_0_REG;
      ENMCOMMAALIGN_0_REG <= ENMCOMMAALIGN_0;
      ENMCOMMAALIGN_0_REC <= ENMCOMMAALIGN_0_REG;
    end if;
  end process rxrecclkreclock0;

                       
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


   -- Route RXRECLK0 through a regional clock buffer
   rxrecclk1bufr : BUFR port map (I => RXRECCLK_1, O => RXRECCLK_1_BUFR,
                                   CE => '1', CLR => '0');

   -- Instantiate the RX elastic buffer. This performs clock
   -- correction on the incoming data to cope with differences
   -- between the user clock and the clock recovered from the data.
   rx_elastic_buffer_inst_1 : rx_elastic_buffer port map (
    -- Signals from the GTP on RXRECCLK.
    rxrecclk          => RXRECCLK_1_BUFR,
    reset             => RXRESET_1_REC,
    rxchariscomma_rec => RXCHARISCOMMA_1_REC,
    rxcharisk_rec     => RXCHARISK_1_REC,
    rxdisperr_rec     => RXDISPERR_1_REC,
    rxnotintable_rec  => RXNOTINTABLE_1_REC,
    rxrundisp_rec     => RXRUNDISP_1_REC,
    rxdata_rec        => RXDATA_1_REC,

    -- Signals reclocked onto USRCLK.
    rxusrclk2         => RXUSRCLK2_1,
    rxreset           => RXRESET_1_USR,
    rxchariscomma_usr => RXCHARISCOMMA_1,
    rxcharisk_usr     => RXCHARISK_1_INT,
    rxdisperr_usr     => RXDISPERR_1_INT,
    rxnotintable_usr  => RXNOTINTABLE_1_INT,
    rxrundisp_usr     => RXRUNDISP_1_INT,
    rxclkcorcnt_usr   => RXCLKCORCNT_1,
    rxbuferr          => RXBUFERR_1_INT,
    rxdata_usr        => RXDATA_1_INT
  );

  RXBUFERR_1 <= RXBUFERR_1_INT or RXBUFERR_1_REC;

  -- Resynchronise the RXRESET onto the RXRECCLK domain
  rxrstreclock1 : process(RXRECCLK_1_BUFR, PMARESET)
  begin
    if PMARESET = '1' then
        RXRESET_1_REG  <= '1';
        RXRESET_1_REC  <= '1';
    elsif RXRECCLK_1_BUFR'event and RXRECCLK_1_BUFR = '1' then
        RXRESET_1_REG  <= '0';
        RXRESET_1_REC  <= RXRESET_1_REG;
    end if;
  end process rxrstreclock1;

  -- Resynchronise the RXRESET onto the RXUSRCLK2_1 domain
  rxrstusrreclock1 : process(RXUSRCLK2_1, RXRESET_1)
  begin
    if RXRESET_1 = '1' then
        RXRESET_1_USR_REG  <= '1';
        RXRESET_1_USR      <= '1';
    elsif RXUSRCLK2_1'event and RXUSRCLK2_1 = '1' then
        RXRESET_1_USR_REG  <= '0';
        RXRESET_1_USR      <= RXRESET_1_USR_REG;
    end if;
  end process rxrstusrreclock1;

  -- Re-align signals from the USRCLK domain into the
  -- RXRECCLK domain
  rxrecclkreclock1 : process (RXRECCLK_1_BUFR, RXRESET_1_REC)
  begin
    if RXRESET_1_REC = '1' then
      ENPCOMMAALIGN_1_REG <= '0';
      ENPCOMMAALIGN_1_REC <= '0';
      ENMCOMMAALIGN_1_REG <= '0';
      ENMCOMMAALIGN_1_REC <= '0';
    elsif RXRECCLK_1_BUFR'event and RXRECCLK_1_BUFR = '1' then
      ENPCOMMAALIGN_1_REG <= ENPCOMMAALIGN_1;
      ENPCOMMAALIGN_1_REC <= ENPCOMMAALIGN_1_REG;
      ENMCOMMAALIGN_1_REG <= ENMCOMMAALIGN_1;
      ENMCOMMAALIGN_1_REC <= ENMCOMMAALIGN_1_REG;
    end if;
  end process rxrecclkreclock1;


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
