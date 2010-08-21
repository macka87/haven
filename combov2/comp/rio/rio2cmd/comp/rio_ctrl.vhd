
-- rio_ctrl.vhd: 4byte-wide RocketIO Transceiver Controller
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- 
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity rio_ctrl is
   port (
      -- Clock, reset
      REFCLK         : in std_logic;                        -- RocketIO clock
      USRCLK         : in std_logic;                        -- FPGA Fabric Clock
      USRCLK2        : in std_logic;                        -- FPGA Fabric Clock
      RESET          : in std_logic;                        -- Reset Signal

      -- TX
      TXDATA         : in std_logic_vector(31 downto 0);    -- Input Data
      TXCHARISK      : in std_logic_vector(3 downto 0);     -- Signal Comma
      TXRUNDISP      : out std_logic_vector(3 downto 0);    -- Running Disparity of Currently Encoded Data

      -- RX
      RXDATA         : out std_logic_vector(31 downto 0);   -- Output Data
      RXCHARISK      : out std_logic_vector(3 downto 0);    -- Signal Comma
      RXSYNCLOSS     : out std_logic_vector (1 downto 0);   -- State of Sync Logic
      RXCLKCORCNT    : out std_logic_vector(2 downto 0);    -- State of Clock Correction Logic
      RXBUFSTATUS    : out std_logic_vector(1 downto 0);    -- State of Recieve Buffer
      RXCHECKINGCRC  : out std_logic;                       -- This signal indicates if the RXCRCERR is valid
      RXCRCERR       : out std_logic;                       -- CRC Check Error
      RXREALIGN      : out std_logic;                       -- Signals whenever, the serial data is realigned from a comma character
      RXCOMMADET     : out std_logic;                       -- This signal indicates if a comma character has been detected in the serial data.
      RXCHARISCOMMA  : out std_logic_vector(3 downto 0);    -- Signals that a specific byte of RXDATA is a comma character
      RXDISPERR      : out std_logic_vector (3 downto 0);   -- This signal indicates if a diparity error occured


      -- MGT interface
      RXN            : in  std_logic;
      RXP            : in  std_logic;
      TXN            : out std_logic;
      TXP            : out std_logic;
      
      -- Control and status interface
      RXPOLARITY     : in std_logic;                        -- Interchange the RX Polarity
      TXPOLARITY     : in std_logic;                        -- Interchange the TX Polarity
      LOOPBACK       : in std_logic_vector(1 downto 0)      -- Switch Loopback(1) or Normal(0) Mode
   );
end rio_ctrl;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of rio_ctrl is

component rio4 is
   port ( ENMCOMMAALIGN_IN  : in    std_logic; 
          ENPCOMMAALIGN_IN  : in    std_logic; 
          LOOPBACK_IN       : in    std_logic_vector (1 downto 0); 
          POWERDOWN_IN      : in    std_logic; 
          REFCLK_IN         : in    std_logic; 
          RXN_IN            : in    std_logic; 
          RXPOLARITY_IN     : in    std_logic; 
          RXP_IN            : in    std_logic; 
          RXRESET_IN        : in    std_logic; 
          RXUSRCLK_IN       : in    std_logic; 
          RXUSRCLK2_IN      : in    std_logic; 
          TXCHARDISPMODE_IN : in    std_logic_vector (3 downto 0); 
          TXCHARDISPVAL_IN  : in    std_logic_vector (3 downto 0); 
          TXCHARISK_IN      : in    std_logic_vector (3 downto 0); 
          TXDATA_IN         : in    std_logic_vector (31 downto 0); 
          TXFORCECRCERR_IN  : in    std_logic;
          TXINHIBIT_IN      : in    std_logic; 
          TXPOLARITY_IN     : in    std_logic; 
          TXRESET_IN        : in    std_logic; 
          TXUSRCLK_IN       : in    std_logic; 
          TXUSRCLK2_IN      : in    std_logic; 
          RXBUFSTATUS_OUT   : out   std_logic_vector (1 downto 0); 
          RXCHARISCOMMA_OUT : out   std_logic_vector (3 downto 0); 
          RXCHARISK_OUT     : out   std_logic_vector (3 downto 0); 
          RXCHECKINGCRC_OUT : out   std_logic; 
          RXCLKCORCNT_OUT   : out   std_logic_vector (2 downto 0); 
          RXCOMMADET_OUT    : out   std_logic; 
          RXCRCERR_OUT      : out   std_logic; 
          RXDATA_OUT        : out   std_logic_vector (31 downto 0); 
          RXDISPERR_OUT     : out   std_logic_vector (3 downto 0); 
          RXLOSSOFSYNC_OUT  : out   std_logic_vector (1 downto 0); 
          RXNOTINTABLE_OUT  : out   std_logic_vector (3 downto 0); 
          RXREALIGN_OUT     : out   std_logic; 
          RXRECCLK_OUT      : out   std_logic; 
          RXRUNDISP_OUT     : out   std_logic_vector (3 downto 0); 
          TXBUFERR_OUT      : out   std_logic; 
          TXKERR_OUT        : out   std_logic_vector (3 downto 0); 
          TXN_OUT           : out   std_logic; 
          TXP_OUT           : out   std_logic; 
          TXRUNDISP_OUT     : out   std_logic_vector (3 downto 0));
end component;

-- common signals
signal pwr     : std_logic;
signal gnd     : std_logic;
signal gnd4    : std_logic_vector(3 downto 0);

-- debug signals (not assigned anywhere)
signal rxnotintable  : std_logic_vector (3 downto 0);
signal rxrecclk      : std_logic;
signal rxrundisp     : std_logic_vector (3 downto 0);
signal txbuferr      : std_logic;
signal txkerr        : std_logic_vector (3 downto 0);

begin

pwr <= '1';
gnd <= '0';
gnd4 <= "0000";

rio_gen: rio4
   port map( 
--          BREFCLK_IN        => BREFCLK,
          ENMCOMMAALIGN_IN  => pwr,
          ENPCOMMAALIGN_IN  => pwr,
          LOOPBACK_IN       => LOOPBACK,
          POWERDOWN_IN      => gnd,
          REFCLK_IN         => REFCLK,
          RXN_IN            => RXN,
          RXPOLARITY_IN     => RXPOLARITY,
          RXP_IN            => RXP,
          RXRESET_IN        => RESET,
          RXUSRCLK_IN       => USRCLK,
          RXUSRCLK2_IN      => USRCLK2,
          TXCHARDISPMODE_IN => gnd4,
          TXCHARDISPVAL_IN  => gnd4,
          TXCHARISK_IN      => TXCHARISK,
          TXDATA_IN         => TXDATA,
          TXFORCECRCERR_IN  => gnd,
          TXINHIBIT_IN      => gnd,
          TXPOLARITY_IN     => TXPOLARITY,
          TXRESET_IN        => RESET,
          TXUSRCLK_IN       => USRCLK,
          TXUSRCLK2_IN      => USRCLK2,
          RXBUFSTATUS_OUT   => RXBUFSTATUS,
          RXCHARISCOMMA_OUT => RXCHARISCOMMA,
          RXCHARISK_OUT     => RXCHARISK,
          RXCHECKINGCRC_OUT => RXCHECKINGCRC,
          RXCLKCORCNT_OUT   => RXCLKCORCNT,
          RXCOMMADET_OUT    => RXCOMMADET,
          RXCRCERR_OUT      => RXCRCERR,
          RXDATA_OUT        => RXDATA,
          RXDISPERR_OUT     => RXDISPERR,
          RXLOSSOFSYNC_OUT  => RXSYNCLOSS,
          RXNOTINTABLE_OUT  => rxnotintable,
          RXREALIGN_OUT     => RXREALIGN,
          RXRECCLK_OUT      => rxrecclk,
          RXRUNDISP_OUT     => rxrundisp,
          TXBUFERR_OUT      => txbuferr,
          TXKERR_OUT        => txkerr,
          TXN_OUT           => TXN,
          TXP_OUT           => TXP,
          TXRUNDISP_OUT     => TXRUNDISP
          );

end behavioral;


