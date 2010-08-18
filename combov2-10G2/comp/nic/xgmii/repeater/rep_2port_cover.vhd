-- rep_2port_cover.vhd: This component encapsulates TX DCM clock management
--                      component, XGMII Receivers and Transmitters and
--                      Repeater.
--                
--                
--
-- Copyright (C) 2008 CESNET
-- Author(s): Michal Kajan <kajan@liberouter.org>
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
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--pragma translate_off
library unisim;
use unisim.vcomponents.all;
--pragma translate_on

-- ----------------------------------------------------------------------------
--  Entity declaration: REP_2PORT_COVER
-- ---------------------------------------------------------------------------- 
entity rep_2port_cover is
   port(
      ECLK           : in  std_logic;
      RESET_GLOBAL   : in  std_logic;
      RESET_IBUF_IFC : out std_logic;
   
      -- XGMII Receiver A input
      RXCLKA     : in  std_logic;
      RXDA       : in  std_logic_vector(31 downto 0);
      RXCA       : in  std_logic_vector(3 downto 0);

      -- XGMII Receiver B input 
      RXCLKB     : in  std_logic;                     
      RXDB       : in  std_logic_vector(31 downto 0);
      RXCB       : in  std_logic_vector(3 downto 0);
   
      -- packet forwarding enable
      EN0        : in  std_logic;
      EN1        : in  std_logic;

      -- FIFO overflow indicator
      OVERFLOW0  : out std_logic;
      OVERFLOW1  : out std_logic;

      -- FIFO underflow indicator
      UNDERFLOW0 : out std_logic;
      UNDERFLOW1 : out std_logic;

      -- XGMII Transmitter A output
      TXCLKA     : out std_logic;
      TXDA       : out std_logic_vector(31 downto 0);
      TXCA       : out std_logic_vector(3 downto 0);

      -- XGMII Transmitter B output
      TXCLKB     : out std_logic;
      TXDB       : out std_logic_vector(31 downto 0);
      TXCB       : out std_logic_vector(3 downto 0);

      -- XGMII Receiver A output
      IBUF0_CLK  : out std_logic;
      IBUF0_DATA : out std_logic_vector(63 downto 0);
      IBUF0_CMD  : out std_logic_vector(7 downto 0);
   
      -- XGMII Receiver B output
      IBUF1_CLK  : out std_logic;
      IBUF1_DATA : out std_logic_vector(63 downto 0);
      IBUF1_CMD  : out std_logic_vector(7 downto 0)
   );
end entity rep_2port_cover;

-- ----------------------------------------------------------------------------
--  Architecture declaration: REP_2PORT_TOP_ARCH
-- ---------------------------------------------------------------------------- 
architecture rep_2port_cover_arch of rep_2port_cover is 

   component DCM
   port (
      CLKIN    : in  std_ulogic := '0';
      CLKFB    : in  std_ulogic := '0';
      DSSEN    : in  std_ulogic := '0';
      PSINCDEC : in  std_ulogic := '0';
      PSEN     : in  std_ulogic := '0';
      PSCLK    : in  std_ulogic := '0';
      RST      : in  std_ulogic := '0';
      CLK0     : out std_ulogic := '0';
      CLK90    : out std_ulogic := '0';
      CLK180   : out std_ulogic := '0';
      CLK270   : out std_ulogic := '0';
      CLK2X    : out std_ulogic := '0';
      CLK2X180 : out std_ulogic := '0';
      CLKDV    : out std_ulogic := '0';
      CLKFX    : out std_ulogic := '0';
      CLKFX180 : out std_ulogic := '0';
      LOCKED   : out std_ulogic := '0';
      PSDONE   : out std_ulogic := '0';
      STATUS   : out std_logic_vector(7 downto 0) := "00000000"
   );
   end component;

   component IBUFGDS
   port(
      I  : in std_logic;
      IB : in std_logic;
      O  : out std_logic
    );
    end component;
    
   component OBUFDS
   port(
      I  : in std_logic;
      OB : out std_logic;
      O  : out std_logic
    );
    end component;
          
   component IBUFG
   port(
      I  : in std_logic;
      O  : out std_logic
    );
   end component;   
   
   component OBUF
   port(
      I  : in std_logic;
      O  : out std_logic
    );
   end component;       
   
   component BUFG
   port(
      O   : out STD_LOGIC;
      I   : in  STD_LOGIC
    );
   end component;

   signal rxclk0        : std_logic;
   signal rxclk1        : std_logic;
   signal tx_clk        : std_logic;
   signal tx_clk_dcm    : std_logic;
   signal tx_clk90      : std_logic;
   signal tx_clk180_dcm : std_logic;
   signal tx_clk180     : std_logic;
   signal tx_clk90_dcm  : std_logic;
   signal tx_clk270_dcm : std_logic;
   signal tx_clk270     : std_logic;

   signal porta_tx_d      : std_logic_vector(63 downto 0);
   signal porta_tx_c      : std_logic_vector(7 downto 0);
   signal portb_tx_d      : std_logic_vector(63 downto 0);
   signal portb_tx_c      : std_logic_vector(7 downto 0);
   signal rx_data_a       : std_logic_vector(63 downto 0) := (Others => '0');   
   signal rx_cmd_a        : std_logic_vector(7 downto 0); 
   signal rx_data_b       : std_logic_vector(63 downto 0) := (Others => '0');   
   signal rx_cmd_b        : std_logic_vector(7 downto 0); 
   signal reg_rx_data_a   : std_logic_vector(63 downto 0) := (Others => '0');   
   signal reg_rx_cmd_a    : std_logic_vector(7 downto 0);
   signal reg_rx_data_b   : std_logic_vector(63 downto 0) := (Others => '0');   
   signal reg_rx_cmd_b    : std_logic_vector(7 downto 0); 

   signal tx_dcm_lock     : std_logic;
   signal rx_dcm_lock_a   : std_logic;
   signal rx_dcm_lock_b   : std_logic;
   signal rxreset_a       : std_logic;
   signal rxreset_b       : std_logic;
   signal reset_a         : std_logic;
   signal reset_b         : std_logic;
   signal reset_ab        : std_logic;
   signal reset           : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                  XGMII clocking
   -- -------------------------------------------------------------------------

   
   -- TX clock for TX DDR data must be shared for both channels, thus I removed 
   -- the DCM from the XGMII_TX component 

   
   TX_CLK_MANAGEMENT : DCM
   port map (
      CLKIN    => ECLK,
      CLKFB    => tx_clk,
      RST      => RESET_GLOBAL,
      DSSEN    => '0',
      PSINCDEC => '0',
      PSEN     => '0',
      PSCLK    => '0',
      CLK0     => tx_clk_dcm,
      CLK90    => tx_clk90_dcm, 
      CLK180   => tx_clk180_dcm,
      CLK270   => tx_clk270_dcm,
      CLK2X    => OPEN,
      CLK2X180 => OPEN,
      CLKDV    => OPEN,
      CLKFX    => OPEN,
      CLKFX180 => OPEN,
      LOCKED   => tx_dcm_lock,
      STATUS   => OPEN,
      PSDONE   => OPEN
   );

   -- Route clocks onto a Global Routing Network
   TXCLK_BUFG0   : BUFG port map(I  => tx_clk_dcm,    O => tx_clk);
   TXCLK_BUFG90  : BUFG port map(I  => tx_clk90_dcm,  O => tx_clk90);
   TXCLK_BUFG180 : BUFG port map(I  => tx_clk180_dcm, O => tx_clk180);
   TXCLK_BUFG270 : BUFG port map(I  => tx_clk270_dcm, O => tx_clk270);

   -- -------------------------------------------------------------------------
   --                         XGMII RX & TX
   -- -------------------------------------------------------------------------
   
   -- Channel A   -------------------------------------------------------------
   XGMII_RECEIVER_A: entity work.XGMII_RX
   port map (
      XGMII_RX_CLK => RXCLKA,
      XGMII_RXD    => RXDA,
      XGMII_RXC    => RXCA,
      RESET        => '0', 
      RX_CLK_INT   => rxclk0,
      RXD_INT      => rx_data_a,
      RXC_INT      => rx_cmd_a,
      RX_DCM_LOCK  => rx_dcm_lock_a,
      RX_DCM_RESET => RESET_GLOBAL
   );

   -- 
   RXREGS_A: process(rxclk0)
   begin
      if rxclk0'event and rxclk0 = '1' then
          reg_rx_data_a <= rx_data_a;
          reg_rx_cmd_a  <= rx_cmd_a;
      end if;
   end process;

   -- connecting XGMII Receiver A output to IBUF0 output 
   IBUF0_CLK  <= rxclk0;
   IBUF0_DATA <= reg_rx_data_a;
   IBUF0_CMD  <= reg_rx_cmd_a;


   XGMII_TRANSMITTER_A: entity work.XGMII_TX(RTL_NO_DCM)
   port map (
      XGMII_TX_CLK  => TXCLKA,    -- XGMII output clock
      XGMII_TXD     => TXDA,      -- XGMII Data
      XGMII_TXC     => TXCA,      -- XGMII Commands
      RESET         => '0',       -- 
      TX_CLK0       => tx_clk,    -- Internal TX_CLK (Tx synchronous logic)
      TX_CLK90      => tx_clk90,  -- 
      TX_CLK180     => tx_clk180, --       
      TX_CLK270     => tx_clk270, --       
      TXD_INT       => porta_tx_d,
      TXC_INT       => porta_tx_c
   );
         
   -- Channel B   ---------------------------------------------------------
   XGMII_RECEIVER_B: entity work.XGMII_RX
   port map (
      XGMII_RX_CLK => RXCLKB,
      XGMII_RXD    => RXDB,
      XGMII_RXC    => RXCB,
      RESET        => '0', 
      RX_CLK_INT   => rxclk1,
      RXD_INT      => rx_data_b,
      RXC_INT      => rx_cmd_b,
      RX_DCM_LOCK  => rx_dcm_lock_b,
      RX_DCM_RESET => RESET_GLOBAL
   );
   
   RXREGS_B: process(rxclk1)
   begin
      if rxclk1'event and rxclk1 = '1' then
         reg_rx_data_b <= rx_data_b;
         reg_rx_cmd_b  <= rx_cmd_b;
      end if;
   end process;
    
   -- connecting XGMII Receiver B output to IBUF1 output
   IBUF1_CLK  <= rxclk1; 
   IBUF1_DATA <= reg_rx_data_b;
   IBUF1_CMD  <= reg_rx_cmd_b;

    
   XGMII_TRANSMITTER_B: entity work.XGMII_TX(RTL_NO_DCM)
   port map (
      XGMII_TX_CLK  => TXCLKB,      -- XGMII output clock
      XGMII_TXD     => TXDB,        -- XGMII Data
      XGMII_TXC     => TXCB,        -- XGMII Commands
      RESET         => '0',
      TX_CLK0       => tx_clk,      -- Internal TX_CLK (use for Tx synchronous logic). 
      TX_CLK90      => tx_clk90,      
      TX_CLK180     => tx_clk180,   --
      TX_CLK270     => tx_clk270,
      TXD_INT       => portb_tx_d,
      TXC_INT       => portb_tx_c
   );       


   -- Resets -----------------------------------------------------------------
   rxreset_a <= not rx_dcm_lock_a;
   reset_a   <= rxreset_a or (not tx_dcm_lock);
   rxreset_b <= not rx_dcm_lock_b;
   reset_b   <= rxreset_b or (not tx_dcm_lock);
   reset_ab  <= reset_a or reset_b;   

   RESET_IBUF_IFC <= reset_ab;
   


   -- ----------------------------------------------------------------------------
   --                            Repeater
   -- ----------------------------------------------------------------------------
  
   REPEATER: entity work.xgmii_rep_2port 
   port map (
      RESET      => reset_ab,
      -- Port 0 -------------
      EN0        => EN0,        -- '0' disables port0 -> port1 forwarding
      OVERFLOW0  => OVERFLOW0,
      UNDERFLOW0 => UNDERFLOW0,
       -- XGMII interface
      RX_CLK0    => rxclk0,     -- 
      RX_D0      => reg_rx_data_a,
      RX_C0      => reg_rx_cmd_a,
      TX_CLK0    => tx_clk,
      TX_D0      => porta_tx_d, -- Forwarded data from port 1 (RX_D1)
      TX_C0      => porta_tx_c, -- Forwarded cmd from port 0
      -- Port 1 -------------
      EN1        => EN1,        -- '0' disables port1 -> port0 forwarding
      OVERFLOW1  => OVERFLOW1,
      UNDERFLOW1 => UNDERFLOW1,
       -- XGMII interface
      RX_CLK1    => rxclk1,
      RX_D1      => reg_rx_data_b,
      RX_C1      => reg_rx_cmd_b,
      TX_CLK1    => tx_clk,
      TX_D1      => portb_tx_d, -- Forwarded data from port 0 (RX_D0)
      TX_C1      => portb_tx_c  -- Forwarded cmd from port 0
   ); 

end architecture rep_2port_cover_arch;

