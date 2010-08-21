-- combov2_xaui.vhd: Cv2 XAUI wrapper
-- Copyright (C) 2008 CESNET
-- Author(s): Ondrej Lengal <xlenga00@stud.fit.vutbr.cz>
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
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- --------------------------------------------------------------------
--                          Entity declaration
-- --------------------------------------------------------------------
entity combov2_xaui is
   port (
      -- Asynchronous reset
      RESET             : in std_logic;
      -- Clock signal for DCM circuits
      DCLK              : in std_logic;

      -- Reference 156.25 MHz clock
      REFCLK_156_P      : in std_logic;
      REFCLK_156_N      : in std_logic;
      
      -- XAUI interface (4 RX and TX differential RocketIO lanes)
      GTP_RX_P          : in  std_logic_vector( 3 downto 0 );
      GTP_RX_N          : in  std_logic_vector( 3 downto 0 );
      GTP_TX_P          : out std_logic_vector( 3 downto 0 );
      GTP_TX_N          : out std_logic_vector( 3 downto 0 );

      -- XGMII SDR interface
         -- RX
      XGMII_RXCLK          : out std_logic;
      XGMII_RXD            : out std_logic_vector(63 downto 0);
      XGMII_RXC            : out std_logic_vector( 7 downto 0);
         -- TX
      XGMII_TXCLK          : out std_logic;
      XGMII_TXD            : in  std_logic_vector(63 downto 0);
      XGMII_TXC            : in  std_logic_vector( 7 downto 0)
   );

end entity combov2_xaui;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of combov2_xaui is

   --------------------------  Components  ----------------------------------
   component BUFG is
   port (
      I : in  std_logic;
      O : out std_logic
   );
   end component;

   component IBUFDS
   port (
      O  : out std_logic;
      I  : in  std_logic;
      IB : in  std_logic
   );
   end component;

   component DCM_BASE
   generic (
      CLKDV_DIVIDE : real := 2.0;
      CLKFX_DIVIDE : integer := 1;
      CLKFX_MULTIPLY : integer := 4;
      CLKIN_DIVIDE_BY_2 : boolean := FALSE;
      CLKIN_PERIOD : real := 10.0;
      CLKOUT_PHASE_SHIFT : string := "NONE";
      CLK_FEEDBACK : string := "1X";
      DCM_PERFORMANCE_MODE : string := "MAX_SPEED";
      DESKEW_ADJUST : string := "SYSTEM_SYNCHRONOUS";
      DFS_FREQUENCY_MODE : string := "LOW";
      DLL_FREQUENCY_MODE : string := "LOW";
      DUTY_CYCLE_CORRECTION : boolean := TRUE;
      PHASE_SHIFT : integer := 0;
      STARTUP_WAIT : boolean := false
   );
   port (
      CLK0 : out std_ulogic;
      CLK180 : out std_ulogic;
      CLK270 : out std_ulogic;
      CLK2X : out std_ulogic;
      CLK2X180 : out std_ulogic;
      CLK90 : out std_ulogic;
      CLKDV : out std_ulogic;
      CLKFX : out std_ulogic;
      CLKFX180 : out std_ulogic;
      LOCKED : out std_ulogic;
      CLKFB : in std_ulogic;
      CLKIN : in std_ulogic;
      RST : in std_ulogic
   );
   end component;


   -------------------------    Signals   -----------------------------------
   signal dcm_reset           : std_logic;
   signal dcm_reset_r1        : std_logic;
   signal dcm_reset_r2        : std_logic;
   signal clk156_dcm_locked   : std_logic;
   signal dcm_locked_reg      : std_logic;

   signal refclk_156    : std_logic;

   signal txoutclk      : std_logic;
   signal txoutclk_bufg : std_logic;

   signal clk156        : std_logic;
   signal clk156_dcm    : std_logic;
   signal reset156      : std_logic;
   signal reset156_r1   : std_logic;
   signal reset156_r2   : std_logic;

   signal clk312        : std_logic;
   signal clk312_dcm    : std_logic;

   signal txlock        : std_logic;

begin

   --XAUI_CORE_I: xaui_v8_2_block
   XAUI_CORE_I: entity work.xaui_v9_2_block
   generic map(
      WRAPPER_SIM_GTPRESET_SPEEDUP => 1
   )
   port map(
      -- clock for DCM reset
      dclk                 => DCLK,
   
      -- System clock for XAUI core and RocketIO fabric ports (156.25 MHz)
      clk156               => clk156,
      reset156             => reset156,
   
      -- 2x clock for RocketIO (312.5 MHz)
      clk312               => clk312,
   
      -- Input clock
      refclk               => refclk_156,
   
      -- 156.25 MHz clock from RocketIO transcievers
      txoutclk             => txoutclk,
   
      -- Asynchronous reset
      reset                => RESET,
   
      -- XGMII interface
      xgmii_txd            => XGMII_TXD,
      xgmii_txc            => XGMII_TXC,
      xgmii_rxd            => XGMII_RXD,
      xgmii_rxc            => XGMII_RXC,
   
      -- XAUI interface
      xaui_tx_l0_p         => GTP_TX_P(0),
      xaui_tx_l0_n         => GTP_TX_N(0),
      xaui_tx_l1_p         => GTP_TX_P(1),
      xaui_tx_l1_n         => GTP_TX_N(1),
      xaui_tx_l2_p         => GTP_TX_P(2),
      xaui_tx_l2_n         => GTP_TX_N(2),
      xaui_tx_l3_p         => GTP_TX_P(3),
      xaui_tx_l3_n         => GTP_TX_N(3),
      xaui_rx_l0_p         => GTP_RX_P(0),
      xaui_rx_l0_n         => GTP_RX_N(0),
      xaui_rx_l1_p         => GTP_RX_P(1),
      xaui_rx_l1_n         => GTP_RX_N(1),
      xaui_rx_l2_p         => GTP_RX_P(2),
      xaui_rx_l2_n         => GTP_RX_N(2),
      xaui_rx_l3_p         => GTP_RX_P(3),
      xaui_rx_l3_n         => GTP_RX_N(3),
   
      txlock               => txlock,
      signal_detect        => "1111",
   
      -- Status signals
      align_status         => open,
      sync_status          => open,
   
      -- RocketIO Dynamic Reconfiguration Port interface
      drp_addr             => (others => '0'),
      drp_en               => (others => '0'),
      drp_i                => (others => '0'),
      drp_o                => open,
      drp_rdy              => open,
      drp_we               => (others => '0'),
   
      mgt_tx_ready         => open,
   
      -- MDIO interface
      mdc                  => '0',  -- should there be clock signal?
      mdio_in              => '1',
      mdio_out             => open,
      mdio_tri             => open,
      prtad                => "00000",
      type_sel             => "10"
   );

   -- Differential clock buffer for RocketIO clock signals
   gtpclk_ibufds : IBUFDS
    port map (
      I  => REFCLK_156_P,
      IB => REFCLK_156_N,
      O  => refclk_156
   );

   -- Route clock signal from XAUI block to Global Buffer
   txoutclk_bufg_i : BUFG
      port map (
         I => txoutclk,
         O => txoutclk_bufg
      );

   -- DCM for XAUI core
   dcm_clk156 : DCM_BASE
      generic map(
         DFS_FREQUENCY_MODE => "HIGH",
         DLL_FREQUENCY_MODE => "HIGH"
         )
      port map (
         -- reset
         RST      => dcm_reset,

         -- input clock signal
         CLKIN    => txoutclk_bufg,
         -- copy of the input signal
         CLK0     => clk156_dcm,
         -- 2x the input signal
         CLK2X    => clk312_dcm,

         -- feedback of CLK0 from Global Buffer
         CLKFB    => clk156,

         -- is the DCM output signal locked?
         LOCKED   => clk156_dcm_locked,

         -- unused
         CLK90    => open,
         CLK180   => open,
         CLK270   => open,
         CLK2X180 => open,
         CLKDV    => open,
         CLKFX    => open,
         CLKFX180 => open
      );

   -- Route clock signal from DCM to Global Buffer
   clk156_bufg_i : BUFG
      port map (
         I => clk156_dcm,
         O => clk156
      );

   p_dcm_locked : process (clk156, RESET)
   begin
     if RESET = '1' then
       dcm_locked_reg <= '0';
     elsif rising_edge(clk156) then
       dcm_locked_reg <= clk156_dcm_locked;
     end if;
   end process;

   -- Route 2x clock signal from DCM to Global Buffer
   clk312_bufg : BUFG
      port map (
         I => clk312_dcm,
         O => clk312
      );

   -- DCM reset needs to be valid for at least 3 clock cycles
   p_dcm_reset : process (dclk, RESET)
   begin
      if RESET = '1' then
         dcm_reset    <= '1';
         dcm_reset_r1 <= '1';
         dcm_reset_r2 <= '1';
      elsif rising_edge(dclk) then
         dcm_reset_r2 <= not txlock;
         dcm_reset_r1 <= dcm_reset_r2;
         dcm_reset    <= dcm_reset_r1;
      end if;
   end process;
 
   -- reset needs to be valid for at least 3 clock cycles
   p_reset : process (clk156, RESET)
   begin
      if RESET = '1' then
         reset156_r1 <= '1';
         reset156_r2 <= '1';
         reset156    <= '1';
      elsif rising_edge(clk156) then
         reset156_r1 <= not dcm_locked_reg;
         reset156_r2 <= reset156_r1;
         reset156    <= reset156_r2;
      end if;
   end process;

   -- mapping of output signals
   XGMII_RXCLK    <= clk156;
   XGMII_TXCLK    <= clk156;

end architecture behavioral;

