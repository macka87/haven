-- combov2_xaui_gtx.vhd: XAUI wrapper for Virtex5 FPGAs with GTX transceivers
--                       XAUI line polarity and order can be swapped
-- Copyright (C) 2009 CESNET
-- Author(s): Michal Kajan <kajan@liberouter.org>
--            Stepan Friedl <friedl@liberouter.org>
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
entity combov2_xaui_gtx is
   generic (
      CH01_SWAP : boolean := false; -- TRUE to swap XAUI channals 1 and 2
      CH23_SWAP : boolean := false;  -- TRUE to swap XAUI channals 3 and 4    
      REFCLK_DIFF : boolean := true  -- TRUE to select differential refclk inputs, false to select REFCLK input
   );
   port (
      -- Asynchronous reset
      RESET             : in std_logic;
      -- Clock signal for DRP circuits
      DCLK              : in std_logic;

      -- Reference 156.25 MHz clock
      REFCLK_156_P      : in std_logic := '0';
      REFCLK_156_N      : in std_logic := '1';
      REFCLK_IN         : in std_logic := '0'; -- Use if REFCLK_DIFF is FALSE
      REFCLK_OUT        : out std_logic; -- Reference clock for next GTX tile
      
      -- XAUI interface (4 RX and TX differential RocketIO lanes)
      GTX_RX_P          : in  std_logic_vector( 3 downto 0 );
      GTX_RX_N          : in  std_logic_vector( 3 downto 0 );
      GTX_TX_P          : out std_logic_vector( 3 downto 0 );
      GTX_TX_N          : out std_logic_vector( 3 downto 0 );
      --
      GTX_RXPOLARITY    : in  std_logic_vector( 3 downto 0 ) := "0000"; -- '1' = invert polarity
      GTX_TXPOLARITY    : in  std_logic_vector( 3 downto 0 ) := "0000";
      -- XGMII SDR interface
         -- RX
      XGMII_RXCLK       : out std_logic;
      XGMII_RXD         : out std_logic_vector(63 downto 0);
      XGMII_RXC         : out std_logic_vector( 7 downto 0);
         -- TX
      XGMII_TXCLK       : out std_logic;
      XGMII_TXD         : in  std_logic_vector(63 downto 0);
      XGMII_TXC         : in  std_logic_vector( 7 downto 0)
   );

end entity combov2_xaui_gtx;

-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of combov2_xaui_gtx is

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

   -------------------------    Signals   -----------------------------------
   signal refclk_156    : std_logic;

   signal txoutclk      : std_logic;
   signal txoutclk_bufg : std_logic;

   signal clk156        : std_logic;
   signal reset_156     : std_logic;
   signal reset_156_r1  : std_logic;
   signal reset_156_r2  : std_logic;
   signal xgmii_txd_int : std_logic_vector(63 downto 0);
   signal xgmii_txc_int : std_logic_vector(7 downto 0);
   signal xgmii_rxd_int : std_logic_vector(63 downto 0);
   signal xgmii_rxc_int : std_logic_vector(7 downto 0);
   signal txlock        : std_logic;

begin

   XAUI_CORE_I: entity work.xaui_gtx_block
   generic map(
      WRAPPER_SIM_GTXRESET_SPEEDUP => 0,
      CH01_SWAP => CH01_SWAP,
      CH23_SWAP => CH23_SWAP
   )
   port map(
      -- clock for DCM reset
      dclk                 => DCLK, 

      -- System clock for XAUI core and RocketIO fabric ports (156.25 MHz)
      clk156               => clk156,
      reset156             => reset_156,

      -- Input clock
      refclk               => refclk_156,

      -- 156.25 MHz clock from RocketIO transcievers
      txoutclk             => txoutclk,

      -- Asynchronous reset
      reset                => RESET,

      -- XGMII interface
      xgmii_txd            => xgmii_txd_int,
      xgmii_txc            => xgmii_txc_int,
      xgmii_rxd            => xgmii_rxd_int,
      xgmii_rxc            => xgmii_rxc_int,

      -- XAUI interface
      xaui_tx_l0_p         => GTX_TX_P(0),
      xaui_tx_l0_n         => GTX_TX_N(0),
      xaui_tx_l1_p         => GTX_TX_P(1),
      xaui_tx_l1_n         => GTX_TX_N(1),
      xaui_tx_l2_p         => GTX_TX_P(2),
      xaui_tx_l2_n         => GTX_TX_N(2),
      xaui_tx_l3_p         => GTX_TX_P(3),
      xaui_tx_l3_n         => GTX_TX_N(3),
      xaui_rx_l0_p         => GTX_RX_P(0),
      xaui_rx_l0_n         => GTX_RX_N(0),
      xaui_rx_l1_p         => GTX_RX_P(1),
      xaui_rx_l1_n         => GTX_RX_N(1),
      xaui_rx_l2_p         => GTX_RX_P(2),
      xaui_rx_l2_n         => GTX_RX_N(2),
      xaui_rx_l3_p         => GTX_RX_P(3),
      xaui_rx_l3_n         => GTX_RX_N(3),

      txlock               => txlock,
      signal_detect        => "1111",

      -- Status signals
      align_status         => open,
      sync_status          => open,
      rxpolarity           => GTX_RXPOLARITY,
      txpolarity           => GTX_TXPOLARITY,
      -- RocketIO Dynamic Reconfiguration Port interface
      drp_addr             => (others => '0'),
      drp_en               => (others => '0'),
      drp_i                => (others => '0'),
      drp_o                => open,
      drp_rdy              => open,
      drp_we               => (others => '0'),

      mgt_tx_ready         => open,

      configuration_vector => "0000000",
      status_vector        => open
   );


-- Clock management logic

   GEN_IBUFDS: if (REFCLK_DIFF) generate
      -- Differential clock buffer for RocketIO clock signals
      gtpclk_ibufds : IBUFDS
      port map (
         I  => REFCLK_156_P,
         IB => REFCLK_156_N,
         O  => refclk_156
      );
   end generate;
   
   NO_IBUFDS: if (not REFCLK_DIFF) generate
      refclk_156 <= REFCLK_IN;
   end generate;
   
   REFCLK_OUT <= refclk_156;

   -- Put system clocks on global clock routing
   txoutclk_bufg_i : BUFG
     port map (
       I => txoutclk,
       O => clk156 );

-- reset logic

  p_reset : process (clk156, reset)
  begin
    if reset = '1' then
        reset_156_r1 <= '1';
        reset_156_r2 <= '1';
        reset_156    <= '1';
    elsif clk156'event and clk156 = '1' then
        reset_156_r1 <= '0';
        reset_156_r2 <= reset_156_r1;
        reset_156    <= reset_156_r2;
    end if;
  end process;

   -- Synthesise input and output registers
  p_xgmii_tx_reg : process (clk156)
  begin
    if clk156'event and clk156 = '1' then
      xgmii_txd_int <= xgmii_txd;
      xgmii_txc_int <= xgmii_txc;
    end if;
  end process p_xgmii_tx_reg;

  p_xgmii_rx_reg : process (clk156)
  begin
    if clk156'event and clk156 = '1' then
      xgmii_rxd <= xgmii_rxd_int;
      xgmii_rxc <= xgmii_rxc_int;
    end if;
  end process p_xgmii_rx_reg;
  
   -- mapping of output signals
   XGMII_RXCLK    <= clk156;
   XGMII_TXCLK    <= clk156;

end architecture behavioral;

