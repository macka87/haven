-- top_level.vhd: Top Level for SFPRO card
-- Copyright (C) 2003 CESNET
-- Author(s): Tomas Filip  <flipflop@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--pragma translate_off
library unisim;
use unisim.vcomponents.all;
--pragma translate_on

use work.ifc_addr_space.all;
use work.ifc_constants.all;
use work.math_pack.all;
use work.ibuf_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture sfp_arch of SFPRO is

constant ID_SW_MAJOR     : std_logic_vector( 7 downto 0):=   X"00";
constant ID_SW_MINOR     : std_logic_vector( 7 downto 0):=   X"01";
constant ID_HW_MAJOR     : std_logic_vector(15 downto 0):= X"0001";
constant ID_HW_MINOR     : std_logic_vector(15 downto 0):= X"0000"; 

-- --------------------------- Clk generation -----------------------------
-- Clock Buffer
component BUFG is
      port (
         I : in  std_logic;
         O : out std_logic
      );
end component;

component IBUFGDS is
      port (
		I  : in  std_logic;
		IB : in  std_logic;
		O  : out std_logic
      );
end component;

component FDDRRSE
   port(
      Q       : out std_logic;
      D0      : in std_logic;
      D1      : in std_logic;
      C0      : in std_logic;
      C1      : in std_logic;
      CE      : in std_logic;
      R       : in std_logic;
      S       : in std_logic
   );
end component;

component CLK_GEN is
   Port (
      -- Input
      CLK         : in  std_logic;  -- Input clock frequency
      RESET       : in  std_logic;  -- Global reset signal
      -- Output
      CLK1X       : out std_logic;  -- 1X output clock
      CLK2X       : out std_logic;  -- 2X output clock
      LOCK        : out std_logic   -- Lock signal
   );
end component CLK_GEN;

-- -------------------- Local bus  - interface ----------------------
component LB_BRIDGE is
   Generic (
      IN_TRISTATES : boolean := true -- always leave TRUE for on-chip use
      -- when FALSE, doesn't use tristate drivers for LBHOLDA_IN and LBRDY_IN
   );
   Port (
      -- local bus interconnection
      RESET      : IN std_logic;
      LBCLK      : IN std_logic;

      -- Local bus input (to card interface - IOS bus)
      LBFRAME_IN : IN std_logic;
      LBAS_IN    : IN std_logic;
      LBRW_IN    : IN std_logic;
      LBLAST_IN  : IN std_logic;
      LBAD_IN    : INOUT std_logic_vector(15 downto 0);
      LBHOLDA_IN : OUT std_logic;
      LBRDY_IN   : OUT std_logic;
      -- Local bus output (to another card)
      LBFRAME_OUT: OUT std_logic;
      LBAS_OUT   : OUT std_logic;
      LBRW_OUT   : OUT std_logic;
      LBLAST_OUT : OUT std_logic;
      LBAD_OUT   : INOUT std_logic_vector(15 downto 0);
      LBHOLDA_OUT: IN std_logic;
      LBRDY_OUT  : IN std_logic
   );
end component;

-- --------------------------- ID component -------------------------------
component ID_COMP_LB is
   generic (
      BASE           : integer := 0;
      USE_HIGH_LOGIC : boolean := false;
   
      PROJECT_ID     : std_logic_vector(15 downto 0):= X"0000";
      SW_MAJOR       : std_logic_vector( 7 downto 0):=   X"00";
      SW_MINOR       : std_logic_vector( 7 downto 0):=   X"00";
      HW_MAJOR       : std_logic_vector(15 downto 0):= X"0000";
      HW_MINOR       : std_logic_vector(15 downto 0):= X"0000";
      PROJECT_TEXT   : std_logic_vector(255 downto 0) :=
      X"0000000000000000000000000000000000000000000000000000000000000000"
   ); 
   port (
      RESET    : in std_logic;
      
      LBCLK     : in    std_logic;  -- internal bus clock, up to 100 MHz
      LBFRAME   : in    std_logic;  -- Frame
      LBHOLDA   : out   std_logic;  -- Hold Ack
      LBAD      : inout std_logic_vector(15 downto 0); -- Address/Data
      LBAS      : in    std_logic;  -- Adress strobe
      LBRW      : in    std_logic;  -- Direction (Read#/Write, low : read)
      LBRDY     : out   std_logic;  -- Ready
      LBLAST    : in    std_logic   -- Last word in transfer
);
end component ID_COMP_LB;

-- -------------------------- DCM ---------------------------------
component DCM
   -- pragma translate_off
   generic (
      DFS_FREQUENCY_MODE : string := "LOW";
      DLL_FREQUENCY_MODE : string := "LOW";
      DUTY_CYCLE_CORRECTION : boolean := TRUE;
      CLKFX_DIVIDE : integer := 1;
      CLKFX_MULTIPLY : integer := 4 ;
      STARTUP_WAIT : boolean := FALSE;
      CLKDV_DIVIDE : real := 2.0
   );
   -- pragma translate_on
port (
      CLKIN     : in  std_logic;
      CLKFB     : in  std_logic;
      RST       : in  std_logic;
      CLK0      : out std_logic;
      CLK90     : out std_logic;
      CLK180    : out std_logic;
      CLK2X     : out std_logic;
      CLK2X180  : out std_logic;
      CLKDV     : out std_logic;
      CLKFX     : out std_logic;
      CLKFX180  : out std_logic;
      LOCKED    : out std_logic;
      PSDONE    : out std_logic;
      STATUS    : out std_logic_vector(7 downto 0)
   );
end component;

-- -------------------------- IBUF ---------------------------------
component ibuf_gmii_top4 is
   generic(
      ADDR_BASE   : integer;
      DATA_PATHS  : integer;     -- Output data width in bytes
      DFIFO_SIZE  : integer;     -- Packet data fifo size
      HFIFO_SIZE  : integer;     -- Control fifo size
      MACS        : integer := 16-- Number of MAC addresses (up to 16)
   );
   port(

      -- ---------------- Control signal -----------------
      RESET         : in  std_logic;

      -- ------------------------------------------------
      -- -------------- IBUF interfaces -----------------
      
      -- -----------
      -- INTERFACE 0
      
      -- GMII RX interface
      IBUF0_RXCLK     : in  std_logic;
      IBUF0_RXD       : in  std_logic_vector(7 downto 0);
      IBUF0_RXDV      : in  std_logic;
      IBUF0_RXER      : in  std_logic;

      -- PHY status interface
      PHY0_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      PHY0_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      PHY0_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      PHY0_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                             -- 1: SGMII mode active, the PHY status ports are valid
      -- PACODAG interface
      IBUF0_CTRL_CLK    : out std_logic;
      IBUF0_CTRL_DATA        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF0_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF0_CTRL_SRC_RDY_N : in std_logic;
      IBUF0_CTRL_SOP_N     : in std_logic;
      IBUF0_CTRL_EOP_N     : in std_logic;
      IBUF0_CTRL_DST_RDY_N : out std_logic;
      IBUF0_CTRL_HDR_EN : in std_logic; -- Enables Packet Headers
      IBUF0_CTRL_FTR_EN : in std_logic; -- Enables Packet Footers

      -- IBUF status interface
      IBUF0_SOP         : out std_logic;
      IBUF0_STAT        : out t_ibuf_stat;
      IBUF0_STAT_DV     : out std_logic;

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT : in std_logic;
      IBUF0_SAU_DV     : in std_logic;

      -- FrameLink interface
      IBUF0_RDCLK      : in  std_logic;
      IBUF0_DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF0_DREM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF0_SRC_RDY_N  : out std_logic;
      IBUF0_SOF_N      : out std_logic;
      IBUF0_SOP_N      : out std_logic;
      IBUF0_EOF_N      : out std_logic;
      IBUF0_EOP_N      : out std_logic;
      IBUF0_DST_RDY_N  : in std_logic;

      -- -----------
      -- INTERFACE 1
      
      -- GMII RX interface
      IBUF1_RXCLK     : in  std_logic;
      IBUF1_RXD       : in  std_logic_vector(7 downto 0);
      IBUF1_RXDV      : in  std_logic;
      IBUF1_RXER      : in  std_logic;

      -- PHY status interface
      PHY1_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      PHY1_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      PHY1_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      PHY1_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                             -- 1: SGMII mode active, the PHY status ports are valid
      -- PACODAG interface
      IBUF1_CTRL_CLK    : out std_logic;
      IBUF1_CTRL_DATA        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF1_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF1_CTRL_SRC_RDY_N : in std_logic;
      IBUF1_CTRL_SOP_N     : in std_logic;
      IBUF1_CTRL_EOP_N     : in std_logic;
      IBUF1_CTRL_DST_RDY_N : out std_logic;
      IBUF1_CTRL_HDR_EN : in std_logic; -- Enables Packet Headers
      IBUF1_CTRL_FTR_EN : in std_logic; -- Enables Packet Footers

      -- IBUF status interface
      IBUF1_SOP         : out std_logic;
      IBUF1_STAT        : out t_ibuf_stat;
      IBUF1_STAT_DV     : out std_logic;

      -- Sampling unit interface
      IBUF1_SAU_ACCEPT : in std_logic;
      IBUF1_SAU_DV     : in std_logic;

      -- FrameLink interface
      IBUF1_RDCLK      : in  std_logic;
      IBUF1_DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF1_DREM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF1_SRC_RDY_N  : out std_logic;
      IBUF1_SOF_N      : out std_logic;
      IBUF1_SOP_N      : out std_logic;
      IBUF1_EOF_N      : out std_logic;
      IBUF1_EOP_N      : out std_logic;
      IBUF1_DST_RDY_N  : in std_logic;

      -- -----------
      -- INTERFACE 2
      
      -- GMII RX interface
      IBUF2_RXCLK     : in  std_logic;
      IBUF2_RXD       : in  std_logic_vector(7 downto 0);
      IBUF2_RXDV      : in  std_logic;
      IBUF2_RXER      : in  std_logic;

      -- PHY status interface
      PHY2_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      PHY2_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      PHY2_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      PHY2_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                             -- 1: SGMII mode active, the PHY status ports are valid
      -- PACODAG interface
      IBUF2_CTRL_CLK    : out std_logic;
      IBUF2_CTRL_DATA        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF2_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF2_CTRL_SRC_RDY_N : in std_logic;
      IBUF2_CTRL_SOP_N     : in std_logic;
      IBUF2_CTRL_EOP_N     : in std_logic;
      IBUF2_CTRL_DST_RDY_N : out std_logic;
      IBUF2_CTRL_HDR_EN : in std_logic; -- Enables Packet Headers
      IBUF2_CTRL_FTR_EN : in std_logic; -- Enables Packet Footers

      -- IBUF status interface
      IBUF2_SOP         : out std_logic;
      IBUF2_STAT        : out t_ibuf_stat;
      IBUF2_STAT_DV     : out std_logic;

      -- Sampling unit interface
      IBUF2_SAU_ACCEPT : in std_logic;
      IBUF2_SAU_DV     : in std_logic;

      -- FrameLink interface
      IBUF2_RDCLK      : in  std_logic;
      IBUF2_DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF2_DREM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF2_SRC_RDY_N  : out std_logic;
      IBUF2_SOF_N      : out std_logic;
      IBUF2_SOP_N      : out std_logic;
      IBUF2_EOF_N      : out std_logic;
      IBUF2_EOP_N      : out std_logic;
      IBUF2_DST_RDY_N  : in std_logic;

      -- -----------
      -- INTERFACE 3
      
      -- GMII RX interface
      IBUF3_RXCLK     : in  std_logic;
      IBUF3_RXD       : in  std_logic_vector(7 downto 0);
      IBUF3_RXDV      : in  std_logic;
      IBUF3_RXER      : in  std_logic;

      -- PHY status interface
      PHY3_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      PHY3_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      PHY3_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      PHY3_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                             -- 1: SGMII mode active, the PHY status ports are valid
      -- PACODAG interface
      IBUF3_CTRL_CLK    : out std_logic;
      IBUF3_CTRL_DATA        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF3_CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF3_CTRL_SRC_RDY_N : in std_logic;
      IBUF3_CTRL_SOP_N     : in std_logic;
      IBUF3_CTRL_EOP_N     : in std_logic;
      IBUF3_CTRL_DST_RDY_N : out std_logic;
      IBUF3_CTRL_HDR_EN : in std_logic; -- Enables Packet Headers
      IBUF3_CTRL_FTR_EN : in std_logic; -- Enables Packet Footers

      -- IBUF status interface
      IBUF3_SOP         : out std_logic;
      IBUF3_STAT        : out t_ibuf_stat;
      IBUF3_STAT_DV     : out std_logic;

      -- Sampling unit interface
      IBUF3_SAU_ACCEPT : in std_logic;
      IBUF3_SAU_DV     : in std_logic;

      -- FrameLink interface
      IBUF3_RDCLK      : in  std_logic;
      IBUF3_DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      IBUF3_DREM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      IBUF3_SRC_RDY_N  : out std_logic;
      IBUF3_SOF_N      : out std_logic;
      IBUF3_SOP_N      : out std_logic;
      IBUF3_EOF_N      : out std_logic;
      IBUF3_EOP_N      : out std_logic;
      IBUF3_DST_RDY_N  : in std_logic;

      -- ------------------------------------------------
      -- ---------- Internal bus signals ----------------
      LBCLK	     : in    std_logic;
      LBFRAME	     : in    std_logic;
      LBHOLDA	     : out   std_logic;
      LBAD	     : inout std_logic_vector(15 downto 0);
      LBAS	     : in    std_logic;
      LBRW	     : in    std_logic;
      LBRDY	     : out   std_logic;
      LBLAST	     : in    std_logic
   );
end component;

-- -------------------------- IBUF_TEST ---------------------------------
component ibuf_test is
   generic(
      ADDR_BASE   : integer;
      DATA_PATHS  : integer;     -- Output data width in bytes
      FIFO_SIZE   : integer      -- Packet fifo size
   );

   port (
      RESET    : in std_logic;

      DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      SRC_RDY_N  : in std_logic;
      SOF_N      : in std_logic;
      SOP_N      : in std_logic;
      EOF_N      : in std_logic;
      EOP_N      : in std_logic;
      DST_RDY_N  : out std_logic;

      -- PACODAG interface
      CTRL_CLK    : in   std_logic;
      CTRL_DI        : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      CTRL_REM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      CTRL_SRC_RDY_N : out std_logic;
      CTRL_SOP_N     : out std_logic;
      CTRL_EOP_N     : out std_logic;
      CTRL_DST_RDY_N : in std_logic;
      CTRL_HDR_EN : out std_logic; -- Enables Packet Headers
      CTRL_FTR_EN : out std_logic; -- Enables Packet Footers

      -- IBUF status interface
      SOP         : in   std_logic;

      -- Sampling unit interface
      SAU_ACCEPT : out    std_logic;
      SAU_DV     : out    std_logic;

      -- ------------------------------------------------
      -- ---------- Internal bus signals ----------------
      LBCLK	     : in    std_logic;
      LBFRAME	     : in    std_logic;
      LBHOLDA	     : out   std_logic;
      LBAD	     : inout std_logic_vector(15 downto 0);
      LBAS	     : in    std_logic;
      LBRW	     : in    std_logic;
      LBRDY	     : out   std_logic;
      LBLAST	     : in    std_logic
   );
end component;

-- *****************************   End of Components parts   *******************************************
-- *****************************************************************************************************

 -- Global Signals....

   constant DATA_PATHS        : integer := 2;
   
   signal ios_lbclk           : std_logic;
   signal ios_reset           : std_logic;
   signal reset               : std_logic;
   signal clk50               : std_logic;
   signal ethclk              : std_logic;
   signal fclk0               : std_logic;
   signal fclk0_bufg          : std_logic;
   signal usr_clk             : std_logic;
   signal usr_clk_bufg        : std_logic;
   signal usr_clk2            : std_logic;
   signal usr_clk2_n          : std_logic;
   signal usr_clk2_bufg       : std_logic;

   signal clkgen_lock            : std_logic;
   signal lock_rio              : std_logic;
   signal lock_lb                : std_logic;

   signal gmii_rxd0           : std_logic_vector(7 downto 0);
   signal gmii_rxdv0          : std_logic;
   signal gmii_rxer0          : std_logic;

   signal ibuf0_ctrl_clk      : std_logic;
   signal ibuf0_ctrl_di    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf0_ctrl_src_rdy_n    : std_logic;
   signal ibuf0_ctrl_rem      : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf0_ctrl_sop_n      : std_logic;
   signal ibuf0_ctrl_eop_n      : std_logic;
   signal ibuf0_ctrl_dst_rdy_n    : std_logic;
   signal ibuf0_ctrl_hdr_en      : std_logic;
   signal ibuf0_ctrl_ftr_en      : std_logic;

      -- IBUF status interface
   signal ibuf0_sop     : std_logic;
   signal ibuf0_stat    : t_ibuf_stat;
   signal ibuf0_stat_dv    : std_logic;

   signal phy0_link_status    : std_logic;
   signal phy0_duplex_mode    : std_logic;
   signal phy0_speed    : std_logic_vector(1 downto 0);
   signal phy0_sgmii    : std_logic;
      -- Sampling unit interface
   signal ibuf0_sau_accept    : std_logic;
   signal ibuf0_sau_dv     : std_logic;

      -- FrameLink interface
   signal ibuf0_data    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf0_drem    : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf0_src_rdy_n     : std_logic;
   signal ibuf0_sof_n      : std_logic;
   signal ibuf0_sop_n      : std_logic;
   signal ibuf0_eof_n      : std_logic;
   signal ibuf0_eop_n      : std_logic;
   signal ibuf0_dst_rdy_n     : std_logic;

   -- Local bus
   signal lbframe             : std_logic;
   signal lbas                : std_logic;
   signal lbrw                : std_logic;
   signal lblast              : std_logic;
   signal lbad                : std_logic_vector(15 downto 0);
   signal lbholda             : std_logic;
   signal lbrdy               : std_logic;
   signal lbclk               : std_logic;

   signal regiob_dummy_xled : std_logic_vector(3 downto 0);


begin

-- ----------------------- Clk gen. component -------------------------
CLK_GEN_U : CLK_GEN
port map (
      -- Input
   CLK               => ios_lbclk,
   RESET             => ios_reset,
      -- Output
   CLK2X             => open,
   CLK1X             => lbclk,
   LOCK              => lock_lb
);


clkgen_lock <= lock_lb and lock_rio;
IBUF_ETHCLK: IBUFGDS
port map (
   I  => ETHCLKP, -- P-Channel input to LVDS buffer
   IB => ETHCLKN, -- N-Channel input to LVDS buffer
   O  => ethclk   -- Output of LVDS buffer (input to FPGA fabric)= DDR data_in
);


-- DCM for RocketIO clocking
RIO_DCM : DCM
-- pragma translate_off
generic map (
   DLL_FREQUENCY_MODE    => "LOW",
   DUTY_CYCLE_CORRECTION => TRUE,
   STARTUP_WAIT          => FALSE,
   CLKDV_DIVIDE          => 2.0
)
-- pragma translate_on
port map (
   CLKIN     => ethclk, --FCLK,
   CLKFB     => fclk0,
   RST       => ios_reset,
   CLK0      => fclk0_bufg,
   CLK180    => usr_clk2_bufg,
   CLKDV     => usr_clk_bufg,
   LOCKED    => lock_rio
);

FCLK0_BUFG_INST   : BUFG port map (I => fclk0_bufg,    O => fclk0);
USRCLK_BUFG_INST  : BUFG port map (I => usr_clk_bufg,  O => usr_clk);
-- USRCLK2_BUFG_INST : BUFG port map (I => usr_clk2_bufg, O => usr_clk2);

-- usr_clk  <= fclk0;
usr_clk2 <= usr_clk;
usr_clk2_n  <= not fclk0;



-- -----------------------------------------------------------------------------
--                              Interface 0
-- -----------------------------------------------------------------------------

-- SFP <==> GMII

GMII2SFP_A : entity work.rio_gmii_debug
generic map(
   BP_BASE   => LB_TCAM_BASE_ADDR,
   BASE => LB_TEST_BASE_ADDR
   )
port map (
   RIO_RCLK  => ethclk,       -- Precise reference clock for RIO, 62.5MHz (REFCLK)
   RIO_DCLK  => usr_clk,      -- 62.5MHz RIO data clk, GMII clk phase aligned (USRCLK, USRCLK2)
   RESET     => reset,        -- System reset
--   -- GMII interface
   GMII_CLK  => fclk0,        -- 125MHz GMII clock, common for RX and TX
   GMII_RXD  => gmii_rxd0,
   GMII_RXDV => gmii_rxdv0,
   GMII_RXER => gmii_rxer0,
   GMII_TXD  => X"00",
   GMII_TXEN => '0',
   GMII_TXER => '0',
   -- MGT (RocketIO) interface
   RXN       => RDN_A,
   RXP       => RDP_A,
   TXN       => TDN_A,
   TXP       => TDP_A,
   -- Status and service interface
   RXPOLARITY => '1',
   TXPOLARITY => '1',
   LOOPBACK   => "00",
   RXSYNCLOSS => open,
   -- ---------- Internal bus signals ----------------
   LBCLK	         => lbclk,
   LBFRAME	      => lbframe,
   LBHOLDA	      => lbholda,
   LBAD	         => lbad,
   LBAS	         => lbas,
   LBRW	         => lbrw,
   LBRDY	         => lbrdy,
   LBLAST	      => lblast
);
   
-- ---------------------- Local bus interface -----------------------------
IOS_TO_LB : LB_BRIDGE
generic map (
   IN_TRISTATES => false  -- Disable tristates on LBRDY_IN and LBHOLDA_IN
)
 port map (
    RESET       => reset,
    LBCLK       => lbclk,
    -- Local bus input (to local_bus driver)
   LBFRAME_IN => IOS(76),
   LBAS_IN    => IOS(77),
   LBRW_IN    => IOS(78),
   LBLAST_IN  => IOS(80),
   LBAD_IN(15 downto 13) => IOS(102 downto 100),
   LBAD_IN(12 downto  4) => IOS(98 downto 90),
   LBAD_IN( 3 downto  1) => IOS(88 downto 86),
   LBAD_IN(0)            => IOS(84),
   LBHOLDA_IN => IOS(82),
   LBRDY_IN   => IOS(81),
    -- Local bus extendet output (to components)
    LBFRAME_OUT => lbframe,
    LBAS_OUT    => lbas,
    LBRW_OUT    => lbrw,
    LBLAST_OUT  => lblast,
    LBAD_OUT    => lbad,
    LBHOLDA_OUT => lbholda,
    LBRDY_OUT   => lbrdy
);

-- --------------------------- ID component -------------------------------
ID_COMP_LB_U: ID_COMP_LB
   generic map (
      BASE         => ID_BASE_ADDR,
      PROJECT_ID   => ID_XFP_TEST, 
      SW_MAJOR     => ID_SW_MAJOR,
      SW_MINOR     => ID_SW_MINOR,
      HW_MAJOR     => ID_HW_MAJOR,
      HW_MINOR     => ID_HW_MINOR,
      PROJECT_TEXT => ID_XFP_TEST_TEXT 
   )
   port map (
      RESET    => reset,
      
      LBCLK    => lbclk,  -- internal bus clock, up to 100 MHz
      LBFRAME  => lbframe, -- Frame
      LBHOLDA  => lbholda, -- Hold Ack
      LBAD     => lbad,    -- Address/Data
      LBAS     => lbas,    -- Adress strobe
      LBRW     => lbrw,    -- Direction (Read#/Write, low : read)
      LBRDY    => lbrdy,   -- Ready
      LBLAST   => lblast   -- Last word in transfer
); 

 --------------------------- IBUF component -------------------------------
--ibuf_gmii_top4_u: ibuf_gmii_top4
--   generic map(
--      ADDR_BASE   => IFC_TEST0_BASE_ADDR,
--      DATA_PATHS  => DATA_PATHS,        -- Output data width in bytes
--      DFIFO_SIZE  => 255,     -- Packet data fifo size
--      HFIFO_SIZE  => 255      -- Header fifo size
--   )
--   port map(
--
--      -- ---------------- Control signal -----------------
--      RESET         => RESET,
--
--      -- ------------------------------------------------
--      -- -------------- IBUF interfaces -----------------
--      
--      -- -----------
--      -- INTERFACE 0
--      
--      -- GMII RX interface
--      IBUF0_RXCLK     => fclk0,
--      IBUF0_RXD       => gmii_rxd0,
--      IBUF0_RXDV      => gmii_rxdv0,
--      IBUF0_RXER      => gmii_rxer0,
--
--      -- PHY status interface
--      PHY0_LINK_STATUS       => phy0_link_status,
--      PHY0_DUPLEX_MODE       => phy0_duplex_mode,
--      PHY0_SPEED             => phy0_speed,
--      PHY0_SGMII             => phy0_sgmii,
--
--      -- PACODAG interface
--      IBUF0_CTRL_CLK    => ibuf0_ctrl_clk,
--      IBUF0_CTRL_DATA        => ibuf0_ctrl_di,
--      IBUF0_CTRL_REM       => ibuf0_ctrl_rem,
--      IBUF0_CTRL_SRC_RDY_N => ibuf0_ctrl_src_rdy_n,
--      IBUF0_CTRL_SOP_N     => ibuf0_ctrl_sop_n,
--      IBUF0_CTRL_EOP_N     => ibuf0_ctrl_eop_n,
--      IBUF0_CTRL_DST_RDY_N => ibuf0_ctrl_dst_rdy_n,
--      IBUF0_CTRL_HDR_EN    => ibuf0_ctrl_hdr_en,
--      IBUF0_CTRL_FTR_EN    => ibuf0_ctrl_ftr_en,
--
--      -- IBUF status interface
--      IBUF0_SOP         => ibuf0_sop,
--      IBUF0_STAT        => ibuf0_stat,
--      IBUF0_STAT_DV     => ibuf0_stat_dv,
--
--      -- Sampling unit interface
----      IBUF0_SAU_ACCEPT => ibuf0_sau_accept,
--      IBUF0_SAU_ACCEPT => '1',
--      IBUF0_SAU_DV     => ibuf0_sau_dv,
--
--      -- FrameLink interface
--      IBUF0_RDCLK      => lbclk,
--      IBUF0_DATA       => ibuf0_data,
--      IBUF0_DREM       => ibuf0_drem,
--      IBUF0_SRC_RDY_N  => ibuf0_src_rdy_n,
--      IBUF0_SOF_N      => ibuf0_sof_n,
--      IBUF0_SOP_N      => ibuf0_sop_n,
--      IBUF0_EOF_N      => ibuf0_eof_n,
--      IBUF0_EOP_N      => ibuf0_eop_n,
--      IBUF0_DST_RDY_N  => ibuf0_dst_rdy_n,
--
--      -- -----------
--      -- INTERFACE 1
--      
--      -- GMII RX interface
--      IBUF1_RXCLK     => fclk0,
--      IBUF1_RXD       => X"00",
--      IBUF1_RXDV      => '0',
--      IBUF1_RXER      => '0',
--
--      -- PHY status interface
--      PHY1_LINK_STATUS       => '0',
--      PHY1_DUPLEX_MODE       => '0',
--      PHY1_SPEED             => "00",
--      PHY1_SGMII             => '0',
--
--      -- PACODAG interface
--      IBUF1_CTRL_CLK    => open,
--      IBUF1_CTRL_DATA        => x"0000",
--      IBUF1_CTRL_REM       => "0",
--      IBUF1_CTRL_SRC_RDY_N => '0',
--      IBUF1_CTRL_SOP_N     => '0',
--      IBUF1_CTRL_EOP_N     => '0',
--      IBUF1_CTRL_DST_RDY_N => open,
--      IBUF1_CTRL_HDR_EN    => '0',
--      IBUF1_CTRL_FTR_EN    => '0',
--
--      -- IBUF status interface
--      IBUF1_SOP         => open,
--      IBUF1_STAT        => open,
--      IBUF1_STAT_DV     => open,
--
--      -- Sampling unit interface
--      IBUF1_SAU_ACCEPT => '0',
--      IBUF1_SAU_DV     => '0',
--
--      -- FrameLink interface
--      IBUF1_RDCLK      => lbclk,
--      IBUF1_DATA       => open,
--      IBUF1_DREM       => open,
--      IBUF1_SRC_RDY_N  => open,
--      IBUF1_SOF_N      => open,
--      IBUF1_SOP_N      => open,
--      IBUF1_EOF_N      => open,
--      IBUF1_EOP_N      => open,
--      IBUF1_DST_RDY_N  => '0',
--
--      -- -----------
--      -- INTERFACE 2
--      
--      -- GMII RX interface
--      IBUF2_RXCLK     => fclk0,
--      IBUF2_RXD       => x"00",
--      IBUF2_RXDV      => '0',
--      IBUF2_RXER      => '0',
--
--      -- PHY status interface
--      PHY2_LINK_STATUS       => '0',
--      PHY2_DUPLEX_MODE       => '0',
--      PHY2_SPEED             => "00",
--      PHY2_SGMII             => '0',
--
--      -- PACODAG interface
--      IBUF2_CTRL_CLK    => open,
--      IBUF2_CTRL_DATA        => x"0000",
--      IBUF2_CTRL_REM       => "0",
--      IBUF2_CTRL_SRC_RDY_N => '0',
--      IBUF2_CTRL_SOP_N     => '0',
--      IBUF2_CTRL_EOP_N     => '0',
--      IBUF2_CTRL_DST_RDY_N => open,
--      IBUF2_CTRL_HDR_EN    => '0',
--      IBUF2_CTRL_FTR_EN    => '0',
--
--      -- IBUF status interface
--      IBUF2_SOP         => open,
--      IBUF2_STAT        => open,
--      IBUF2_STAT_DV     => open,
--
--      -- Sampling unit interface
--      IBUF2_SAU_ACCEPT => '0',
--      IBUF2_SAU_DV     => '0',
--
--      -- FrameLink interface
--      IBUF2_RDCLK      => lbclk,
--      IBUF2_DATA       => open,
--      IBUF2_DREM       => open,
--      IBUF2_SRC_RDY_N  => open,
--      IBUF2_SOF_N      => open,
--      IBUF2_SOP_N      => open,
--      IBUF2_EOF_N      => open,
--      IBUF2_EOP_N      => open,
--      IBUF2_DST_RDY_N  => '0',
--
--      -- -----------
--      -- INTERFACE 3
--      
--      -- GMII RX interface
--      IBUF3_RXCLK     => fclk0,
--      IBUF3_RXD       => x"00",
--      IBUF3_RXDV      => '0',
--      IBUF3_RXER      => '0',
--
--      -- PHY status interface
--      PHY3_LINK_STATUS       => '0',
--      PHY3_DUPLEX_MODE       => '0',
--      PHY3_SPEED             => "00",
--      PHY3_SGMII             => '0',
--
--      -- PACODAG interface
--      IBUF3_CTRL_CLK    => open,
--      IBUF3_CTRL_DATA        => x"0000",
--      IBUF3_CTRL_REM       => "0",
--      IBUF3_CTRL_SRC_RDY_N => '0',
--      IBUF3_CTRL_SOP_N     => '0',
--      IBUF3_CTRL_EOP_N     => '0',
--      IBUF3_CTRL_DST_RDY_N => open,
--      IBUF3_CTRL_HDR_EN    => '0',
--      IBUF3_CTRL_FTR_EN    => '0',
--            
--      -- IBUF status interface
--      IBUF3_SOP         => open,
--      IBUF3_STAT        => open,
--      IBUF3_STAT_DV     => open,
--
--      -- Sampling unit interface
--      IBUF3_SAU_ACCEPT => '1',
--      IBUF3_SAU_DV     => '1',
--
--      -- FrameLink interface
--      IBUF3_RDCLK      => lbclk,
--      IBUF3_DATA       => open,
--      IBUF3_DREM       => open,
--      IBUF3_SRC_RDY_N  => open,
--      IBUF3_SOF_N      => open,
--      IBUF3_SOP_N      => open,
--      IBUF3_EOF_N      => open,
--      IBUF3_EOP_N      => open,
--      IBUF3_DST_RDY_N  => '0',
--
--      -- ------------------------------------------------
--      -- ---------- Internal bus signals ----------------
--      LBCLK	         => lbclk,
--      LBFRAME	      => lbframe,
--      LBHOLDA	      => lbholda,
--      LBAD	         => lbad,
--      LBAS	         => lbas,
--      LBRW	         => lbrw,
--      LBRDY	         => lbrdy,
--      LBLAST	      => lblast
--   );
---- --------------------------- IBUF_TEST component -------------------------------
--IBUF_TEST_U: ibuf_test
--   generic map(
--      ADDR_BASE   => IFC_TEST1_BASE_ADDR,
--      DATA_PATHS  => DATA_PATHS,
--      FIFO_SIZE   => 8191
--   )
--
--   port map(
--      RESET    => RESET,
--
--      DATA       => ibuf0_data,
--      DREM       => ibuf0_drem,
--      SRC_RDY_N  => ibuf0_src_rdy_n,
--      SOF_N      => ibuf0_sof_n,
--      SOP_N      => ibuf0_sop_n,
--      EOF_N      => ibuf0_eof_n,
--      EOP_N      => ibuf0_eop_n,
--      DST_RDY_N  => ibuf0_dst_rdy_n,
--
--      -- PACODAG interface
--      CTRL_CLK    => ibuf0_ctrl_clk,
--      CTRL_DI     => ibuf0_ctrl_di,
--      CTRL_SRC_RDY_N => ibuf0_ctrl_src_rdy_n,
--      CTRL_REM    => ibuf0_ctrl_rem,
--      CTRL_SOP_N    => ibuf0_ctrl_sop_n,
--      CTRL_EOP_N    => ibuf0_ctrl_eop_n,
--      CTRL_DST_RDY_N => ibuf0_ctrl_dst_rdy_n,
--      CTRL_HDR_EN => ibuf0_ctrl_hdr_en,
--      CTRL_FTR_EN => ibuf0_ctrl_ftr_en,
--
--      -- IBUF status interface
--      SOP         => ibuf0_sop,
--
--      -- Sampling unit interface
--      SAU_ACCEPT => ibuf0_sau_accept,
--      SAU_DV     => ibuf0_sau_dv,
--
--      -- Local Bus Interface
--      LBCLK     => lbclk,
--      LBFRAME   => lbframe,
--      LBHOLDA   => lbholda,
--      LBAD      => lbad,
--      LBAS      => lbas,
--      LBRW      => lbrw,
--      LBRDY     => lbrdy,
--      LBLAST    => lblast
--   );

PHYTER_I2C_U: entity work.PHYTER_I2C
   generic map(
      BASE  => PHYTER_I2C_BASE_ADDR
   )
   port map(
      CLK      => lbclk,
      RESET    => reset,
      --
      SCL0     => MODDEFA(1),
      SDA0     => MODDEFA(2),
      SCL1     => MODDEFB(1),
      SDA1     => MODDEFB(2),
      SCL2     => MODDEFC(1),
      SDA2     => MODDEFC(2),
      SCL3     => MODDEFD(1),
      SDA3     => MODDEFD(2),
      --
      PHDISA   => TXDISA,
      PHDISB   => TXDISB,
      PHDISC   => TXDISC,
      PHDISD   => TXDISD,
      --
      LBCLK    => lbclk,   -- internal bus clock, up to 100 MHz
      LBFRAME  => lbframe, -- Frame
      LBHOLDA  => lbholda, -- Hold Ack
      LBAD     => lbad,    -- Address/Data
      LBAS     => lbas,    -- Adress strobe
      LBRW     => lbrw,    -- Direction (Read#/Write, low : read)
      LBRDY    => lbrdy,   -- Ready
      LBLAST   => lblast   -- Last word in transfer
   );

-- ----------------------------------------------------------------------------
-- Fake solution : we need to have at least one *regiob* register in design
-- to pass compilation of design (IOB attributes settings). LED outputs are
-- used for this purpose. LRESET signal and clkgen_lock signal are used as
-- inputs for LEDs.
-- Solution by Tomas Pecenka,thanks
regiob_dummy_xledp: process(clk50)
begin
   if (clk50'event AND clk50 = '1') then
      regiob_dummy_xled <= reset & clkgen_lock & reset & clkgen_lock;
   end if;
end process;
-- ----------------------------------------------------------------------------

ios_lbclk    <= IOS(79);
ios_reset    <= IOS(20);

reset       <= not clkgen_lock or ios_reset;

-- -----------------------------------------------------------------------------
--                             Other interfaces
-- -----------------------------------------------------------------------------

RSA       <= '0';

RSB       <= '0';

RSC       <= '0';

RSD       <= '0';

end architecture sfp_arch;
