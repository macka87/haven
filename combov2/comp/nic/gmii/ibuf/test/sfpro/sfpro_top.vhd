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
      HFIFO_SIZE  : integer      -- Control fifo size
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
end component ibuf_gmii_top4;

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

-- -------------------------- OBUF ---------------------------------
component obuf_gmii_top4 is
   generic(
      ADDR_BASE   : integer;
      DATA_PATHS  : integer;
      DFIFO_SIZE  : integer;
      SFIFO_SIZE  : integer;
      CTRL_CMD    : boolean
   );
   port(

      -- ---------------- Control signal -----------------
      RESET         : in  std_logic;
      WRCLK         : in  std_logic;
      REFCLK        : in  std_logic;

      -- -------------- Buffer interface -----------------
      -- Interface 0
      OBUF0_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF0_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF0_SRC_RDY_N  : in std_logic;
      OBUF0_SOF_N      : in std_logic;
      OBUF0_SOP_N      : in std_logic;
      OBUF0_EOF_N      : in std_logic;
      OBUF0_EOP_N      : in std_logic;
      OBUF0_DST_RDY_N  : out std_logic;
      -- Interface 1 
      OBUF1_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF1_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF1_SRC_RDY_N  : in std_logic;
      OBUF1_SOF_N      : in std_logic;
      OBUF1_SOP_N      : in std_logic;
      OBUF1_EOF_N      : in std_logic;
      OBUF1_EOP_N      : in std_logic;
      OBUF1_DST_RDY_N  : out std_logic;
      -- Interface 2 
      OBUF2_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF2_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF2_SRC_RDY_N  : in std_logic;
      OBUF2_SOF_N      : in std_logic;
      OBUF2_SOP_N      : in std_logic;
      OBUF2_EOF_N      : in std_logic;
      OBUF2_EOP_N      : in std_logic;
      OBUF2_DST_RDY_N  : out std_logic;
      -- Interface 3 
      OBUF3_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      OBUF3_DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      OBUF3_SRC_RDY_N  : in std_logic;
      OBUF3_SOF_N      : in std_logic;
      OBUF3_SOP_N      : in std_logic;
      OBUF3_EOF_N      : in std_logic;
      OBUF3_EOP_N      : in std_logic;
      OBUF3_DST_RDY_N  : out std_logic;

      -- -------------- GMII/MII interface ---------------
      -- Interface 0
      OBUF0_TXCLK       : out  std_logic;
      OBUF0_TXD         : out  std_logic_vector(7 downto 0);
      OBUF0_TXEN        : out  std_logic;
      OBUF0_TXER        : out  std_logic;
      -- Interface 1
      OBUF1_TXCLK       : out  std_logic;
      OBUF1_TXD        : out  std_logic_vector(7 downto 0);
      OBUF1_TXEN       : out  std_logic;
      OBUF1_TXER       : out  std_logic;
      -- Interface 2
      OBUF2_TXCLK       : out  std_logic;
      OBUF2_TXD        : out  std_logic_vector(7 downto 0);
      OBUF2_TXEN       : out  std_logic;
      OBUF2_TXER       : out  std_logic;
      -- Interface 3
      OBUF3_TXCLK       : out  std_logic;
      OBUF3_TXD        : out  std_logic_vector(7 downto 0);
      OBUF3_TXEN       : out  std_logic;
      OBUF3_TXER       : out  std_logic;

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
end component obuf_gmii_top4;
-- *****************************   End of Components parts   *******************************************
-- *****************************************************************************************************

 -- Global Signals....

   constant DATA_PATHS        : integer := 8;
   
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

   signal gmii_rxd1           : std_logic_vector(7 downto 0);
   signal gmii_rxdv1          : std_logic;
   signal gmii_rxer1          : std_logic;

   signal gmii_rxd2           : std_logic_vector(7 downto 0);
   signal gmii_rxdv2          : std_logic;
   signal gmii_rxer2          : std_logic;

   signal gmii_rxd3           : std_logic_vector(7 downto 0);
   signal gmii_rxdv3          : std_logic;
   signal gmii_rxer3          : std_logic;

   signal ibuf0_ctrl_clk      : std_logic;
   signal ibuf0_ctrl_di    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf0_ctrl_src_rdy_n    : std_logic;
   signal ibuf0_ctrl_rem      : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf0_ctrl_sop_n      : std_logic;
   signal ibuf0_ctrl_eop_n      : std_logic;
   signal ibuf0_ctrl_dst_rdy_n    : std_logic;
   signal ibuf0_ctrl_hdr_en      : std_logic;
   signal ibuf0_ctrl_ftr_en      : std_logic;

   signal ibuf1_ctrl_clk      : std_logic;
   signal ibuf1_ctrl_di    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf1_ctrl_src_rdy_n    : std_logic;
   signal ibuf1_ctrl_rem      : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf1_ctrl_sop_n      : std_logic;
   signal ibuf1_ctrl_eop_n      : std_logic;
   signal ibuf1_ctrl_dst_rdy_n    : std_logic;
   signal ibuf1_ctrl_hdr_en      : std_logic;
   signal ibuf1_ctrl_ftr_en      : std_logic;

   signal ibuf2_ctrl_clk      : std_logic;
   signal ibuf2_ctrl_di    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf2_ctrl_src_rdy_n    : std_logic;
   signal ibuf2_ctrl_rem      : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf2_ctrl_sop_n      : std_logic;
   signal ibuf2_ctrl_eop_n      : std_logic;
   signal ibuf2_ctrl_dst_rdy_n    : std_logic;
   signal ibuf2_ctrl_hdr_en      : std_logic;
   signal ibuf2_ctrl_ftr_en      : std_logic;

   signal ibuf3_ctrl_clk      : std_logic;
   signal ibuf3_ctrl_di    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf3_ctrl_src_rdy_n    : std_logic;
   signal ibuf3_ctrl_rem      : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf3_ctrl_sop_n      : std_logic;
   signal ibuf3_ctrl_eop_n      : std_logic;
   signal ibuf3_ctrl_dst_rdy_n    : std_logic;
   signal ibuf3_ctrl_hdr_en      : std_logic;
   signal ibuf3_ctrl_ftr_en      : std_logic;

   signal phy0_link_status    : std_logic;
   signal phy0_duplex_mode    : std_logic;
   signal phy0_speed    : std_logic_vector(1 downto 0);
   signal phy0_sgmii    : std_logic;
      -- IBUF status interface
   signal ibuf0_sop     : std_logic;
   signal ibuf0_stat    : t_ibuf_stat;
   signal ibuf0_stat_dv    : std_logic;
   signal ibuf1_sop     : std_logic;
   signal ibuf1_stat    : t_ibuf_stat;
   signal ibuf1_stat_dv    : std_logic;
   signal ibuf2_sop     : std_logic;
   signal ibuf2_stat    : t_ibuf_stat;
   signal ibuf2_stat_dv    : std_logic;
   signal ibuf3_sop     : std_logic;
   signal ibuf3_stat    : t_ibuf_stat;
   signal ibuf3_stat_dv    : std_logic;

      -- Sampling unit interface
   signal ibuf0_sau_accept    : std_logic;
   signal ibuf0_sau_dv     : std_logic;

   signal ibuf1_sau_accept    : std_logic;
   signal ibuf1_sau_dv     : std_logic;

   signal ibuf2_sau_accept    : std_logic;
   signal ibuf2_sau_dv     : std_logic;

   signal ibuf3_sau_accept    : std_logic;
   signal ibuf3_sau_dv     : std_logic;

      -- FrameLink interface
   signal ibuf0_data    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf0_drem    : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf0_src_rdy_n     : std_logic;
   signal ibuf0_sof_n      : std_logic;
   signal ibuf0_sop_n      : std_logic;
   signal ibuf0_eof_n      : std_logic;
   signal ibuf0_eop_n      : std_logic;
   signal ibuf0_dst_rdy_n     : std_logic;

   signal ibuf1_data    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf1_drem    : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf1_src_rdy_n     : std_logic;
   signal ibuf1_sof_n      : std_logic;
   signal ibuf1_sop_n      : std_logic;
   signal ibuf1_eof_n      : std_logic;
   signal ibuf1_eop_n      : std_logic;
   signal ibuf1_dst_rdy_n     : std_logic;

   signal ibuf2_data    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf2_drem    : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf2_src_rdy_n     : std_logic;
   signal ibuf2_sof_n      : std_logic;
   signal ibuf2_sop_n      : std_logic;
   signal ibuf2_eof_n      : std_logic;
   signal ibuf2_eop_n      : std_logic;
   signal ibuf2_dst_rdy_n     : std_logic;

   signal ibuf3_data    : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal ibuf3_drem    : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal ibuf3_src_rdy_n     : std_logic;
   signal ibuf3_sof_n      : std_logic;
   signal ibuf3_sop_n      : std_logic;
   signal ibuf3_eof_n      : std_logic;
   signal ibuf3_eop_n      : std_logic;
   signal ibuf3_dst_rdy_n     : std_logic;

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

   signal reg_genctrl0 : std_logic;
   signal reg_genctrl1 : std_logic;
   signal reg_genctrl2 : std_logic;
   signal reg_genctrl3 : std_logic;

   signal obuf0_data : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal obuf0_drem : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal obuf0_src_rdy_n : std_logic;
   signal obuf0_sof_n : std_logic;
   signal obuf0_sop_n : std_logic;
   signal obuf0_eof_n : std_logic;
   signal obuf0_eop_n : std_logic;
   signal obuf0_txclk : std_logic;
   signal obuf0_txd : std_logic_vector(7 downto 0);
   signal obuf0_txen : std_logic;
   signal obuf0_txer : std_logic;

   signal obuf1_data : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal obuf1_drem : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal obuf1_src_rdy_n : std_logic;
   signal obuf1_sof_n : std_logic;
   signal obuf1_sop_n : std_logic;
   signal obuf1_eof_n : std_logic;
   signal obuf1_eop_n : std_logic;
   signal obuf1_txclk : std_logic;
   signal obuf1_txd : std_logic_vector(7 downto 0);
   signal obuf1_txen : std_logic;
   signal obuf1_txer : std_logic;

   signal obuf2_data : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal obuf2_drem : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal obuf2_src_rdy_n : std_logic;
   signal obuf2_sof_n : std_logic;
   signal obuf2_sop_n : std_logic;
   signal obuf2_eof_n : std_logic;
   signal obuf2_eop_n : std_logic;
   signal obuf2_txclk : std_logic;
   signal obuf2_txd : std_logic_vector(7 downto 0);
   signal obuf2_txen : std_logic;
   signal obuf2_txer : std_logic;

   signal obuf3_data : std_logic_vector((DATA_PATHS*8)-1 downto 0);
   signal obuf3_drem : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal obuf3_src_rdy_n : std_logic;
   signal obuf3_sof_n : std_logic;
   signal obuf3_sop_n : std_logic;
   signal obuf3_eof_n : std_logic;
   signal obuf3_eop_n : std_logic;
   signal obuf3_txclk : std_logic;
   signal obuf3_txd : std_logic_vector(7 downto 0);
   signal obuf3_txen : std_logic;
   signal obuf3_txer : std_logic;

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

--GMII2SFP_A : entity work.rio_gmii
--port map (
--   RIO_RCLK  => ethclk,       -- Precise reference clock for RIO, 62.5MHz (REFCLK)
--   RIO_DCLK  => usr_clk,      -- 62.5MHz RIO data clk, GMII clk phase aligned (USRCLK, USRCLK2)
--   RESET     => reset,        -- System reset
----   -- GMII interface
--   GMII_CLK  => fclk0,        -- 125MHz GMII clock, common for RX and TX
--   GMII_RXD  => gmii_rxd0,
--   GMII_RXDV => gmii_rxdv0,
--   GMII_RXER => gmii_rxer0,
--   GMII_TXD  => X"00",
--   GMII_TXEN => '0',
--   GMII_TXER => '0',
--   -- MGT (RocketIO) interface
--   RXN       => RDN_A,
--   RXP       => RDP_A,
--   TXN       => TDN_A,
--   TXP       => TDP_A,
--   -- Status and service interface
--   RXPOLARITY => '1',
--   TXPOLARITY => '1',
--   LOOPBACK   => "00",
--   RXSYNCLOSS => open
--);

GMII2SFP_A : entity work.rio_gmii_debug
generic map(
   BP_BASE   => IFC_TEST1_BASE_ADDR,
   BASE => LB_TEST_BASE_ADDR,
   BUFFER_SIZE => 2048
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
   GMII_TXD  => obuf0_txd,
   GMII_TXEN => obuf0_txen,
   GMII_TXER => obuf0_txer,
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
   -- PHY status interface
   LINK_STATUS       => phy0_link_status,
   DUPLEX_MODE       => phy0_duplex_mode,
   SPEED             => phy0_speed,
   SGMII             => phy0_sgmii,
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
   
GMII2SFP_B : entity work.rio_gmii
port map (
   RIO_RCLK  => ethclk,       -- Precise reference clock for RIO, 62.5MHz (REFCLK)
   RIO_DCLK  => usr_clk,      -- 62.5MHz RIO data clk, GMII clk phase aligned (USRCLK, USRCLK2)
   RESET     => reset,        -- System reset
--   -- GMII interface
   GMII_CLK  => fclk0,        -- 125MHz GMII clock, common for RX and TX
   GMII_RXD  => gmii_rxd1,
   GMII_RXDV => gmii_rxdv1,
   GMII_RXER => gmii_rxer1,
   GMII_TXD  => obuf1_txd,
   GMII_TXEN => obuf1_txen,
   GMII_TXER => obuf1_txer,
   -- MGT (RocketIO) interface
   RXN       => RDN_B,
   RXP       => RDP_B,
   TXN       => TDN_B,
   TXP       => TDP_B,
   -- Status and service interface
   RXPOLARITY => '1',
   TXPOLARITY => '1',
   LOOPBACK   => "00",
   RXSYNCLOSS => open
);

GMII2SFP_C : entity work.rio_gmii
port map (
   RIO_RCLK  => ethclk,       -- Precise reference clock for RIO, 62.5MHz (REFCLK)
   RIO_DCLK  => usr_clk,      -- 62.5MHz RIO data clk, GMII clk phase aligned (USRCLK, USRCLK2)
   RESET     => reset,        -- System reset
--   -- GMII interface
   GMII_CLK  => fclk0,        -- 125MHz GMII clock, common for RX and TX
   GMII_RXD  => gmii_rxd2,
   GMII_RXDV => gmii_rxdv2,
   GMII_RXER => gmii_rxer2,
   GMII_TXD  => obuf2_txd,
   GMII_TXEN => obuf2_txen,
   GMII_TXER => obuf2_txer,
   -- MGT (RocketIO) interface
   RXN       => RDN_C,
   RXP       => RDP_C,
   TXN       => TDN_C,
   TXP       => TDP_C,
   -- Status and service interface
   RXPOLARITY => '1',
   TXPOLARITY => '1',
   LOOPBACK   => "00",
   RXSYNCLOSS => open
);

GMII2SFP_D : entity work.rio_gmii
port map (
   RIO_RCLK  => ethclk,       -- Precise reference clock for RIO, 62.5MHz (REFCLK)
   RIO_DCLK  => usr_clk,      -- 62.5MHz RIO data clk, GMII clk phase aligned (USRCLK, USRCLK2)
   RESET     => reset,        -- System reset
--   -- GMII interface
   GMII_CLK  => fclk0,        -- 125MHz GMII clock, common for RX and TX
   GMII_RXD  => gmii_rxd3,
   GMII_RXDV => gmii_rxdv3,
   GMII_RXER => gmii_rxer3,
   GMII_TXD  => obuf3_txd,
   GMII_TXEN => obuf3_txen,
   GMII_TXER => obuf3_txer,
   -- MGT (RocketIO) interface
   RXN       => RDN_D,
   RXP       => RDP_D,
   TXN       => TDN_D,
   TXP       => TDP_D,
   -- Status and service interface
   RXPOLARITY => '1',
   TXPOLARITY => '1',
   LOOPBACK   => "00",
   RXSYNCLOSS => open
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

-- --------------------------- IBUF component -------------------------------
ibuf_gmii_top4_u: ibuf_gmii_top4
   generic map(
      ADDR_BASE   => IFC_TEST0_BASE_ADDR,
      DATA_PATHS  => DATA_PATHS,        -- Output data width in bytes
      DFIFO_SIZE  => 255,     -- Packet data fifo size
      HFIFO_SIZE  => 255      -- Header fifo size
   )
   port map(

      -- ---------------- Control signal -----------------
      RESET         => RESET,

      -- ------------------------------------------------
      -- -------------- IBUF interfaces -----------------
      
      -- -----------
      -- INTERFACE 0
      
      -- GMII RX interface
      IBUF0_RXCLK     => fclk0,
      IBUF0_RXD       => gmii_rxd0,
      IBUF0_RXDV      => gmii_rxdv0,
      IBUF0_RXER      => gmii_rxer0,

      -- PHY status interface
--      PHY0_LINK_STATUS       => phy0_link_status,
--      PHY0_DUPLEX_MODE       => phy0_duplex_mode,
--      PHY0_SPEED             => phy0_speed,
--      PHY0_SGMII             => phy0_sgmii,

      -- PACODAG interface
      IBUF0_CTRL_CLK    => ibuf0_ctrl_clk,
      IBUF0_CTRL_DATA        => ibuf0_ctrl_di,
      IBUF0_CTRL_REM       => ibuf0_ctrl_rem,
      IBUF0_CTRL_SRC_RDY_N => ibuf0_ctrl_src_rdy_n,
      IBUF0_CTRL_SOP_N     => ibuf0_ctrl_sop_n,
      IBUF0_CTRL_EOP_N     => ibuf0_ctrl_eop_n,
      IBUF0_CTRL_DST_RDY_N => ibuf0_ctrl_dst_rdy_n,
      IBUF0_CTRL_HDR_EN    => ibuf0_ctrl_hdr_en,
      IBUF0_CTRL_FTR_EN    => ibuf0_ctrl_ftr_en,

      -- IBUF status interface
      IBUF0_SOP         => ibuf0_sop,
      IBUF0_STAT        => ibuf0_stat,
      IBUF0_STAT_DV     => ibuf0_stat_dv,

      -- Sampling unit interface
      IBUF0_SAU_ACCEPT => ibuf0_sau_accept,
--      IBUF0_SAU_ACCEPT => '1',
      IBUF0_SAU_DV     => ibuf0_sau_dv,

      -- FrameLink interface
      IBUF0_RDCLK      => lbclk,
      IBUF0_DATA       => ibuf0_data,
      IBUF0_DREM       => ibuf0_drem,
      IBUF0_SRC_RDY_N  => ibuf0_src_rdy_n,
      IBUF0_SOF_N      => ibuf0_sof_n,
      IBUF0_SOP_N      => ibuf0_sop_n,
      IBUF0_EOF_N      => ibuf0_eof_n,
      IBUF0_EOP_N      => ibuf0_eop_n,
      IBUF0_DST_RDY_N  => ibuf0_dst_rdy_n,

      -- -----------
      -- INTERFACE 1
      
      -- GMII RX interface
      IBUF1_RXCLK     => fclk0,
      IBUF1_RXD       => gmii_rxd1,
      IBUF1_RXDV      => gmii_rxdv1,
      IBUF1_RXER      => gmii_rxer1,

      -- PHY status interface
--      PHY1_LINK_STATUS       => phy1_link_status,
--      PHY1_DUPLEX_MODE       => phy1_duplex_mode,
--      PHY1_SPEED             => phy1_speed,
--      PHY1_SGMII             => phy1_sgmii,

      -- PACODAG interface
      IBUF1_CTRL_CLK    => ibuf1_ctrl_clk,
      IBUF1_CTRL_DATA        => ibuf1_ctrl_di,
      IBUF1_CTRL_REM       => ibuf1_ctrl_rem,
      IBUF1_CTRL_SRC_RDY_N => ibuf1_ctrl_src_rdy_n,
      IBUF1_CTRL_SOP_N     => ibuf1_ctrl_sop_n,
      IBUF1_CTRL_EOP_N     => ibuf1_ctrl_eop_n,
      IBUF1_CTRL_DST_RDY_N => ibuf1_ctrl_dst_rdy_n,
      IBUF1_CTRL_HDR_EN    => ibuf1_ctrl_hdr_en,
      IBUF1_CTRL_FTR_EN    => ibuf1_ctrl_ftr_en,

      -- IBUF status interface
      IBUF1_SOP         => ibuf1_sop,
      IBUF1_STAT        => ibuf1_stat,
      IBUF1_STAT_DV     => ibuf1_stat_dv,

      -- Sampling unit interface
      IBUF1_SAU_ACCEPT => ibuf1_sau_accept,
--      IBUF1_SAU_ACCEPT => '1',
      IBUF1_SAU_DV     => ibuf1_sau_dv,

      -- FrameLink interface
      IBUF1_RDCLK      => lbclk,
      IBUF1_DATA       => ibuf1_data,
      IBUF1_DREM       => ibuf1_drem,
      IBUF1_SRC_RDY_N  => ibuf1_src_rdy_n,
      IBUF1_SOF_N      => ibuf1_sof_n,
      IBUF1_SOP_N      => ibuf1_sop_n,
      IBUF1_EOF_N      => ibuf1_eof_n,
      IBUF1_EOP_N      => ibuf1_eop_n,
      IBUF1_DST_RDY_N  => ibuf1_dst_rdy_n,

      -- -----------
      -- INTERFACE 2
      
      -- GMII RX interface
      IBUF2_RXCLK     => fclk0,
      IBUF2_RXD       => gmii_rxd2,
      IBUF2_RXDV      => gmii_rxdv2,
      IBUF2_RXER      => gmii_rxer2,

      -- PHY status interface
--      PHY2_LINK_STATUS       => phy2_link_status,
--      PHY2_DUPLEX_MODE       => phy2_duplex_mode,
--      PHY2_SPEED             => phy2_speed,
--      PHY2_SGMII             => phy2_sgmii,

      -- PACODAG interface
      IBUF2_CTRL_CLK    => ibuf2_ctrl_clk,
      IBUF2_CTRL_DATA        => ibuf2_ctrl_di,
      IBUF2_CTRL_REM       => ibuf2_ctrl_rem,
      IBUF2_CTRL_SRC_RDY_N => ibuf2_ctrl_src_rdy_n,
      IBUF2_CTRL_SOP_N     => ibuf2_ctrl_sop_n,
      IBUF2_CTRL_EOP_N     => ibuf2_ctrl_eop_n,
      IBUF2_CTRL_DST_RDY_N => ibuf2_ctrl_dst_rdy_n,
      IBUF2_CTRL_HDR_EN    => ibuf2_ctrl_hdr_en,
      IBUF2_CTRL_FTR_EN    => ibuf2_ctrl_ftr_en,

      -- IBUF status interface
      IBUF2_SOP         => ibuf2_sop,
      IBUF2_STAT        => ibuf2_stat,
      IBUF2_STAT_DV     => ibuf2_stat_dv,

      -- Sampling unit interface
      IBUF2_SAU_ACCEPT => ibuf2_sau_accept,
--      IBUF2_SAU_ACCEPT => '1',
      IBUF2_SAU_DV     => ibuf2_sau_dv,

      -- FrameLink interface
      IBUF2_RDCLK      => lbclk,
      IBUF2_DATA       => ibuf2_data,
      IBUF2_DREM       => ibuf2_drem,
      IBUF2_SRC_RDY_N  => ibuf2_src_rdy_n,
      IBUF2_SOF_N      => ibuf2_sof_n,
      IBUF2_SOP_N      => ibuf2_sop_n,
      IBUF2_EOF_N      => ibuf2_eof_n,
      IBUF2_EOP_N      => ibuf2_eop_n,
      IBUF2_DST_RDY_N  => ibuf2_dst_rdy_n,

      -- -----------
      -- INTERFACE 3
      
      -- GMII RX interface
      IBUF3_RXCLK     => fclk0,
      IBUF3_RXD       => gmii_rxd3,
      IBUF3_RXDV      => gmii_rxdv3,
      IBUF3_RXER      => gmii_rxer3,

      -- PHY status interface
--      PHY3_LINK_STATUS       => phy3_link_status,
--      PHY3_DUPLEX_MODE       => phy3_duplex_mode,
--      PHY3_SPEED             => phy3_speed,
--      PHY3_SGMII             => phy3_sgmii,

      -- PACODAG interface
      IBUF3_CTRL_CLK    => ibuf3_ctrl_clk,
      IBUF3_CTRL_DATA        => ibuf3_ctrl_di,
      IBUF3_CTRL_REM       => ibuf3_ctrl_rem,
      IBUF3_CTRL_SRC_RDY_N => ibuf3_ctrl_src_rdy_n,
      IBUF3_CTRL_SOP_N     => ibuf3_ctrl_sop_n,
      IBUF3_CTRL_EOP_N     => ibuf3_ctrl_eop_n,
      IBUF3_CTRL_DST_RDY_N => ibuf3_ctrl_dst_rdy_n,
      IBUF3_CTRL_HDR_EN    => ibuf3_ctrl_hdr_en,
      IBUF3_CTRL_FTR_EN    => ibuf3_ctrl_ftr_en,

      -- IBUF status interface
      IBUF3_SOP         => ibuf3_sop,
      IBUF3_STAT        => ibuf3_stat,
      IBUF3_STAT_DV     => ibuf3_stat_dv,

      -- Sampling unit interface
      IBUF3_SAU_ACCEPT => ibuf3_sau_accept,
--      IBUF3_SAU_ACCEPT => '1',
      IBUF3_SAU_DV     => ibuf3_sau_dv,

      -- FrameLink interface
      IBUF3_RDCLK      => lbclk,
      IBUF3_DATA       => ibuf3_data,
      IBUF3_DREM       => ibuf3_drem,
      IBUF3_SRC_RDY_N  => ibuf3_src_rdy_n,
      IBUF3_SOF_N      => ibuf3_sof_n,
      IBUF3_SOP_N      => ibuf3_sop_n,
      IBUF3_EOF_N      => ibuf3_eof_n,
      IBUF3_EOP_N      => ibuf3_eop_n,
      IBUF3_DST_RDY_N  => ibuf3_dst_rdy_n,

      -- ------------------------------------------------
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
-- --------------------------- IBUF_TEST component -------------------------------
IBUF0_TEST_U: ibuf_test
   generic map(
      ADDR_BASE   => IBUF0_TEST_BASE_ADDR,
      DATA_PATHS  => DATA_PATHS,
      FIFO_SIZE   => 255
   )

   port map(
      RESET    => RESET,

      DATA       => ibuf0_data,
      DREM       => ibuf0_drem,
      SRC_RDY_N  => ibuf0_src_rdy_n,
      SOF_N      => ibuf0_sof_n,
      SOP_N      => ibuf0_sop_n,
      EOF_N      => ibuf0_eof_n,
      EOP_N      => ibuf0_eop_n,
      DST_RDY_N  => ibuf0_dst_rdy_n,

      -- PACODAG interface
      CTRL_CLK    => ibuf0_ctrl_clk,
      CTRL_DI     => ibuf0_ctrl_di,
      CTRL_SRC_RDY_N => ibuf0_ctrl_src_rdy_n,
      CTRL_REM    => ibuf0_ctrl_rem,
      CTRL_SOP_N    => ibuf0_ctrl_sop_n,
      CTRL_EOP_N    => ibuf0_ctrl_eop_n,
      CTRL_DST_RDY_N => ibuf0_ctrl_dst_rdy_n,
      CTRL_HDR_EN => ibuf0_ctrl_hdr_en,
      CTRL_FTR_EN => ibuf0_ctrl_ftr_en,

      -- IBUF status interface
      SOP         => ibuf0_sop,

      -- Sampling unit interface
      SAU_ACCEPT => ibuf0_sau_accept,
      SAU_DV     => ibuf0_sau_dv,

      -- Local Bus Interface
      LBCLK     => lbclk,
      LBFRAME   => lbframe,
      LBHOLDA   => lbholda,
      LBAD      => lbad,
      LBAS      => lbas,
      LBRW      => lbrw,
      LBRDY     => lbrdy,
      LBLAST    => lblast
   );

IBUF1_TEST_U: ibuf_test
   generic map(
      ADDR_BASE   => IBUF1_TEST_BASE_ADDR,
      DATA_PATHS  => DATA_PATHS,
      FIFO_SIZE   => 255
   )

   port map(
      RESET    => RESET,

      DATA       => ibuf1_data,
      DREM       => ibuf1_drem,
      SRC_RDY_N  => ibuf1_src_rdy_n,
      SOF_N      => ibuf1_sof_n,
      SOP_N      => ibuf1_sop_n,
      EOF_N      => ibuf1_eof_n,
      EOP_N      => ibuf1_eop_n,
      DST_RDY_N  => ibuf1_dst_rdy_n,

      -- PACODAG interface
      CTRL_CLK    => ibuf1_ctrl_clk,
      CTRL_DI     => ibuf1_ctrl_di,
      CTRL_SRC_RDY_N => ibuf1_ctrl_src_rdy_n,
      CTRL_REM    => ibuf1_ctrl_rem,
      CTRL_SOP_N    => ibuf1_ctrl_sop_n,
      CTRL_EOP_N    => ibuf1_ctrl_eop_n,
      CTRL_DST_RDY_N => ibuf1_ctrl_dst_rdy_n,
      CTRL_HDR_EN => ibuf1_ctrl_hdr_en,
      CTRL_FTR_EN => ibuf1_ctrl_ftr_en,

      -- IBUF status interface
      SOP         => ibuf1_sop,

      -- Sampling unit interface
      SAU_ACCEPT => ibuf1_sau_accept,
      SAU_DV     => ibuf1_sau_dv,

      -- Local Bus Interface
      LBCLK     => lbclk,
      LBFRAME   => lbframe,
      LBHOLDA   => lbholda,
      LBAD      => lbad,
      LBAS      => lbas,
      LBRW      => lbrw,
      LBRDY     => lbrdy,
      LBLAST    => lblast
   );

IBUF2_TEST_U: ibuf_test
   generic map(
      ADDR_BASE   =>IBUF2_TEST_BASE_ADDR,
      DATA_PATHS  => DATA_PATHS,
      FIFO_SIZE   => 255
   )

   port map(
      RESET    => RESET,

      DATA       => ibuf2_data,
      DREM       => ibuf2_drem,
      SRC_RDY_N  => ibuf2_src_rdy_n,
      SOF_N      => ibuf2_sof_n,
      SOP_N      => ibuf2_sop_n,
      EOF_N      => ibuf2_eof_n,
      EOP_N      => ibuf2_eop_n,
      DST_RDY_N  => ibuf2_dst_rdy_n,

      -- PACODAG interface
      CTRL_CLK    => ibuf2_ctrl_clk,
      CTRL_DI     => ibuf2_ctrl_di,
      CTRL_SRC_RDY_N => ibuf2_ctrl_src_rdy_n,
      CTRL_REM    => ibuf2_ctrl_rem,
      CTRL_SOP_N    => ibuf2_ctrl_sop_n,
      CTRL_EOP_N    => ibuf2_ctrl_eop_n,
      CTRL_DST_RDY_N => ibuf2_ctrl_dst_rdy_n,
      CTRL_HDR_EN => ibuf2_ctrl_hdr_en,
      CTRL_FTR_EN => ibuf2_ctrl_ftr_en,

      -- IBUF status interface
      SOP         => ibuf2_sop,

      -- Sampling unit interface
      SAU_ACCEPT => ibuf2_sau_accept,
      SAU_DV     => ibuf2_sau_dv,

      -- Local Bus Interface
      LBCLK     => lbclk,
      LBFRAME   => lbframe,
      LBHOLDA   => lbholda,
      LBAD      => lbad,
      LBAS      => lbas,
      LBRW      => lbrw,
      LBRDY     => lbrdy,
      LBLAST    => lblast
   );

IBUF3_TEST_U: ibuf_test
   generic map(
      ADDR_BASE   => IBUF3_TEST_BASE_ADDR,
      DATA_PATHS  => DATA_PATHS,
      FIFO_SIZE   => 255
   )

   port map(
      RESET    => RESET,

      DATA       => ibuf3_data,
      DREM       => ibuf3_drem,
      SRC_RDY_N  => ibuf3_src_rdy_n,
      SOF_N      => ibuf3_sof_n,
      SOP_N      => ibuf3_sop_n,
      EOF_N      => ibuf3_eof_n,
      EOP_N      => ibuf3_eop_n,
      DST_RDY_N  => ibuf3_dst_rdy_n,

      -- PACODAG interface
      CTRL_CLK    => ibuf3_ctrl_clk,
      CTRL_DI     => ibuf3_ctrl_di,
      CTRL_SRC_RDY_N => ibuf3_ctrl_src_rdy_n,
      CTRL_REM    => ibuf3_ctrl_rem,
      CTRL_SOP_N    => ibuf3_ctrl_sop_n,
      CTRL_EOP_N    => ibuf3_ctrl_eop_n,
      CTRL_DST_RDY_N => ibuf3_ctrl_dst_rdy_n,
      CTRL_HDR_EN => ibuf3_ctrl_hdr_en,
      CTRL_FTR_EN => ibuf3_ctrl_ftr_en,

      -- IBUF status interface
      SOP         => ibuf3_sop,

      -- Sampling unit interface
      SAU_ACCEPT => ibuf3_sau_accept,
      SAU_DV     => ibuf3_sau_dv,

      -- Local Bus Interface
      LBCLK     => lbclk,
      LBFRAME   => lbframe,
      LBHOLDA   => lbholda,
      LBAD      => lbad,
      LBAS      => lbas,
      LBRW      => lbrw,
      LBRDY     => lbrdy,
      LBLAST    => lblast
   );

-- --------------------------- OBUF component -------------------------------
-- gener control data for obuf
process(RESET, LBCLK)
begin
   if (RESET = '1') then
      reg_genctrl0 <= '0';
      reg_genctrl1 <= '0';
      reg_genctrl2 <= '0';
      reg_genctrl3 <= '0';
   elsif (LBCLK'event AND LBCLK = '1') then
      if (ibuf0_eop_n = '0') then
         reg_genctrl0 <= '1';
      elsif (ibuf0_eop_n = '1') then
         reg_genctrl0 <= '0';
      end if;
      if (ibuf1_eop_n = '0') then
         reg_genctrl1 <= '1';
      elsif (ibuf1_eop_n = '1') then
         reg_genctrl1 <= '0';
      end if;
      if (ibuf2_eop_n = '0') then
         reg_genctrl2 <= '1';
      elsif (ibuf2_eop_n = '1') then
         reg_genctrl2 <= '0';
      end if;
      if (ibuf3_eop_n = '0') then
         reg_genctrl3 <= '1';
      elsif (ibuf3_eop_n = '1') then
         reg_genctrl3 <= '0';
      end if;
   end if;
end process;

obuf0_data(3 downto 0) <= X"3" when reg_genctrl0 = '1' else
                          ibuf0_data(3 downto 0);
obuf0_data((DATA_PATHS*8)-1 downto 4) <= ibuf0_data((DATA_PATHS*8)-1 downto 4);
obuf0_drem <= (others => '1') when reg_genctrl0 = '1' else
              ibuf0_drem;
obuf0_src_rdy_n <= '0' when reg_genctrl0 = '1' else
              ibuf0_src_rdy_n;
obuf0_sop_n <= '0' when reg_genctrl0 = '1' else
              ibuf0_sop_n;
obuf0_eop_n <= '0' when reg_genctrl0 = '1' else
              ibuf0_eop_n;

obuf1_data(3 downto 0) <= X"3" when reg_genctrl1 = '1' else
                          ibuf1_data(3 downto 0);
obuf1_data((DATA_PATHS*8)-1 downto 4) <= ibuf1_data((DATA_PATHS*8)-1 downto 4);
obuf1_drem <= (others => '1') when reg_genctrl1 = '1' else
              ibuf1_drem;
obuf1_src_rdy_n <= '0' when reg_genctrl1 = '1' else
              ibuf1_src_rdy_n;
obuf1_sop_n <= '0' when reg_genctrl1 = '1' else
              ibuf1_sop_n;
obuf1_eop_n <= '0' when reg_genctrl1 = '1' else
              ibuf1_eop_n;

obuf2_data(3 downto 0) <= X"3" when reg_genctrl2 = '1' else
                          ibuf2_data(3 downto 0);
obuf2_data((DATA_PATHS*8)-1 downto 4) <= ibuf2_data((DATA_PATHS*8)-1 downto 4);
obuf2_drem <= (others => '1') when reg_genctrl2 = '1' else
              ibuf2_drem;
obuf2_src_rdy_n <= '0' when reg_genctrl2 = '1' else
              ibuf2_src_rdy_n;
obuf2_sop_n <= '0' when reg_genctrl2 = '1' else
              ibuf2_sop_n;
obuf2_eop_n <= '0' when reg_genctrl2 = '1' else
              ibuf2_eop_n;

obuf3_data(3 downto 0) <= X"3" when reg_genctrl3 = '1' else
                          ibuf3_data(3 downto 0);
obuf3_data((DATA_PATHS*8)-1 downto 4) <= ibuf3_data((DATA_PATHS*8)-1 downto 4);
obuf3_drem <= (others => '1') when reg_genctrl3 = '1' else
              ibuf3_drem;
obuf3_src_rdy_n <= '0' when reg_genctrl3 = '1' else
              ibuf3_src_rdy_n;
obuf3_sop_n <= '0' when reg_genctrl3 = '1' else
              ibuf3_sop_n;
obuf3_eop_n <= '0' when reg_genctrl3 = '1' else
              ibuf3_eop_n;

obuf_gmii_top4_u: obuf_gmii_top4
   generic map(
      ADDR_BASE   => LB_SSRAM0_BASE_ADDR,
      DATA_PATHS  => DATA_PATHS,
      DFIFO_SIZE  => 255,
      SFIFO_SIZE  => 255,
      CTRL_CMD    => true
   )
   port map(

      -- ---------------- Control signal -----------------
      RESET         => reset,
      WRCLK         => lbclk,
      REFCLK        => fclk0,

      -- -------------- Buffer interface -----------------
      -- Interface 0
      OBUF0_DATA       => obuf0_data,
      OBUF0_DREM       => obuf0_drem,
      OBUF0_SRC_RDY_N  => obuf0_src_rdy_n,
      OBUF0_SOF_N      => '1',
      OBUF0_SOP_N      => obuf0_sop_n,
      OBUF0_EOF_N      => '1',
      OBUF0_EOP_N      => obuf0_eop_n,
      OBUF0_DST_RDY_N  => open,
      -- Interface 1 
      OBUF1_DATA       => obuf1_data,
      OBUF1_DREM       => obuf1_drem,
      OBUF1_SRC_RDY_N  => obuf1_src_rdy_n,
      OBUF1_SOF_N      => '1',
      OBUF1_SOP_N      => obuf1_sop_n,
      OBUF1_EOF_N      => '1',
      OBUF1_EOP_N      => obuf1_eop_n,
      OBUF1_DST_RDY_N  => open,
      -- Interface 2 
      OBUF2_DATA       => obuf2_data,
      OBUF2_DREM       => obuf2_drem,
      OBUF2_SRC_RDY_N  => obuf2_src_rdy_n,
      OBUF2_SOF_N      => '1',
      OBUF2_SOP_N      => obuf2_sop_n,
      OBUF2_EOF_N      => '1',
      OBUF2_EOP_N      => obuf2_eop_n,
      OBUF2_DST_RDY_N  => open,
      -- Interface 3 
      OBUF3_DATA       => obuf3_data,
      OBUF3_DREM       => obuf3_drem,
      OBUF3_SRC_RDY_N  => obuf3_src_rdy_n,
      OBUF3_SOF_N      => '1',
      OBUF3_SOP_N      => obuf3_sop_n,
      OBUF3_EOF_N      => '1',
      OBUF3_EOP_N      => obuf3_eop_n,
      OBUF3_DST_RDY_N  => open,

      -- -------------- GMII/MII interface ---------------
      -- Interface 0
      OBUF0_TXCLK       => open,
      OBUF0_TXD         => obuf0_txd,
      OBUF0_TXEN        => obuf0_txen,
      OBUF0_TXER        => obuf0_txer,
      -- Interface 1
      OBUF1_TXCLK       => open,
      OBUF1_TXD         => obuf1_txd,
      OBUF1_TXEN        => obuf1_txen,
      OBUF1_TXER        => obuf1_txer,
      -- Interface 2
      OBUF2_TXCLK       => open,
      OBUF2_TXD         => obuf2_txd,
      OBUF2_TXEN        => obuf2_txen,
      OBUF2_TXER        => obuf2_txer,
      -- Interface 3
      OBUF3_TXCLK       => open,
      OBUF3_TXD         => obuf3_txd,
      OBUF3_TXEN        => obuf3_txen,
      OBUF3_TXER        => obuf3_txer,

      -- ---------- Internal bus signals ----------------
      LBCLK	     => lbclk,
      LBFRAME	     => lbframe,
      LBHOLDA	     => lbholda,
      LBAD	     => lbad,
      LBAS	     => lbas,
      LBRW	     => lbrw,
      LBRDY	     => lbrdy,
      LBLAST	     => lblast
   );

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
