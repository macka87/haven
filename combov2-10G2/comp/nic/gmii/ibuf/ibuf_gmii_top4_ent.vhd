-- ibuf_gmii_top4_hfe2_ent.vhd: Input Buffer - 4 ibufs + LB entity
-- Copyright (C) 2006 CESNET
-- Author(s): Mikusek Martin <martin.mikusek@liberouter.org>
--            Jan Pazdera    <pazdera@liberouter.org>
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
use work.math_pack.all;
use work.ibuf_general_pkg.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity ibuf_gmii_top4 is
   generic(
      ADDR_BASE   : integer;
      DATA_PATHS  : integer;     -- Output data width in bytes
      DFIFO_SIZE  : integer;     -- Packet data fifo size
      HFIFO_SIZE  : integer;     -- Control fifo size
      MACS        : integer := 16;  -- Number of MAC addresses (up to 16)
      -- true: FCS is kept in the frame
      -- false: FCS is cut out during processing
      INBANDFCS   : boolean := false
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
--      PHY0_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
--      PHY0_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
--      PHY0_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
--      PHY0_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
--                                             -- 1: SGMII mode active, the PHY status ports are valid
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
      IBUF0_CTRL_RDY    : in std_logic;

      -- IBUF status interface
      IBUF0_SOP         : out std_logic;
      IBUF0_STAT        : out t_ibuf_general_stat;
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
--      PHY1_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
--      PHY1_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
--      PHY1_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
--      PHY1_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
--                                             -- 1: SGMII mode active, the PHY status ports are valid
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
      IBUF1_CTRL_RDY    : in std_logic;

      -- IBUF status interface
      IBUF1_SOP         : out std_logic;
      IBUF1_STAT        : out t_ibuf_general_stat;
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
--      PHY2_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
--      PHY2_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
--      PHY2_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
--      PHY2_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
--                                             -- 1: SGMII mode active, the PHY status ports are valid
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
      IBUF2_CTRL_RDY    : in std_logic;

      -- IBUF status interface
      IBUF2_SOP         : out std_logic;
      IBUF2_STAT        : out t_ibuf_general_stat;
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
--      PHY3_LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
--      PHY3_DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
--      PHY3_SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
--      PHY3_SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
--                                             -- 1: SGMII mode active, the PHY status ports are valid
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
      IBUF3_CTRL_RDY    : in std_logic;

      -- IBUF status interface
      IBUF3_SOP         : out std_logic;
      IBUF3_STAT        : out t_ibuf_general_stat;
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
end entity ibuf_gmii_top4;
-- ----------------------------------------------------------------------------
