--
-- ibuf_gmii_ent.vhd: Input buffer for gmii - entity
--
-- Copyright (C) 2005 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--            Martin Mikusek <martin.mikusek@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
entity ibuf_gmii is
   generic(
      DATA_PATHS  : integer := 2;      -- Output data width in bytes
      DFIFO_SIZE  : integer := 2048;      -- Packet data fifo size
      HFIFO_SIZE  : integer := 512;      -- Header fifo size
      MACS        : integer := 16;-- Number of MAC addresses (up to 16)
      -- Add control data to FrameLink header/footer
      CTRL_HDR_EN : boolean := true;
      CTRL_FTR_EN : boolean := false;
      -- true: FCS is kept in the frame
      -- false: FCS is cut out during processing
      INBANDFCS   : boolean := false
   );

   port (
      RESET    : in  std_logic;

      -- GMII RX interface
      RXCLK     : in  std_logic;
      RXD       : in  std_logic_vector(7 downto 0);
      RXDV      : in  std_logic;
      RXER      : in  std_logic;

      -- PHY status interface
      LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                             -- 1: SGMII mode active, the PHY status ports are valid
      -- PACODAG interface
      CTRL_CLK    : out std_logic;
      CTRL_DI        : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      CTRL_REM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      CTRL_SRC_RDY_N : in std_logic;
      CTRL_SOP_N     : in std_logic;
      CTRL_EOP_N     : in std_logic;
      CTRL_DST_RDY_N : out std_logic;
      CTRL_RDY    : in std_logic; -- PACODAG is ready

      -- IBUF status interface
      SOP         : out std_logic;
      STAT        : out t_ibuf_general_stat;
      STAT_DV     : out std_logic;

      -- Sampling unit interface
      SAU_ACCEPT : in std_logic;
      SAU_DV     : in std_logic;

      -- FrameLink interface
      RDCLK      : in  std_logic;
      DATA       : out std_logic_vector((DATA_PATHS*8)-1 downto 0);
      DREM       : out std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      SRC_RDY_N  : out std_logic;
      SOF_N      : out std_logic;
      SOP_N      : out std_logic;
      EOF_N      : out std_logic;
      EOP_N      : out std_logic;
      DST_RDY_N  : in std_logic;

      -- Address decoder interface
      ADC_CLK  : out std_logic;
      ADC_RD   : in  std_logic;
      ADC_WR   : in  std_logic;
      ADC_ADDR : in  std_logic_vector(5 downto 0);
      ADC_DI   : in  std_logic_vector(31 downto 0);
      ADC_DO   : out std_logic_vector(31 downto 0);
      ADC_DRDY : out std_logic
   );
end entity ibuf_gmii;

