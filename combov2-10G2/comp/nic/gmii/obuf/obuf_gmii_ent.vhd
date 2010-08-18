--
-- obuf_gmii_ent.vhd: Output buffer for gmii - entity
--
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_gmii is
   generic (
      --ADDR_BASE  : integer := 0;
      --ADDR_WIDTH : integer := 9;

      DATA_PATHS : integer := 2;
      DFIFO_SIZE : integer := 4095;
      SFIFO_SIZE : integer := 127;

      CTRL_CMD   : boolean := false;

      -- true: FCS is present in the frame (and will be recomputed)
      -- false: FCS will be added
      INBANDFCS  : boolean := false;
      -- Should the FCS computation be skipped?
      SKIP_FCS   : boolean := false
      -- NB: if SKIP_FCS is set to true (i.e. FCS is already present in the
      -- frame), INBANDFCS needs to be set to false, otherwise, the FCS from
      -- the original frame will be cut off
   );
   port (
      RESET      : in  std_logic;

      -- FrameLink input interface
      WRCLK      : in  std_logic;
      DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      DREM       : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);
      SRC_RDY_N  : in std_logic;
      SOF_N      : in std_logic;
      SOP_N      : in std_logic;
      EOF_N      : in std_logic;
      EOP_N      : in std_logic;
      DST_RDY_N  : out std_logic;

      -- transmit gmii interface
      REFCLK     : in  std_logic;
      TXCLK      : out std_logic;
      TXD	 : out std_logic_vector(7 downto 0);
      TXEN	 : out std_logic;
      TXER	 : out std_logic;

      -- PHY status interface
      LINK_STATUS       : in std_logic; -- 0: link down, 1: link up
      DUPLEX_MODE       : in std_logic; -- 0: half duplex, 1: full duplex
      SPEED             : in std_logic_vector(1 downto 0); -- 00: 10Mbps, 01: 100Mbps, 10: 1000Mbps, 11: RESERVED
      SGMII             : in std_logic; -- 0: PHY status is not valid, the speed is 1000Mbps full duplex, 
                                             -- 1: SGMII mode active, the PHY status ports are valid
      -- address decoder interface
      ADC_CLK    : out std_logic;
      ADC_RD     : in  std_logic;
      ADC_WR     : in  std_logic;
      ADC_ADDR   : in  std_logic_vector(5 downto 0); -- 32bit addressable words
      ADC_DI     : in  std_logic_vector(31 downto 0);
      ADC_DO     : out std_logic_vector(31 downto 0);
      ADC_DRDY   : out std_logic
   );
end entity obuf_gmii;

