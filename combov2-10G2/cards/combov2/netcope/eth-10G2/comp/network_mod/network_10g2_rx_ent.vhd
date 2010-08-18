-- network_10g2_ent.vhd: Network Module for 2x10Gbps Combo2 interface card
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.network_mod_10g2_rx_const.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.all;
-- pragma translate_on

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity NETWORK_MOD_10G2_RX is
   port(
      -- Clock signal for user interface
      USER_CLK             :  in std_logic;
      -- FrameLink reset
      FL_RESET             :  in std_logic;
      -- ICS reset
      BUSRESET             :  in std_logic;

      -- 2 XGMII INTERFACES
      -- RX
      XGMII_RESET          :  in std_logic_vector(  1 downto 0);
      XGMII_RXCLK          :  in std_logic_vector(  1 downto 0);
      XGMII_RXD            :  in std_logic_vector(127 downto 0);
      XGMII_RXC            :  in std_logic_vector( 15 downto 0);
      -- TX
      XGMII_TXCLK          :  in std_logic_vector(  1 downto 0);
      XGMII_TXD            : out std_logic_vector(127 downto 0);
      XGMII_TXC            : out std_logic_vector( 15 downto 0);

      -- USER INTERFACE
      -- Network interface 0
      IBUF0_TX_SOF_N       : out std_logic;
      IBUF0_TX_SOP_N       : out std_logic;
      IBUF0_TX_EOP_N       : out std_logic;
      IBUF0_TX_EOF_N       : out std_logic;
      IBUF0_TX_SRC_RDY_N   : out std_logic;
      IBUF0_TX_DST_RDY_N   :  in std_logic;
      IBUF0_TX_DATA        : out std_logic_vector(127 downto 0);
      IBUF0_TX_REM         : out std_logic_vector(3 downto 0);

      -- PACODAG interface
      IBUF0_CTRL_CLK       : out std_logic;
      IBUF0_CTRL_RESET     : out std_logic;
      IBUF0_CTRL_DATA      :  in std_logic_vector(127 downto 0);
      IBUF0_CTRL_REM       :  in std_logic_vector(3 downto 0);
      IBUF0_CTRL_SRC_RDY_N :  in std_logic;
      IBUF0_CTRL_SOP_N     :  in std_logic;
      IBUF0_CTRL_EOP_N     :  in std_logic;
      IBUF0_CTRL_DST_RDY_N : out std_logic;
      IBUF0_CTRL_RDY       :  in std_logic;

      -- IBUF status interface
      IBUF0_SOP            : out std_logic;
      IBUF0_PAYLOAD_LEN    : out std_logic_vector(15 downto 0);
      IBUF0_FRAME_ERROR    : out std_logic; -- 0: OK, 1: Error occured
      IBUF0_CRC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad CRC 
      IBUF0_MAC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad MAC
      IBUF0_LEN_BELOW_MIN  : out std_logic; -- 0: OK, 1: Length is below min
      IBUF0_LEN_OVER_MTU   : out std_logic; -- 0: OK, 1: Length is over MTU
      IBUF0_STAT_DV        : out std_logic;
      -- Signals active in '1' for one cycle for every processed packet
      IBUF0_FRAME_RECEIVED    : out std_logic;
      IBUF0_FRAME_DISCARDED   : out std_logic;
      -- When active in '1' frame was discarded due to buffer overflow. Can be active only together
      -- with FRAME_DISCARDED
      IBUF0_BUFFER_OVF        : out std_logic;

      -- Sampling unit interface
      IBUF0_SAU_CLK        : out std_logic;
      IBUF0_SAU_RESET      : out std_logic;
      IBUF0_SAU_REQ        : out std_logic;
      IBUF0_SAU_ACCEPT     :  in std_logic;
      IBUF0_SAU_DV         :  in std_logic;
      
      -- Network interface 1 --------------------------------------------------
      IBUF1_TX_SOF_N       : out std_logic;
      IBUF1_TX_SOP_N       : out std_logic;
      IBUF1_TX_EOP_N       : out std_logic;
      IBUF1_TX_EOF_N       : out std_logic;
      IBUF1_TX_SRC_RDY_N   : out std_logic;
      IBUF1_TX_DST_RDY_N   :  in std_logic;
      IBUF1_TX_DATA        : out std_logic_vector(127 downto 0);
      IBUF1_TX_REM         : out std_logic_vector(3 downto 0);

      -- PACODAG interface
      IBUF1_CTRL_CLK       : out std_logic;
      IBUF1_CTRL_RESET     : out std_logic;
      IBUF1_CTRL_DATA      :  in std_logic_vector(127 downto 0);
      IBUF1_CTRL_REM       :  in std_logic_vector(3 downto 0);
      IBUF1_CTRL_SRC_RDY_N :  in std_logic;
      IBUF1_CTRL_SOP_N     :  in std_logic;
      IBUF1_CTRL_EOP_N     :  in std_logic;
      IBUF1_CTRL_DST_RDY_N : out std_logic;
      IBUF1_CTRL_RDY       :  in std_logic;

      -- IBUF status interface
      IBUF1_SOP            : out std_logic;
      IBUF1_PAYLOAD_LEN    : out std_logic_vector(15 downto 0);
      IBUF1_FRAME_ERROR    : out std_logic; -- 0: OK, 1: Error occured
      IBUF1_CRC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad CRC 
      IBUF1_MAC_CHECK_FAILED:out std_logic; -- 0: OK, 1: Bad MAC
      IBUF1_LEN_BELOW_MIN  : out std_logic; -- 0: OK, 1: Length is below min
      IBUF1_LEN_OVER_MTU   : out std_logic; -- 0: OK, 1: Length is over MTU
      IBUF1_STAT_DV        : out std_logic;
      -- Signals active in '1' for one cycle for every processed packet
      IBUF1_FRAME_RECEIVED    : out std_logic;
      IBUF1_FRAME_DISCARDED   : out std_logic;
      -- When active in '1' frame was discarded due to buffer overflow. Can be active only together
      -- with FRAME_DISCARDED
      IBUF1_BUFFER_OVF        : out std_logic;

      -- Sampling unit interface
      IBUF1_SAU_CLK        : out std_logic;
      IBUF1_SAU_RESET      : out std_logic;
      IBUF1_SAU_REQ        : out std_logic;
      IBUF1_SAU_ACCEPT     :  in std_logic;
      IBUF1_SAU_DV         :  in std_logic;

      -- Led interface
      IBUF_LED             : out std_logic_vector(1 downto 0);
      OBUF_LED             : out std_logic_vector(1 downto 0);
     
      -- Link presence interface
      LINK0		   : out std_logic;
      LINK1		   : out std_logic;
 
      -- MI32 interface
      MI32_DWR             : in  std_logic_vector(31 downto 0);
      MI32_ADDR            : in  std_logic_vector(31 downto 0);
      MI32_RD              : in  std_logic;
      MI32_WR              : in  std_logic;
      MI32_BE              : in  std_logic_vector(3 downto 0);
      MI32_DRD             : out std_logic_vector(31 downto 0);
      MI32_ARDY            : out std_logic;
      MI32_DRDY            : out std_logic
   );
end entity NETWORK_MOD_10G2_RX;


