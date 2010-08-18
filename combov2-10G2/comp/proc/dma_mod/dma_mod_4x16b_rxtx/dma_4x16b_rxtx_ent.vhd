-- dma_4x16b_rxtx_ent.vhd: entity of DMA Module for 4x16 RX+TX interface
-- Copyright (C) 2008 CESNET
-- Author(s):  Pavol Korcek <korcek@liberouter.org>
--             Martin Kosek <kosek@liberouter.org>
--             Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

entity DMA_MOD_4x16b_RXTX is
   port(
      -- Common interface
      -- ICS Clock and RESET - drives almost whole module, also IB and LB ifcs
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- USER Clock and RESET - driver FL_ASFIFOs and FL ifcs
      USER_CLK       : in  std_logic;
      USER_RESET     : in  std_logic;

      -- Synchronous at CLK (ICS Clock)
      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;

      -- network interfaces - USER_CLK
      -- input interface
      RX0_DATA       : in  std_logic_vector(15 downto 0);
      RX0_DREM       : in  std_logic_vector(0 downto 0);
      RX0_SOP_N      : in  std_logic;
      RX0_EOP_N      : in  std_logic;
      RX0_SOF_N      : in  std_logic;
      RX0_EOF_N      : in  std_logic;
      RX0_SRC_RDY_N  : in  std_logic;
      RX0_DST_RDY_N  : out std_logic;

      RX1_DATA       : in  std_logic_vector(15 downto 0);
      RX1_DREM       : in  std_logic_vector(0 downto 0);
      RX1_SOP_N      : in  std_logic;
      RX1_EOP_N      : in  std_logic;
      RX1_SOF_N      : in  std_logic;
      RX1_EOF_N      : in  std_logic;
      RX1_SRC_RDY_N  : in  std_logic;
      RX1_DST_RDY_N  : out std_logic;

      RX2_DATA       : in  std_logic_vector(15 downto 0);
      RX2_DREM       : in  std_logic_vector(0 downto 0);
      RX2_SOP_N      : in  std_logic;
      RX2_EOP_N      : in  std_logic;
      RX2_SOF_N      : in  std_logic;
      RX2_EOF_N      : in  std_logic;
      RX2_SRC_RDY_N  : in  std_logic;
      RX2_DST_RDY_N  : out std_logic;

      RX3_DATA       : in  std_logic_vector(15 downto 0);
      RX3_DREM       : in  std_logic_vector(0 downto 0);
      RX3_SOP_N      : in  std_logic;
      RX3_EOP_N      : in  std_logic;
      RX3_SOF_N      : in  std_logic;
      RX3_EOF_N      : in  std_logic;
      RX3_SRC_RDY_N  : in  std_logic;
      RX3_DST_RDY_N  : out std_logic;

      -- output interfaces
      TX0_DATA       : out std_logic_vector(15 downto 0);
      TX0_DREM       : out std_logic_vector(0 downto 0);
      TX0_SOP_N      : out std_logic;
      TX0_EOP_N      : out std_logic;
      TX0_SOF_N      : out std_logic;
      TX0_EOF_N      : out std_logic;
      TX0_SRC_RDY_N  : out std_logic;
      TX0_DST_RDY_N  : in  std_logic;

      TX1_DATA       : out std_logic_vector(15 downto 0);
      TX1_DREM       : out std_logic_vector(0 downto 0);
      TX1_SOP_N      : out std_logic;
      TX1_EOP_N      : out std_logic;
      TX1_SOF_N      : out std_logic;
      TX1_EOF_N      : out std_logic;
      TX1_SRC_RDY_N  : out std_logic;
      TX1_DST_RDY_N  : in  std_logic;

      TX2_DATA       : out std_logic_vector(15 downto 0);
      TX2_DREM       : out std_logic_vector(0 downto 0);
      TX2_SOP_N      : out std_logic;
      TX2_EOP_N      : out std_logic;
      TX2_SOF_N      : out std_logic;
      TX2_EOF_N      : out std_logic;
      TX2_SRC_RDY_N  : out std_logic;
      TX2_DST_RDY_N  : in  std_logic;

      TX3_DATA       : out std_logic_vector(15 downto 0);
      TX3_DREM       : out std_logic_vector(0 downto 0);
      TX3_SOP_N      : out std_logic;
      TX3_EOP_N      : out std_logic;
      TX3_SOF_N      : out std_logic;
      TX3_EOF_N      : out std_logic;
      TX3_SRC_RDY_N  : out std_logic;
      TX3_DST_RDY_N  : in  std_logic;

      -- Internal Bus - CLK (ICS Clock)
      IB_DOWN_DATA      : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N     : in  std_logic;
      IB_DOWN_EOF_N     : in  std_logic;
      IB_DOWN_SRC_RDY_N : in  std_logic;
      IB_DOWN_DST_RDY_N : out std_logic;
      IB_UP_DATA        : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N       : out std_logic;
      IB_UP_EOF_N       : out std_logic;
      IB_UP_SRC_RDY_N   : out std_logic;
      IB_UP_DST_RDY_N   : in  std_logic;

      -- MI32 interface - CLK (ICS Clock)
      MI32_DWR          : in  std_logic_vector(31 downto 0);
      MI32_ADDR         : in  std_logic_vector(31 downto 0);
      MI32_RD           : in  std_logic;
      MI32_WR           : in  std_logic;
      MI32_BE           : in  std_logic_vector(3 downto 0);
      MI32_DRD          : out std_logic_vector(31 downto 0);
      MI32_ARDY         : out std_logic;
      MI32_DRDY         : out std_logic
   );
end entity DMA_MOD_4x16b_RXTX;

