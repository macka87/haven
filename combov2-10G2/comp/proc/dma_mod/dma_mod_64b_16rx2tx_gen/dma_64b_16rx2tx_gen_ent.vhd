-- dma_64b_16rx2tx_ent.vhd: DMA Module for 16 RX and 2 TX interfaces
-- Copyright (C) 2010 CESNET
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

use work.dma_mod_64b_16rx2tx_gen_const.all;

entity DMA_MOD_64b_16RX2TX_GEN is
   port(
      -- ICS Clock and RESET - drives the whole module
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Synchronous at CLK
      RX_INTERRUPT   : out std_logic;
      TX_INTERRUPT   : out std_logic;
      
      -- input interface
      RX_DATA       : in  std_logic_vector(63 downto 0);
      RX_DREM       : in  std_logic_vector(2 downto 0);
      RX_SOF_N      : in  std_logic;
      RX_EOF_N      : in  std_logic;
      RX_SOP_N      : in  std_logic;
      RX_EOP_N      : in  std_logic;
      RX_SRC_RDY_N  : in  std_logic;
      RX_DST_RDY_N  : out std_logic_vector(15 downto 0);
      -- Determine the number of channel. Must be valid for each data word.
      RX_CHANNEL    : in  std_logic_vector(3 downto 0);

      -- output interfaces
      TX0_DATA       : out std_logic_vector(63 downto 0);
      TX0_DREM       : out std_logic_vector(2 downto 0);
      TX0_SOF_N      : out std_logic;
      TX0_EOF_N      : out std_logic;
      TX0_SOP_N      : out std_logic;
      TX0_EOP_N      : out std_logic;
      TX0_SRC_RDY_N  : out std_logic;
      TX0_DST_RDY_N  : in  std_logic;

      TX1_DATA       : out std_logic_vector(63 downto 0);
      TX1_DREM       : out std_logic_vector(2 downto 0);
      TX1_SOF_N      : out std_logic;
      TX1_EOF_N      : out std_logic;
      TX1_SOP_N      : out std_logic;
      TX1_EOP_N      : out std_logic;
      TX1_SRC_RDY_N  : out std_logic;
      TX1_DST_RDY_N  : in  std_logic;

      -- Internal Bus - CLK (ICS Clock)
      IB_DOWN_DATA   : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOF_N  : in  std_logic;
      IB_DOWN_EOF_N  : in  std_logic;
      IB_DOWN_SRC_RDY_N:in std_logic;
      IB_DOWN_DST_RDY_N:out std_logic;
      IB_UP_DATA     : out std_logic_vector(63 downto 0);
      IB_UP_SOF_N    : out std_logic;
      IB_UP_EOF_N    : out std_logic;
      IB_UP_SRC_RDY_N: out std_logic;
      IB_UP_DST_RDY_N: in  std_logic;

      -- MI32 Interface
      MI32_DWR         : in  std_logic_vector(31 downto 0);
      MI32_ADDR        : in  std_logic_vector(31 downto 0);
      MI32_BE          : in  std_logic_vector(3 downto 0);
      MI32_RD          : in  std_logic;
      MI32_WR          : in  std_logic;
      MI32_DRDY        : out std_logic;
      MI32_ARDY        : out std_logic;
      MI32_DRD         : out std_logic_vector(31 downto 0) 
   );
end entity DMA_MOD_64b_16RX2TX_GEN;

