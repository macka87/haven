-- top_level.vhd: DMA test application toplevel for PCIe2IB Bridge
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
use work.ib_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TOP_LEVEL is
   port(
      -- Common Interface
      CLK           : in  std_logic;
      RESET         : in  std_logic;
      
      -- Internal Bus Interface
      -- DOWNSTREAM
      IB_DOWN_DATA        : in  std_logic_vector(63 downto 0);
      IB_DOWN_SOP_N       : in  std_logic;
      IB_DOWN_EOP_N       : in  std_logic;
      IB_DOWN_SRC_RDY_N   : in  std_logic;
      IB_DOWN_DST_RDY_N   : out std_logic;
      -- UPSTREAM
      IB_UP_DATA          : out std_logic_vector(63 downto 0);
      IB_UP_SOP_N         : out std_logic;
      IB_UP_EOP_N         : out std_logic;
      IB_UP_SRC_RDY_N     : out std_logic;
      IB_UP_DST_RDY_N     : in  std_logic
      );
end entity TOP_LEVEL;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SYNTH of TOP_LEVEL IS

   signal ib_bus64 : t_internal_bus64;

begin

   ib_bus64.down.DATA      <= IB_DOWN_DATA;
   ib_bus64.down.SOP_N     <= IB_DOWN_SOP_N;
   ib_bus64.down.EOP_N     <= IB_DOWN_EOP_N;
   ib_bus64.down.SRC_RDY_N <= IB_DOWN_SRC_RDY_N;
   IB_DOWN_DST_RDY_N       <= ib_bus64.down.DST_RDY_N;
    
   IB_UP_DATA              <= ib_bus64.up.DATA;
   IB_UP_SOP_N             <= ib_bus64.up.SOP_N;
   IB_UP_EOP_N             <= ib_bus64.up.EOP_N;
   IB_UP_SRC_RDY_N         <= ib_bus64.up.SRC_RDY_N;
   ib_bus64.up.DST_RDY_N   <= IB_UP_DST_RDY_N;

-- ----------------------------------------------------------------------------
DMA_TEST_U : entity work.DMA_TEST
   port map(
      -- Common Interface
      CLK           => CLK,
      RESET         => RESET,
      -- Internal Bus Interface
      INTERNAL_BUS  => ib_bus64
   );
end architecture SYNTH;
