-- crossbar.vhd: XGMII to XGMII crossbar
-- Copyright (C) 2010 CESNET
-- Author(s):  Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

use work.math_pack.ALL;

---
-- Architecture
--
--* Simple stupid crossbar.
--* Doesn't care of XGMII.
---
architecture behav of xgmii_crossbar is

   -- width of the mapping number (to map to output XGMII port)
   constant DEST_WIDTH : integer := log2(XGMII_COUNT);

begin

   assert XGMII_COUNT > 1
      report "Sorry, crossbar for less than 2 XGMII doesn't make sense"
      severity error;

   ---
   -- Generating multiplexors for each output port
   ---
   gen_mux_foreach_tx:
   for i in 0 to XGMII_COUNT - 1 generate
   begin         

      mux: entity work.xgmii_mux
      generic map (
         XGMII_COUNT    => XGMII_COUNT
      )
      port map (
         XGMII_RXD      => XGMII_RXD,
         XGMII_RXC      => XGMII_RXC,
         RX_SOP         => RX_SOP,
         RX_EOP         => RX_EOP,

         XGMII_TXD      => XGMII_TXD((i + 1) * 64 - 1 downto i * 64),
         XGMII_TXC      => XGMII_TXC((i + 1) *  8 - 1 downto i *  8),
         TX_SOP         => TX_SOP(i),
         TX_EOP         => TX_EOP(i),

         SEL            => MAPPING((i + 1) * DEST_WIDTH - 1 downto i * DEST_WIDTH)
      );

-- obsolete:
--      ---
--      -- Data generic MUX
--      ---
--      data_mux_element : entity work.GEN_MUX
--      generic map (
--         DATA_WIDTH => 64,
--         MUX_WIDTH => XGMII_COUNT
--      )
--      port map (
--         DATA_IN => XGMII_RXD,
--         -- get mapping for current output port
--         SEL => MAPPING((i + 1) * DEST_WIDTH - 1 downto i * DEST_WIDTH),
--         DATA_OUT => XGMII_TXD((i + 1) * 64 - 1 downto i * 64)
--      );
--
--      ---
--      -- CTRL generic MUX
--      ---
--      ctrl_mux_element : entity work.GEN_MUX
--      generic map (
--         DATA_WIDTH => 8,
--         MUX_WIDTH => XGMII_COUNT
--      )
--      port map (
--         DATA_IN => XGMII_RXC,
--         -- get mapping for current output port
--         SEL => MAPPING((i + 1) * DEST_WIDTH - 1 downto i * DEST_WIDTH),
--         DATA_OUT => XGMII_TXC((i + 1) * 8 - 1 downto i * 8)
--      );
--
--      ---
--      -- SOP generic mux
--      ---
--      sop_mux : entity work.GEN_MUX
--      generic map (
--         DATA_WIDTH  => 1,
--         MUX_WIDTH   => XGMII_COUNT
--      )
--      port map (
--         DATA_IN   => RX_SOP,
--         SEL       => MAPPING((i + 1) * DEST_WIDTH - 1 downto i * DEST_WIDTH),
--         DATA_OUT(0)  => TX_SOP(i)
--      );
--      
--      ---
--      -- EOP generic mux
--      ---
--      eop_mux : entity work.GEN_MUX
--      generic map (
--         DATA_WIDTH  => 1,
--         MUX_WIDTH   => XGMII_COUNT
--      )
--      port map (
--         DATA_IN   => RX_EOP,
--         SEL       => MAPPING((i + 1) * DEST_WIDTH - 1 downto i * DEST_WIDTH),
--         DATA_OUT(0)  => TX_EOP(i)
--      );
    
   end generate;

end architecture;

