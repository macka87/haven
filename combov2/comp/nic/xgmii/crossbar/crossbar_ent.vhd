-- crossbar_ent.vhd: XGMII to XGMII crossbar
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
-- Entity
--
--* Generic crossbar to interconnect XGMII ports
--* with dynamic mapping (in -> out).
---
entity xgmii_crossbar is
   generic (
      -- XGMII ports count
      XGMII_COUNT : integer := 6
   );
   port (
      --+ XGMII RX
      XGMII_RXC   : in std_logic_vector
                        (XGMII_COUNT * 8 - 1 downto 0);
      XGMII_RXD   : in std_logic_vector
                        (XGMII_COUNT * 64 - 1 downto 0);
      --+ Packet info RX
      RX_SOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);
      RX_EOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);

      --+ XGMII TX
      XGMII_TXC   : out std_logic_vector
                        (XGMII_COUNT * 8 - 1 downto 0);
      XGMII_TXD   : out std_logic_vector
                        (XGMII_COUNT * 64 - 1 downto 0);
      --+ Packet info TX
      TX_SOP      : out std_logic_vector(XGMII_COUNT - 1 downto 0);
      TX_EOP      : out std_logic_vector(XGMII_COUNT - 1 downto 0);

      --+ Configuration
      --* <pre>| src(0) | ... | src(XGMII_COUNT - 1) |</pre>
      --* mapping:
      --*   TX(i) <= RX(src(i))
      MAPPING     : in std_logic_vector
                        (XGMII_COUNT * log2(XGMII_COUNT) - 1 downto 0)
   );
end entity;

