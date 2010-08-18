-- crossbar_config_ent.vhd: XGMII to XGMII crossbar configurator
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
--* MI32 configurator of crossbar
---
entity xgmii_crossbar_config is
   generic (
      --+ XGMII ports count
      XGMII_COUNT : integer := 6
   );
   port (
      --+ common signals
      CLK     : in std_logic;
      RESET   : in std_logic;

      --+ readed mapping for the XGMII_CROSSBAR
      MAPPING     : out std_logic_vector
                        (XGMII_COUNT * log2(XGMII_COUNT) - 1 downto 0);
      --+ write enable of the mapping to some output register
      MAPPING_WE  : out std_logic;
   
      --+ MI32 DWR
      DWR   : in std_logic_vector(31 downto 0);
      --+ MI32 ADDR
      ADDR  : in std_logic_vector(31 downto 0);
      --+ MI32 RD
      RD    : in std_logic;
      --+ MI32 WR
      WR    : in std_logic;
      --+ MI32 Byte Enables are used!
      BE    : in std_logic_vector(3 downto 0);
      --+ MI32 ARDY
      ARDY  : out std_logic;
      --+ MI32 DRD
      DRD   : out std_logic_vector(31 downto 0);
      --+ MI32 DRDY
      DRDY  : out std_logic
   );
end entity;

