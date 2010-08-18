-- crossbar_top.vhd: XGMII to XGMII crossbar, wrapper for direct use
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
--* Top level entity that wraps generic crossbar and MI32 configuration.
---
entity xgmii_crossbar_top is
   generic (
      --+ XGMII ports count
      XGMII_COUNT    : integer := 6;
      XGMII_STRICT   : boolean := false
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;

      --+ XGMII RX:
      XGMII_RXC   : in std_logic_vector
                        (XGMII_COUNT * 8 - 1 downto 0);
      XGMII_RXD   : in std_logic_vector
                        (XGMII_COUNT * 64 - 1 downto 0);
      --+ Packet information RX
      RX_SOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);
      RX_EOP      : in std_logic_vector(XGMII_COUNT - 1 downto 0);

      --+ XGMII TX
      XGMII_TXC   : out std_logic_vector
                        (XGMII_COUNT * 8 - 1 downto 0);
      XGMII_TXD   : out std_logic_vector
                        (XGMII_COUNT * 64 - 1 downto 0);
      --+ Packet information TX
      TX_SOP      : out std_logic_vector(XGMII_COUNT - 1 downto 0);
      TX_EOP      : out std_logic_vector(XGMII_COUNT - 1 downto 0);

      DWR   : in std_logic_vector(31 downto 0);
      ADDR  : in std_logic_vector(31 downto 0);
      RD    : in std_logic;
      WR    : in std_logic;
      --+ MI32 Byte Enables are used!
      BE    : in std_logic_vector(3 downto 0);
      ARDY  : out std_logic;
      DRD   : out std_logic_vector(31 downto 0);
      DRDY  : out std_logic
   );
end entity;


---
-- Architecture
---
architecture behav of xgmii_crossbar_top is

   signal mapping    : std_logic_vector
                     (XGMII_COUNT * log2(XGMII_COUNT) - 1 downto 0);
   signal mapping_we : std_logic;

begin

   simple_crossbar:
   if not XGMII_STRICT generate
      CROSSBAR_GEN_I : entity work.XGMII_CROSSBAR
      generic map (
         XGMII_COUNT => XGMII_COUNT
      )
      port map (
         --+ ports
         XGMII_RXC   => XGMII_RXC,
         XGMII_RXD   => XGMII_RXD,
         XGMII_TXC   => XGMII_TXC,
         XGMII_TXD   => XGMII_TXD,

         RX_SOP      => RX_SOP,
         RX_EOP      => RX_EOP,
         TX_SOP      => TX_SOP,
         TX_EOP      => TX_EOP,

         --+ configuration of the crossbar
         MAPPING     => mapping
      );
   end generate;
   

   strict_crossbar:
   if XGMII_STRICT generate

      CROSSBAR_STRICT_I : entity work.XGMII_CROSSBAR_STRICT
      generic map (
         XGMII_COUNT => XGMII_COUNT
      )
      port map (
         CLK         => CLK,
         RESET       => RESET,

         --+ ports
         XGMII_RXC   => XGMII_RXC,
         XGMII_RXD   => XGMII_RXD,
         XGMII_TXC   => XGMII_TXC,
         XGMII_TXD   => XGMII_TXD,

         RX_SOP      => RX_SOP,
         RX_EOP      => RX_EOP,
         TX_SOP      => TX_SOP,
         TX_EOP      => TX_EOP,

         --+ configuration of the crossbar
         MAPPING     => mapping,
         MAPPING_WE  => mapping_we
      );

   end generate;


   CROSSBAR_CONFIG : entity work.XGMII_CROSSBAR_CONFIG
   generic map (
      XGMII_COUNT => XGMII_COUNT
   )
   port map (
      CLK   => CLK,
      RESET => RESET,
      --+ result of the MI32 communication
      MAPPING     => mapping,
      MAPPING_WE  => mapping_we,

      DWR   => DWR,
      ADDR  => ADDR,
      RD    => RD,
      WR    => WR,
      BE    => BE,
      DRD   => DRD,
      ARDY  => ARDY,
      DRDY  => DRDY
   );

end architecture;

