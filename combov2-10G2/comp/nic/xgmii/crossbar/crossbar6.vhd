-- crossbar6.vhd: XGMII to XGMII crossbar wrapper for 6 ports
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
--* Crossbar for 6 duplex ports.
--* Configuration by MI32.
---
entity xgmii_crossbar6 is
   generic (
      XGMII_STRICT   : boolean := false
   );
   port (
      CLK         : in std_logic;
      RESET       : in std_logic;

      --+ SOP/EOP/ERR
      RX_SOP      : in std_logic_vector(5 downto 0);   
      RX_EOP      : in std_logic_vector(5 downto 0);   
      TX_SOP      : out std_logic_vector(5 downto 0);   
      TX_EOP      : out std_logic_vector(5 downto 0);   

      --+ XGMII port RX 0
      XGMII_RXC0   : in std_logic_vector(7 downto 0);
      XGMII_RXD0   : in std_logic_vector(63 downto 0);
      --+ XGMII port TX 0
      XGMII_TXC0   : out std_logic_vector(7 downto 0);
      XGMII_TXD0   : out std_logic_vector(63 downto 0);

      --+ XGMII port RX 1
      XGMII_RXC1   : in std_logic_vector(7 downto 0);
      XGMII_RXD1   : in std_logic_vector(63 downto 0);
      --+ XGMII port TX 1
      XGMII_TXC1   : out std_logic_vector(7 downto 0);
      XGMII_TXD1   : out std_logic_vector(63 downto 0);

      --+ XGMII port RX 2
      XGMII_RXC2   : in std_logic_vector(7 downto 0);
      XGMII_RXD2   : in std_logic_vector(63 downto 0);
      --+ XGMII port TX 2
      XGMII_TXC2   : out std_logic_vector(7 downto 0);
      XGMII_TXD2   : out std_logic_vector(63 downto 0);

      --+ XGMII port RX 3
      XGMII_RXC3   : in std_logic_vector(7 downto 0);
      XGMII_RXD3   : in std_logic_vector(63 downto 0);
      --+ XGMII port TX 3
      XGMII_TXC3   : out std_logic_vector(7 downto 0);
      XGMII_TXD3   : out std_logic_vector(63 downto 0);

      --+ XGMII port RX 4
      XGMII_RXC4   : in std_logic_vector(7 downto 0);
      XGMII_RXD4   : in std_logic_vector(63 downto 0);
      --+ XGMII port TX 4
      XGMII_TXC4   : out std_logic_vector(7 downto 0);
      XGMII_TXD4   : out std_logic_vector(63 downto 0);

      --+ XGMII port RX 5
      XGMII_RXC5   : in std_logic_vector(7 downto 0);
      XGMII_RXD5   : in std_logic_vector(63 downto 0);
      --+ XGMII port TX 5
      XGMII_TXC5   : out std_logic_vector(7 downto 0);
      XGMII_TXD5   : out std_logic_vector(63 downto 0);

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

---
-- Architecture
---
architecture behav of xgmii_crossbar6 is

begin

   -- instance of the generic crossbar component
   CROSSBAR_U : entity work.XGMII_CROSSBAR_TOP
   generic map (
      XGMII_COUNT    => 6,
      XGMII_STRICT   => XGMII_STRICT
   )
   port map (
      CLK   => CLK,
      RESET => RESET,

      XGMII_RXC( 7 downto  0)    => XGMII_RXC0,
      XGMII_RXC(15 downto  8)    => XGMII_RXC1,
      XGMII_RXC(23 downto 16)    => XGMII_RXC2,
      XGMII_RXC(31 downto 24)    => XGMII_RXC3,
      XGMII_RXC(39 downto 32)    => XGMII_RXC4,
      XGMII_RXC(47 downto 40)    => XGMII_RXC5,
      
      XGMII_RXD( 63 downto   0)  => XGMII_RXD0,
      XGMII_RXD(127 downto  64)  => XGMII_RXD1,
      XGMII_RXD(191 downto 128)  => XGMII_RXD2,
      XGMII_RXD(255 downto 192)  => XGMII_RXD3,
      XGMII_RXD(319 downto 256)  => XGMII_RXD4,
      XGMII_RXD(383 downto 320)  => XGMII_RXD5,

      XGMII_TXC( 7 downto  0)    => XGMII_TXC0,
      XGMII_TXC(15 downto  8)    => XGMII_TXC1,
      XGMII_TXC(23 downto 16)    => XGMII_TXC2,
      XGMII_TXC(31 downto 24)    => XGMII_TXC3,
      XGMII_TXC(39 downto 32)    => XGMII_TXC4,
      XGMII_TXC(47 downto 40)    => XGMII_TXC5,
      
      XGMII_TXD( 63 downto   0)  => XGMII_TXD0,
      XGMII_TXD(127 downto  64)  => XGMII_TXD1,
      XGMII_TXD(191 downto 128)  => XGMII_TXD2,
      XGMII_TXD(255 downto 192)  => XGMII_TXD3,
      XGMII_TXD(319 downto 256)  => XGMII_TXD4,
      XGMII_TXD(383 downto 320)  => XGMII_TXD5,

      RX_SOP   => RX_SOP,
      RX_EOP   => RX_EOP,
      TX_SOP   => TX_SOP,
      TX_EOP   => TX_EOP,

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
