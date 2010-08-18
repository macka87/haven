-- ssram_cy7c1380d.vhd: Cypress 512Kx36 SSRAM
--
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
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
use IEEE.std_logic_1164.all;
-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity ssram_cy7c1380d is
   generic(
      ADDR_WIDTH  : integer   := 19;
      DATA_WIDTH  : integer   := 36;
      DEBUG       : integer   := 0
   );
   port(
      SCLK     : in  std_logic;  -- SSRAM clock
      SADSC    : in  std_logic;  -- Controller address strobe
      SADSP    : in  std_logic;  -- Processor address strobe
      SCS1     : in  std_logic;  -- Chip select nCS1
      SCS2     : in  std_logic;  -- Chip select CS2
--       SCS3     : in  std_logic;  -- Chip select nCS3
      SADV     : in  std_logic;  -- Burst control - address advance
      SBW      : in  std_logic;  -- Byte write enable
      SWE      : in  std_logic_vector(3 downto 0); -- Byte write
      SGW      : in  std_logic;  -- Write/Read (0 => write)
      SOE      : in  std_logic;  -- Output enable
      SA       : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- Address
      SD       : inout std_logic_vector(DATA_WIDTH-1 downto 0) -- Data
   );
end entity ssram_cy7c1380d;

-- ------------------------------------------------------------------------
--                        Architecture declaration
-- ------------------------------------------------------------------------
architecture vhdl of ssram_cy7c1380d is

begin

ssram_cy7c1380d_I: entity work.CY7C1380D
   generic map(
      addr_bits   => ADDR_WIDTH,
      data_bits   => DATA_WIDTH
   )
   port map(
      iZZ      => '0',
      iMode    => '0',
      iADDR    => SA,
      inGW     => SGW,
      inBWE    => SBW,
      inBWd    => SWE(3),
      inBWc    => SWE(2),
      inBWb    => SWE(1),
      inBWa    => SWE(0),
      inCE1    => SCS1,
      iCE2     => SCS2,
      inCE3    => '0',
      inADSP   => SADSP,
      inADSC   => SADSC,
      inADV    => SADV,
      inOE     => SOE,
      ioDQ     => SD,
      iCLK     => SCLK
   );

end architecture vhdl;
