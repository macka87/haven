-- ntram_k7n643645m.vhd: Samsung NtRAM 2Mx36bit SSRAM
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity ntram_k7n643645m is
   generic(
      ADDR_WIDTH  : integer   := 21;
      DATA_WIDTH  : integer   := 36;
      DEBUG       : integer   := 0
   );
   port(
      SCLK     : in  std_logic;  -- SSRAM clock
      SCKE     : in  std_logic;  -- Clock enable
      SCS      : in  std_logic;  -- Chip select
      SADV     : in  std_logic;  -- Burst control - address advance
      SBW      : in  std_logic_vector(3 downto 0); -- Byte write
      SWE      : in  std_logic;  -- Write/Read (0 => write)
      SOE      : in  std_logic;  -- Output enable
      SA       : in  std_logic_vector(ADDR_WIDTH-1 downto 0);  -- Address
      SD       : inout std_logic_vector(DATA_WIDTH-1 downto 0) -- Data
   );
end entity ntram_k7n643645m;

-- ------------------------------------------------------------------------
--                        Architecture declaration
-- ------------------------------------------------------------------------
architecture vhdl of ntram_k7n643645m is

begin

ntram_k7n643645m_I: entity work.K7N643645M
   generic map(
      addr_bits   => ADDR_WIDTH,
      data_bits   => DATA_WIDTH,
      mem_sizes   => 2*1024*1024 - 1,
      debug       => DEBUG
   )
   port map(
      Dq    => SD,
      Addr  => SA,
      K     => SCLK,
      CKEb  => SCKE,
      Bwa_n => SBW(0),
      Bwb_n => SBW(1),
      Bwc_n => SBW(2),
      Bwd_n => SBW(3),
      WEb   => SWE,
      ADV   => SADV,
      OEb   => SOE,
      CS1b  => SCS,
      CS2   => '1',
      CS2b  => '0',
      LBOb  => '0',
      ZZ    => '0'
   );

end architecture vhdl;
