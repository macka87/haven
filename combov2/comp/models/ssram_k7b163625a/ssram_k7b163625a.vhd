--
-- SSRAM_K7B163625A.vhd: SSRAM - Samsung K7B163625 512Kx36bit
--                               Synchronous SRAM
--
-- Copyright (C) 2004 CESNET
-- Author(s): Pecenka Tomas <pecenka at liberouter.org>
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SSRAM_K7B163625A is
   generic (
      ADDR_WIDTH  : integer := 19;
      DATA_WIDTH  : integer := 36;
      MEM_INIT    : string  := "";  -- INIT values for SSRAM
      FILE_FORMAT : integer :=  0;  -- 0: Address(hex) Data(hex);
                                    -- 1: Data(hex)
                                    -- 2: Data(bin)
      DEBUG       : integer :=  0   -- Show debug informations 1=ON/0=OFF
   );
   port (
      SCLK      : in std_logic;    -- SSRAM clock
      SCS1      : in std_logic;    --
      SCS2      : in std_logic;    -- Chip Selects
      SMODE     : in std_logic;    -- Linear/Interleaved
      SADSP     : in std_logic;    -- Processor
      SADSC     : in std_logic;    -- Cache
      SADV      : in std_logic;    -- Burst control
      SGW       : in std_logic;    -- Global Write
      SBW       : in std_logic;    -- Byte Write
      SOE       : in std_logic;    -- Output Enable
      SWE       : in std_logic_vector(3 downto 0);  -- Byte Write Select
      SA        : in std_logic_vector(ADDR_WIDTH-1 downto 0); -- Address
      SD        : inout std_logic_vector(DATA_WIDTH-1 downto 0)  -- Data bus
   );
end entity SSRAM_K7B163625A;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SSRAM_K7B163625A_arch of SSRAM_K7B163625A is

   signal gnd : std_logic;
   signal ucc : std_logic;

   signal sig_dq : std_logic_vector(DATA_WIDTH-1 downto 0);

begin

SSRAM_K7B163625A_U : entity work.k7b163625a
   generic map (
      addr_bits   => ADDR_WIDTH,
      data_bits   => DATA_WIDTH,
      mem_sizes   => 2**ADDR_WIDTH - 1,
      file_format => FILE_FORMAT,
      mem_init    => MEM_INIT,
      debug       => DEBUG
   )
   port map (
      A      => SA,
      ADV_N  => SADV,
      ADSP_N => SADSP,
      ADSC_N => SADSC,
      CLK    => SCLK,
      CS1_N  => SCS1,
      CS2    => ucc,
      CS2_N  => SCS2,
      WE_N   => SWE,
      OE_N   => SOE,
      GW_N   => SGW,
      BW_N   => SBW,
      ZZ     => gnd,
      LBO_N  => SMODE,
      DQ     => sig_dq
   );

   wd32 : if DATA_WIDTH = 32 generate
      process(SOE, sig_dq, SD)
      begin
         if SOE = '0' then
            SD <= sig_dq;
            sig_dq <= (others => 'Z');
         else
            sig_dq <= SD;
            SD <= (others => 'Z');
         end if;
      end process;
   end generate;

   wd36 : if DATA_WIDTH = 36 generate
      process(SOE, sig_dq, SD)
      begin
         if SOE = '0' then
            SD(7 downto 0)   <= sig_dq(7 downto 0);
            SD(15 downto 8)  <= sig_dq(16 downto 9);
            SD(23 downto 16) <= sig_dq(25 downto 18);
            SD(31 downto 24) <= sig_dq(34 downto 27);
            SD(32)           <= sig_dq(8);
            SD(33)           <= sig_dq(17);
            SD(34)           <= sig_dq(26);
            SD(35)           <= sig_dq(35);
            sig_dq <= (others => 'Z');
         else
            sig_dq(7 downto 0)   <= SD(7 downto 0);
            sig_dq(16 downto 9)  <= SD(15 downto 8);
            sig_dq(25 downto 18) <= SD(23 downto 16);
            sig_dq(34 downto 27) <= SD(31 downto 24);
            sig_dq(8)            <= SD(32);
            sig_dq(17)           <= SD(33);
            sig_dq(26)           <= SD(34);
            sig_dq(35)           <= SD(35);
            SD <= (others => 'Z');
         end if;
      end process;
   end generate;

   -- GND and UCC signals definition
   gnd <= '0';
   ucc <= '1';

end architecture SSRAM_K7B163625A_arch;

