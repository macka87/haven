-- ssram_empty.vhd: SSRAM empty component
-- 
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--            Tomas Pecenka <pecenka at liberouter.org>
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

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SSRAM_EMPTY is
   generic(
      ADDR_WIDTH  : integer := 19;
      DATA_WIDTH  : integer := 36
   ); 
   port(
      -- SSRAM interface
      SA       : out std_logic_vector(ADDR_WIDTH-1 downto 0);   -- Address
      SADSP_N  : out std_logic;           -- Processor
      SADSC_N  : out std_logic;           -- Cache
      SADV_N   : out std_logic;           -- Burst control
      SCS1_N   : out std_logic;
      SCS2_N   : out std_logic;           -- Chip Selects
      SGW_N    : out std_logic;           -- Global Write
      SBW_N    : out std_logic;           -- Byte Write
      SWE_N    : out std_logic_vector(3 downto 0);    -- Byte Write Select
      SOE_N    : out std_logic;           -- Output Enable
      SCLK     : out std_logic;           -- SSRAM clock
      SMODE    : out std_logic;           -- Linear/Interleaved (only C6)
      SD       : inout std_logic_vector(DATA_WIDTH-1 downto 0) -- Data bus
	);
end entity SSRAM_EMPTY;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture SSRAM_EMPTY_arch of SSRAM_EMPTY is

   signal empty_sig : std_logic_vector((DATA_WIDTH-1) downto 0);

begin
   empty_sig <= SD;             -- DATA_WIDTH
                                --------------
                                -- DATA_WIDTH

      -- SSRAM interface
      SA       <= (others => '0');
      SADSP_N  <= '1';
      SADSC_N  <= '1'; 
      SADV_N   <= '1'; 
      SCS1_N   <= '1'; 
      SCS2_N   <= '1'; 
      SGW_N    <= '1'; 
      SBW_N    <= '1'; 
      SWE_N    <= "1111"; 
      SOE_N    <= '1'; 
      SCLK     <= '0'; 
      SMODE    <= '0';
      SD       <= (others => 'Z');

end architecture SSRAM_EMPTY_arch; 

