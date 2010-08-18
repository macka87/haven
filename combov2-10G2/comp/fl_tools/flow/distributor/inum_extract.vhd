-- inum_extract.vhd: Extracts interface number from RX_DATA.
-- Copyright (C) 2004 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity inum_extract is
   generic (
      DATA_WIDTH : integer := 32;
      INUM_WIDTH : integer := 2;
      INUM_OFFSET : integer := 0
   );
   port (
      signal RX_DATA : in std_logic_vector(DATA_WIDTH-1 downto 0);
      signal RX_REM : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      signal RX_EOP_N : in std_logic;
      signal LAST_INUM : in std_logic_vector(INUM_WIDTH-1 downto 0);
      signal INUM : out std_logic_vector(INUM_WIDTH-1 downto 0)
   );
end entity inum_extract;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of inum_extract is

   constant DATA_SIZE : integer := DATA_WIDTH / 8;
   constant INUM_LAST_BYTE : integer := (INUM_OFFSET / 8) mod DATA_SIZE;

begin

   get_inum : process(RX_DATA, RX_EOP_N, RX_REM)
   begin
      if INUM_LAST_BYTE <= RX_REM or RX_EOP_N = '1' then
         -- INUM is contained in the RX_DATA
         INUM <= RX_DATA((INUM_OFFSET mod DATA_WIDTH) + INUM_WIDTH - 1 downto (INUM_OFFSET mod DATA_WIDTH));

      else
         INUM <= LAST_INUM;

      end if;
   end process;

end architecture; 

