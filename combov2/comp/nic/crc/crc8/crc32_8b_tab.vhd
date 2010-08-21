
--
-- CRC32.vhd: 32-bit CRC table for 8 bits at a time
-- Copyright (C) 2005 CESNET
-- Author(s): Bidlo Michal <bidlom@fit.vutbr.cz>
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
entity crc32_8b_tab is
   port(
      DI: in std_logic_vector(7 downto 0);
      CRC: out std_logic_vector(31 downto 0)
   );
end entity crc32_8b_tab;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CRC32_table_8b_arch of crc32_8b_tab is

begin

   CRC(0) <= DI(2);
   CRC(1) <= DI(0) XOR DI(3);
   CRC(2) <= DI(0) XOR DI(1) XOR DI(4);
   CRC(3) <= DI(1) XOR DI(2) XOR DI(5);
   CRC(4) <= DI(2) XOR DI(3) XOR DI(0) XOR DI(6);
   CRC(5) <= DI(3) XOR DI(4) XOR DI(1) XOR DI(7);
   CRC(6) <= DI(4) XOR DI(5);
   CRC(7) <= DI(5) XOR DI(0) XOR DI(6);
   CRC(8) <= DI(6) XOR DI(1) XOR DI(7);
   CRC(9) <= DI(7);
   CRC(10) <= DI(2);
   CRC(11) <= DI(3);
   CRC(12) <= DI(0) XOR DI(4);
   CRC(13) <= DI(0) XOR DI(1) XOR DI(5);
   CRC(14) <= DI(1) XOR DI(2) XOR DI(6);
   CRC(15) <= DI(2) XOR DI(3) XOR DI(7);
   CRC(16) <= DI(0) XOR DI(2) XOR DI(3) XOR DI(4);
   CRC(17) <= DI(0) XOR DI(1) XOR DI(3) XOR DI(4) XOR DI(5);
   CRC(18) <= DI(1) XOR DI(2) XOR DI(4) XOR DI(5) XOR DI(0) XOR DI(6);
   CRC(19) <= DI(2) XOR DI(3) XOR DI(5) XOR DI(6) XOR DI(1) XOR DI(7);
   CRC(20) <= DI(3) XOR DI(4) XOR DI(6) XOR DI(7);
   CRC(21) <= DI(2) XOR DI(4) XOR DI(5) XOR DI(7);
   CRC(22) <= DI(2) XOR DI(3) XOR DI(5) XOR DI(6);
   CRC(23) <= DI(3) XOR DI(4) XOR DI(6) XOR DI(7);
   CRC(24) <= DI(0) XOR DI(2) XOR DI(4) XOR DI(5) XOR DI(7);
   CRC(25) <= DI(1) XOR DI(2) XOR DI(3) XOR DI(5) XOR DI(0) XOR DI(6);
   CRC(26) <= DI(2) XOR DI(3) XOR DI(4) XOR DI(0) XOR DI(6) XOR DI(1) XOR DI(7);
   CRC(27) <= DI(3) XOR DI(4) XOR DI(5) XOR DI(1) XOR DI(7);
   CRC(28) <= DI(4) XOR DI(5) XOR DI(0) XOR DI(6);
   CRC(29) <= DI(5) XOR DI(0) XOR DI(6) XOR DI(1) XOR DI(7);
   CRC(30) <= DI(0) XOR DI(6) XOR DI(1) XOR DI(7);
   CRC(31) <= DI(1) XOR DI(7);

end architecture CRC32_table_8b_arch;

