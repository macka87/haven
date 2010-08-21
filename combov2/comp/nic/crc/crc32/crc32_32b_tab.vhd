--
-- CRC32.vhd: 32-bit CRC table for CRC32 module processing 32 bits in parallel
-- (8 bit version)
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
entity crc32_32b_tab is
   port(
      DI: in std_logic_vector(31 downto 0);
      CRC: out std_logic_vector(31 downto 0)
   );
end entity crc32_32b_tab;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture crc32_32b_tab_arch of crc32_32b_tab is

begin

   CRC(0) <= DI(8) XOR DI(3) XOR DI(4) XOR DI(6) XOR DI(22) XOR DI(7) XOR DI(23) XOR DI(2) XOR DI(0) XOR DI(16) XOR DI(1) XOR DI(20) XOR DI(26);
   CRC(1) <= DI(9) XOR DI(4) XOR DI(5) XOR DI(7) XOR DI(23) XOR DI(8) XOR DI(24) XOR DI(3) XOR DI(1) XOR DI(17) XOR DI(2) XOR DI(21) XOR DI(27);
   CRC(2) <= DI(10) XOR DI(5) XOR DI(6) XOR DI(8) XOR DI(24) XOR DI(9) XOR DI(25) XOR DI(4) XOR DI(0) XOR DI(2) XOR DI(18) XOR DI(3) XOR DI(22) XOR DI(28);
   CRC(3) <= DI(11) XOR DI(6) XOR DI(7) XOR DI(9) XOR DI(25) XOR DI(10) XOR DI(26) XOR DI(5) XOR DI(1) XOR DI(3) XOR DI(19) XOR DI(4) XOR DI(23) XOR DI(29);
   CRC(4) <= DI(12) XOR DI(7) XOR DI(8) XOR DI(10) XOR DI(26) XOR DI(11) XOR DI(27) XOR DI(6) XOR DI(2) XOR DI(4) XOR DI(20) XOR DI(5) XOR DI(24) XOR DI(30);
   CRC(5) <= DI(13) XOR DI(8) XOR DI(9) XOR DI(11) XOR DI(27) XOR DI(12) XOR DI(28) XOR DI(7) XOR DI(3) XOR DI(5) XOR DI(21) XOR DI(6) XOR DI(0) XOR DI(25) XOR DI(31);
   CRC(6) <= DI(14) XOR DI(9) XOR DI(10) XOR DI(2) XOR DI(12) XOR DI(16) XOR DI(28) XOR DI(0) XOR DI(3) XOR DI(20) XOR DI(13) XOR DI(23) XOR DI(29);
   CRC(7) <= DI(15) XOR DI(10) XOR DI(11) XOR DI(3) XOR DI(13) XOR DI(17) XOR DI(29) XOR DI(1) XOR DI(4) XOR DI(21) XOR DI(14) XOR DI(24) XOR DI(30);
   CRC(8) <= DI(16) XOR DI(11) XOR DI(12) XOR DI(4) XOR DI(14) XOR DI(18) XOR DI(30) XOR DI(2) XOR DI(5) XOR DI(22) XOR DI(15) XOR DI(0) XOR DI(25) XOR DI(31);
   CRC(9) <= DI(17) XOR DI(4) XOR DI(8) XOR DI(20) XOR DI(12) XOR DI(13) XOR DI(7) XOR DI(2) XOR DI(5) XOR DI(22) XOR DI(15) XOR DI(0) XOR DI(19) XOR DI(31);
   CRC(10) <= DI(7) XOR DI(18) XOR DI(4) XOR DI(5) XOR DI(9) XOR DI(21) XOR DI(13) XOR DI(22) XOR DI(2) XOR DI(0) XOR DI(14) XOR DI(26);
   CRC(11) <= DI(8) XOR DI(19) XOR DI(5) XOR DI(6) XOR DI(10) XOR DI(22) XOR DI(14) XOR DI(23) XOR DI(3) XOR DI(1) XOR DI(15) XOR DI(27);
   CRC(12) <= DI(9) XOR DI(20) XOR DI(6) XOR DI(7) XOR DI(11) XOR DI(23) XOR DI(15) XOR DI(24) XOR DI(4) XOR DI(2) XOR DI(16) XOR DI(28);
   CRC(13) <= DI(10) XOR DI(21) XOR DI(7) XOR DI(8) XOR DI(12) XOR DI(24) XOR DI(16) XOR DI(25) XOR DI(5) XOR DI(0) XOR DI(3) XOR DI(17) XOR DI(29);
   CRC(14) <= DI(11) XOR DI(22) XOR DI(8) XOR DI(9) XOR DI(13) XOR DI(25) XOR DI(17) XOR DI(26) XOR DI(6) XOR DI(1) XOR DI(4) XOR DI(0) XOR DI(18) XOR DI(30);
   CRC(15) <= DI(12) XOR DI(23) XOR DI(9) XOR DI(10) XOR DI(14) XOR DI(26) XOR DI(18) XOR DI(27) XOR DI(7) XOR DI(2) XOR DI(5) XOR DI(1) XOR DI(19) XOR DI(31);
   CRC(16) <= DI(13) XOR DI(7) XOR DI(23) XOR DI(24) XOR DI(10) XOR DI(26) XOR DI(1) XOR DI(11) XOR DI(15) XOR DI(27) XOR DI(4) XOR DI(19) XOR DI(16) XOR DI(22) XOR DI(28);
   CRC(17) <= DI(14) XOR DI(8) XOR DI(24) XOR DI(25) XOR DI(11) XOR DI(27) XOR DI(2) XOR DI(12) XOR DI(16) XOR DI(28) XOR DI(5) XOR DI(20) XOR DI(17) XOR DI(23) XOR DI(29);
   CRC(18) <= DI(15) XOR DI(9) XOR DI(25) XOR DI(26) XOR DI(12) XOR DI(28) XOR DI(3) XOR DI(13) XOR DI(17) XOR DI(29) XOR DI(6) XOR DI(21) XOR DI(0) XOR DI(18) XOR DI(24) XOR DI(30);
   CRC(19) <= DI(16) XOR DI(10) XOR DI(26) XOR DI(27) XOR DI(13) XOR DI(29) XOR DI(4) XOR DI(14) XOR DI(18) XOR DI(30) XOR DI(7) XOR DI(22) XOR DI(1) XOR DI(0) XOR DI(19) XOR DI(25) XOR DI(31);
   CRC(20) <= DI(17) XOR DI(11) XOR DI(27) XOR DI(16) XOR DI(28) XOR DI(4) XOR DI(14) XOR DI(30) XOR DI(7) XOR DI(3) XOR DI(5) XOR DI(6) XOR DI(22) XOR DI(15) XOR DI(0) XOR DI(19) XOR DI(31);
   CRC(21) <= DI(26) XOR DI(18) XOR DI(12) XOR DI(28) XOR DI(17) XOR DI(29) XOR DI(2) XOR DI(3) XOR DI(5) XOR DI(22) XOR DI(15) XOR DI(0) XOR DI(31);
   CRC(22) <= DI(22) XOR DI(7) XOR DI(8) XOR DI(26) XOR DI(27) XOR DI(19) XOR DI(13) XOR DI(29) XOR DI(2) XOR DI(20) XOR DI(18) XOR DI(30);
   CRC(23) <= DI(23) XOR DI(8) XOR DI(9) XOR DI(27) XOR DI(28) XOR DI(20) XOR DI(14) XOR DI(30) XOR DI(3) XOR DI(21) XOR DI(0) XOR DI(19) XOR DI(31);
   CRC(24) <= DI(8) XOR DI(24) XOR DI(9) XOR DI(10) XOR DI(26) XOR DI(16) XOR DI(28) XOR DI(23) XOR DI(29) XOR DI(7) XOR DI(2) XOR DI(3) XOR DI(21) XOR DI(6) XOR DI(15) XOR DI(31);
   CRC(25) <= DI(9) XOR DI(25) XOR DI(10) XOR DI(26) XOR DI(11) XOR DI(27) XOR DI(17) XOR DI(23) XOR DI(29) XOR DI(6) XOR DI(1) XOR DI(2) XOR DI(20) XOR DI(24) XOR DI(30);
   CRC(26) <= DI(10) XOR DI(26) XOR DI(11) XOR DI(27) XOR DI(12) XOR DI(28) XOR DI(18) XOR DI(24) XOR DI(30) XOR DI(7) XOR DI(2) XOR DI(3) XOR DI(21) XOR DI(25) XOR DI(31);
   CRC(27) <= DI(11) XOR DI(27) XOR DI(12) XOR DI(16) XOR DI(28) XOR DI(20) XOR DI(13) XOR DI(23) XOR DI(29) XOR DI(7) XOR DI(2) XOR DI(6) XOR DI(1) XOR DI(0) XOR DI(19) XOR DI(25) XOR DI(31);
   CRC(28) <= DI(12) XOR DI(16) XOR DI(22) XOR DI(28) XOR DI(13) XOR DI(17) XOR DI(23) XOR DI(29) XOR DI(6) XOR DI(4) XOR DI(21) XOR DI(0) XOR DI(14) XOR DI(24) XOR DI(30);
   CRC(29) <= DI(13) XOR DI(17) XOR DI(23) XOR DI(29) XOR DI(14) XOR DI(18) XOR DI(24) XOR DI(30) XOR DI(7) XOR DI(5) XOR DI(22) XOR DI(1) XOR DI(15) XOR DI(0) XOR DI(25) XOR DI(31);
   CRC(30) <= DI(4) XOR DI(20) XOR DI(14) XOR DI(18) XOR DI(24) XOR DI(30) XOR DI(7) XOR DI(3) XOR DI(22) XOR DI(15) XOR DI(19) XOR DI(25) XOR DI(31);
   CRC(31) <= DI(7) XOR DI(2) XOR DI(3) XOR DI(5) XOR DI(21) XOR DI(6) XOR DI(22) XOR DI(1) XOR DI(15) XOR DI(0) XOR DI(19) XOR DI(25) XOR DI(31);

end architecture crc32_32b_tab_arch;
