--
-- crc32_64b_tab.vhd: A 32-bit CRC table for processing 64 bits in parallel
-- Copyright (C) 2006 CESNET
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
entity crc32_64b_tab is
   port(
      DI    : in  std_logic_vector(63 downto 0);
      MASK  : in  std_logic_vector(2 downto 0);
      DO    : out std_logic_vector(31 downto 0)
   );
end entity crc32_64b_tab;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture crc32_64b_tab_arch of crc32_64b_tab is

signal c_8, c_16, c_24, c_32, c_40, c_48, c_56, c_64 : std_logic_vector(31 downto 0);

begin

   c_8(0) <= DI(2);
   c_8(1) <= DI(0) XOR DI(3);
   c_8(2) <= DI(0) XOR DI(1) XOR DI(4);
   c_8(3) <= DI(1) XOR DI(2) XOR DI(5);
   c_8(4) <= DI(2) XOR DI(3) XOR DI(0) XOR DI(6);
   c_8(5) <= DI(3) XOR DI(4) XOR DI(1) XOR DI(7);
   c_8(6) <= DI(4) XOR DI(5);
   c_8(7) <= DI(5) XOR DI(0) XOR DI(6);
   c_8(8) <= DI(6) XOR DI(1) XOR DI(7);
   c_8(9) <= DI(7);
   c_8(10) <= DI(2);
   c_8(11) <= DI(3);
   c_8(12) <= DI(0) XOR DI(4);
   c_8(13) <= DI(0) XOR DI(1) XOR DI(5);
   c_8(14) <= DI(1) XOR DI(2) XOR DI(6);
   c_8(15) <= DI(2) XOR DI(3) XOR DI(7);
   c_8(16) <= DI(0) XOR DI(2) XOR DI(3) XOR DI(4);
   c_8(17) <= DI(0) XOR DI(1) XOR DI(3) XOR DI(4) XOR DI(5);
   c_8(18) <= DI(1) XOR DI(2) XOR DI(4) XOR DI(5) XOR DI(0) XOR DI(6);
   c_8(19) <= DI(2) XOR DI(3) XOR DI(5) XOR DI(6) XOR DI(1) XOR DI(7);
   c_8(20) <= DI(3) XOR DI(4) XOR DI(6) XOR DI(7);
   c_8(21) <= DI(2) XOR DI(4) XOR DI(5) XOR DI(7);
   c_8(22) <= DI(2) XOR DI(3) XOR DI(5) XOR DI(6);
   c_8(23) <= DI(3) XOR DI(4) XOR DI(6) XOR DI(7);
   c_8(24) <= DI(0) XOR DI(2) XOR DI(4) XOR DI(5) XOR DI(7);
   c_8(25) <= DI(1) XOR DI(2) XOR DI(3) XOR DI(5) XOR DI(0) XOR DI(6);
   c_8(26) <= DI(2) XOR DI(3) XOR DI(4) XOR DI(0) XOR DI(6) XOR DI(1) XOR DI(7);
   c_8(27) <= DI(3) XOR DI(4) XOR DI(5) XOR DI(1) XOR DI(7);
   c_8(28) <= DI(4) XOR DI(5) XOR DI(0) XOR DI(6);
   c_8(29) <= DI(5) XOR DI(0) XOR DI(6) XOR DI(1) XOR DI(7);
   c_8(30) <= DI(0) XOR DI(6) XOR DI(1) XOR DI(7);
   c_8(31) <= DI(1) XOR DI(7);

   c_16(0) <= c_8(8) XOR c_8(2) XOR DI(10);
   c_16(1) <= c_8(9) XOR c_8(0) XOR DI(8) XOR c_8(3) XOR DI(11);
   c_16(2) <= c_8(10) XOR c_8(0) XOR DI(8) XOR c_8(1) XOR DI(9) XOR c_8(4) XOR DI(12);
   c_16(3) <= c_8(11) XOR c_8(1) XOR DI(9) XOR c_8(2) XOR DI(10) XOR c_8(5) XOR DI(13);
   c_16(4) <= c_8(12) XOR c_8(2) XOR DI(10) XOR c_8(3) XOR DI(11) XOR c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14);
   c_16(5) <= c_8(13) XOR c_8(3) XOR DI(11) XOR c_8(4) XOR DI(12) XOR c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);
   c_16(6) <= c_8(14) XOR c_8(4) XOR DI(12) XOR c_8(5) XOR DI(13);
   c_16(7) <= c_8(15) XOR c_8(5) XOR DI(13) XOR c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14);
   c_16(8) <= c_8(16) XOR c_8(6) XOR DI(14) XOR c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);
   c_16(9) <= c_8(17) XOR c_8(7) XOR DI(15);
   c_16(10) <= c_8(18) XOR c_8(2) XOR DI(10);
   c_16(11) <= c_8(19) XOR c_8(3) XOR DI(11);
   c_16(12) <= c_8(20) XOR c_8(0) XOR DI(8) XOR c_8(4) XOR DI(12);
   c_16(13) <= c_8(21) XOR c_8(0) XOR DI(8) XOR c_8(1) XOR DI(9) XOR c_8(5) XOR DI(13);
   c_16(14) <= c_8(22) XOR c_8(1) XOR DI(9) XOR c_8(2) XOR DI(10) XOR c_8(6) XOR DI(14);
   c_16(15) <= c_8(23) XOR c_8(2) XOR DI(10) XOR c_8(3) XOR DI(11) XOR c_8(7) XOR DI(15);
   c_16(16) <= c_8(24) XOR c_8(0) XOR DI(8) XOR c_8(2) XOR DI(10) XOR c_8(3) XOR DI(11) XOR c_8(4) XOR DI(12);
   c_16(17) <= c_8(25) XOR c_8(0) XOR DI(8) XOR c_8(1) XOR DI(9) XOR c_8(3) XOR DI(11) XOR c_8(4) XOR DI(12) XOR c_8(5) XOR DI(13);
   c_16(18) <= c_8(26) XOR c_8(1) XOR DI(9) XOR c_8(2) XOR DI(10) XOR c_8(4) XOR DI(12) XOR c_8(5) XOR DI(13) XOR c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14);
   c_16(19) <= c_8(27) XOR c_8(2) XOR DI(10) XOR c_8(3) XOR DI(11) XOR c_8(5) XOR DI(13) XOR c_8(6) XOR DI(14) XOR c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);
   c_16(20) <= c_8(28) XOR c_8(3) XOR DI(11) XOR c_8(4) XOR DI(12) XOR c_8(6) XOR DI(14) XOR c_8(7) XOR DI(15);
   c_16(21) <= c_8(29) XOR c_8(2) XOR DI(10) XOR c_8(4) XOR DI(12) XOR c_8(5) XOR DI(13) XOR c_8(7) XOR DI(15);
   c_16(22) <= c_8(30) XOR c_8(2) XOR DI(10) XOR c_8(3) XOR DI(11) XOR c_8(5) XOR DI(13) XOR c_8(6) XOR DI(14);
   c_16(23) <= c_8(31) XOR c_8(3) XOR DI(11) XOR c_8(4) XOR DI(12) XOR c_8(6) XOR DI(14) XOR c_8(7) XOR DI(15);
   c_16(24) <= c_8(0) XOR DI(8) XOR c_8(2) XOR DI(10) XOR c_8(4) XOR DI(12) XOR c_8(5) XOR DI(13) XOR c_8(7) XOR DI(15);
   c_16(25) <= c_8(1) XOR DI(9) XOR c_8(2) XOR DI(10) XOR c_8(3) XOR DI(11) XOR c_8(5) XOR DI(13) XOR c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14);
   c_16(26) <= c_8(2) XOR DI(10) XOR c_8(3) XOR DI(11) XOR c_8(4) XOR DI(12) XOR c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14) XOR c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);
   c_16(27) <= c_8(3) XOR DI(11) XOR c_8(4) XOR DI(12) XOR c_8(5) XOR DI(13) XOR c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);
   c_16(28) <= c_8(4) XOR DI(12) XOR c_8(5) XOR DI(13) XOR c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14);
   c_16(29) <= c_8(5) XOR DI(13) XOR c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14) XOR c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);
   c_16(30) <= c_8(6) XOR c_8(0) XOR DI(8) XOR DI(14) XOR c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);
   c_16(31) <= c_8(7) XOR c_8(1) XOR DI(9) XOR DI(15);

   c_24(0) <= c_16(8) XOR c_16(2) XOR DI(18);
   c_24(1) <= c_16(9) XOR c_16(0) XOR DI(16) XOR c_16(3) XOR DI(19);
   c_24(2) <= c_16(10) XOR c_16(0) XOR DI(16) XOR c_16(1) XOR DI(17) XOR c_16(4) XOR DI(20);
   c_24(3) <= c_16(11) XOR c_16(1) XOR DI(17) XOR c_16(2) XOR DI(18) XOR c_16(5) XOR DI(21);
   c_24(4) <= c_16(12) XOR c_16(2) XOR DI(18) XOR c_16(3) XOR DI(19) XOR c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22);
   c_24(5) <= c_16(13) XOR c_16(3) XOR DI(19) XOR c_16(4) XOR DI(20) XOR c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);
   c_24(6) <= c_16(14) XOR c_16(4) XOR DI(20) XOR c_16(5) XOR DI(21);
   c_24(7) <= c_16(15) XOR c_16(5) XOR DI(21) XOR c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22);
   c_24(8) <= c_16(16) XOR c_16(6) XOR DI(22) XOR c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);
   c_24(9) <= c_16(17) XOR c_16(7) XOR DI(23);
   c_24(10) <= c_16(18) XOR c_16(2) XOR DI(18);
   c_24(11) <= c_16(19) XOR c_16(3) XOR DI(19);
   c_24(12) <= c_16(20) XOR c_16(0) XOR DI(16) XOR c_16(4) XOR DI(20);
   c_24(13) <= c_16(21) XOR c_16(0) XOR DI(16) XOR c_16(1) XOR DI(17) XOR c_16(5) XOR DI(21);
   c_24(14) <= c_16(22) XOR c_16(1) XOR DI(17) XOR c_16(2) XOR DI(18) XOR c_16(6) XOR DI(22);
   c_24(15) <= c_16(23) XOR c_16(2) XOR DI(18) XOR c_16(3) XOR DI(19) XOR c_16(7) XOR DI(23);
   c_24(16) <= c_16(24) XOR c_16(0) XOR DI(16) XOR c_16(2) XOR DI(18) XOR c_16(3) XOR DI(19) XOR c_16(4) XOR DI(20);
   c_24(17) <= c_16(25) XOR c_16(0) XOR DI(16) XOR c_16(1) XOR DI(17) XOR c_16(3) XOR DI(19) XOR c_16(4) XOR DI(20) XOR c_16(5) XOR DI(21);
   c_24(18) <= c_16(26) XOR c_16(1) XOR DI(17) XOR c_16(2) XOR DI(18) XOR c_16(4) XOR DI(20) XOR c_16(5) XOR DI(21) XOR c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22);
   c_24(19) <= c_16(27) XOR c_16(2) XOR DI(18) XOR c_16(3) XOR DI(19) XOR c_16(5) XOR DI(21) XOR c_16(6) XOR DI(22) XOR c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);
   c_24(20) <= c_16(28) XOR c_16(3) XOR DI(19) XOR c_16(4) XOR DI(20) XOR c_16(6) XOR DI(22) XOR c_16(7) XOR DI(23);
   c_24(21) <= c_16(29) XOR c_16(2) XOR DI(18) XOR c_16(4) XOR DI(20) XOR c_16(5) XOR DI(21) XOR c_16(7) XOR DI(23);
   c_24(22) <= c_16(30) XOR c_16(2) XOR DI(18) XOR c_16(3) XOR DI(19) XOR c_16(5) XOR DI(21) XOR c_16(6) XOR DI(22);
   c_24(23) <= c_16(31) XOR c_16(3) XOR DI(19) XOR c_16(4) XOR DI(20) XOR c_16(6) XOR DI(22) XOR c_16(7) XOR DI(23);
   c_24(24) <= c_16(0) XOR DI(16) XOR c_16(2) XOR DI(18) XOR c_16(4) XOR DI(20) XOR c_16(5) XOR DI(21) XOR c_16(7) XOR DI(23);
   c_24(25) <= c_16(1) XOR DI(17) XOR c_16(2) XOR DI(18) XOR c_16(3) XOR DI(19) XOR c_16(5) XOR DI(21) XOR c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22);
   c_24(26) <= c_16(2) XOR DI(18) XOR c_16(3) XOR DI(19) XOR c_16(4) XOR DI(20) XOR c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22) XOR c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);
   c_24(27) <= c_16(3) XOR DI(19) XOR c_16(4) XOR DI(20) XOR c_16(5) XOR DI(21) XOR c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);
   c_24(28) <= c_16(4) XOR DI(20) XOR c_16(5) XOR DI(21) XOR c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22);
   c_24(29) <= c_16(5) XOR DI(21) XOR c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22) XOR c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);
   c_24(30) <= c_16(6) XOR c_16(0) XOR DI(16) XOR DI(22) XOR c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);
   c_24(31) <= c_16(7) XOR c_16(1) XOR DI(17) XOR DI(23);

   c_32(0) <= c_24(8) XOR c_24(2) XOR DI(26);
   c_32(1) <= c_24(9) XOR c_24(0) XOR DI(24) XOR c_24(3) XOR DI(27);
   c_32(2) <= c_24(10) XOR c_24(0) XOR DI(24) XOR c_24(1) XOR DI(25) XOR c_24(4) XOR DI(28);
   c_32(3) <= c_24(11) XOR c_24(1) XOR DI(25) XOR c_24(2) XOR DI(26) XOR c_24(5) XOR DI(29);
   c_32(4) <= c_24(12) XOR c_24(2) XOR DI(26) XOR c_24(3) XOR DI(27) XOR c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30);
   c_32(5) <= c_24(13) XOR c_24(3) XOR DI(27) XOR c_24(4) XOR DI(28) XOR c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);
   c_32(6) <= c_24(14) XOR c_24(4) XOR DI(28) XOR c_24(5) XOR DI(29);
   c_32(7) <= c_24(15) XOR c_24(5) XOR DI(29) XOR c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30);
   c_32(8) <= c_24(16) XOR c_24(6) XOR DI(30) XOR c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);
   c_32(9) <= c_24(17) XOR c_24(7) XOR DI(31);
   c_32(10) <= c_24(18) XOR c_24(2) XOR DI(26);
   c_32(11) <= c_24(19) XOR c_24(3) XOR DI(27);
   c_32(12) <= c_24(20) XOR c_24(0) XOR DI(24) XOR c_24(4) XOR DI(28);
   c_32(13) <= c_24(21) XOR c_24(0) XOR DI(24) XOR c_24(1) XOR DI(25) XOR c_24(5) XOR DI(29);
   c_32(14) <= c_24(22) XOR c_24(1) XOR DI(25) XOR c_24(2) XOR DI(26) XOR c_24(6) XOR DI(30);
   c_32(15) <= c_24(23) XOR c_24(2) XOR DI(26) XOR c_24(3) XOR DI(27) XOR c_24(7) XOR DI(31);
   c_32(16) <= c_24(24) XOR c_24(0) XOR DI(24) XOR c_24(2) XOR DI(26) XOR c_24(3) XOR DI(27) XOR c_24(4) XOR DI(28);
   c_32(17) <= c_24(25) XOR c_24(0) XOR DI(24) XOR c_24(1) XOR DI(25) XOR c_24(3) XOR DI(27) XOR c_24(4) XOR DI(28) XOR c_24(5) XOR DI(29);
   c_32(18) <= c_24(26) XOR c_24(1) XOR DI(25) XOR c_24(2) XOR DI(26) XOR c_24(4) XOR DI(28) XOR c_24(5) XOR DI(29) XOR c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30);
   c_32(19) <= c_24(27) XOR c_24(2) XOR DI(26) XOR c_24(3) XOR DI(27) XOR c_24(5) XOR DI(29) XOR c_24(6) XOR DI(30) XOR c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);
   c_32(20) <= c_24(28) XOR c_24(3) XOR DI(27) XOR c_24(4) XOR DI(28) XOR c_24(6) XOR DI(30) XOR c_24(7) XOR DI(31);
   c_32(21) <= c_24(29) XOR c_24(2) XOR DI(26) XOR c_24(4) XOR DI(28) XOR c_24(5) XOR DI(29) XOR c_24(7) XOR DI(31);
   c_32(22) <= c_24(30) XOR c_24(2) XOR DI(26) XOR c_24(3) XOR DI(27) XOR c_24(5) XOR DI(29) XOR c_24(6) XOR DI(30);
   c_32(23) <= c_24(31) XOR c_24(3) XOR DI(27) XOR c_24(4) XOR DI(28) XOR c_24(6) XOR DI(30) XOR c_24(7) XOR DI(31);
   c_32(24) <= c_24(0) XOR DI(24) XOR c_24(2) XOR DI(26) XOR c_24(4) XOR DI(28) XOR c_24(5) XOR DI(29) XOR c_24(7) XOR DI(31);
   c_32(25) <= c_24(1) XOR DI(25) XOR c_24(2) XOR DI(26) XOR c_24(3) XOR DI(27) XOR c_24(5) XOR DI(29) XOR c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30);
   c_32(26) <= c_24(2) XOR DI(26) XOR c_24(3) XOR DI(27) XOR c_24(4) XOR DI(28) XOR c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30) XOR c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);
   c_32(27) <= c_24(3) XOR DI(27) XOR c_24(4) XOR DI(28) XOR c_24(5) XOR DI(29) XOR c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);
   c_32(28) <= c_24(4) XOR DI(28) XOR c_24(5) XOR DI(29) XOR c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30);
   c_32(29) <= c_24(5) XOR DI(29) XOR c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30) XOR c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);
   c_32(30) <= c_24(6) XOR c_24(0) XOR DI(24) XOR DI(30) XOR c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);
   c_32(31) <= c_24(7) XOR c_24(1) XOR DI(25) XOR DI(31);

   c_40(0) <= c_32(8) XOR c_32(2) XOR DI(34);
   c_40(1) <= c_32(9) XOR c_32(0) XOR DI(32) XOR c_32(3) XOR DI(35);
   c_40(2) <= c_32(10) XOR c_32(0) XOR DI(32) XOR c_32(1) XOR DI(33) XOR c_32(4) XOR DI(36);
   c_40(3) <= c_32(11) XOR c_32(1) XOR DI(33) XOR c_32(2) XOR DI(34) XOR c_32(5) XOR DI(37);
   c_40(4) <= c_32(12) XOR c_32(2) XOR DI(34) XOR c_32(3) XOR DI(35) XOR c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38);
   c_40(5) <= c_32(13) XOR c_32(3) XOR DI(35) XOR c_32(4) XOR DI(36) XOR c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);
   c_40(6) <= c_32(14) XOR c_32(4) XOR DI(36) XOR c_32(5) XOR DI(37);
   c_40(7) <= c_32(15) XOR c_32(5) XOR DI(37) XOR c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38);
   c_40(8) <= c_32(16) XOR c_32(6) XOR DI(38) XOR c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);
   c_40(9) <= c_32(17) XOR c_32(7) XOR DI(39);
   c_40(10) <= c_32(18) XOR c_32(2) XOR DI(34);
   c_40(11) <= c_32(19) XOR c_32(3) XOR DI(35);
   c_40(12) <= c_32(20) XOR c_32(0) XOR DI(32) XOR c_32(4) XOR DI(36);
   c_40(13) <= c_32(21) XOR c_32(0) XOR DI(32) XOR c_32(1) XOR DI(33) XOR c_32(5) XOR DI(37);
   c_40(14) <= c_32(22) XOR c_32(1) XOR DI(33) XOR c_32(2) XOR DI(34) XOR c_32(6) XOR DI(38);
   c_40(15) <= c_32(23) XOR c_32(2) XOR DI(34) XOR c_32(3) XOR DI(35) XOR c_32(7) XOR DI(39);
   c_40(16) <= c_32(24) XOR c_32(0) XOR DI(32) XOR c_32(2) XOR DI(34) XOR c_32(3) XOR DI(35) XOR c_32(4) XOR DI(36);
   c_40(17) <= c_32(25) XOR c_32(0) XOR DI(32) XOR c_32(1) XOR DI(33) XOR c_32(3) XOR DI(35) XOR c_32(4) XOR DI(36) XOR c_32(5) XOR DI(37);
   c_40(18) <= c_32(26) XOR c_32(1) XOR DI(33) XOR c_32(2) XOR DI(34) XOR c_32(4) XOR DI(36) XOR c_32(5) XOR DI(37) XOR c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38);
   c_40(19) <= c_32(27) XOR c_32(2) XOR DI(34) XOR c_32(3) XOR DI(35) XOR c_32(5) XOR DI(37) XOR c_32(6) XOR DI(38) XOR c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);
   c_40(20) <= c_32(28) XOR c_32(3) XOR DI(35) XOR c_32(4) XOR DI(36) XOR c_32(6) XOR DI(38) XOR c_32(7) XOR DI(39);
   c_40(21) <= c_32(29) XOR c_32(2) XOR DI(34) XOR c_32(4) XOR DI(36) XOR c_32(5) XOR DI(37) XOR c_32(7) XOR DI(39);
   c_40(22) <= c_32(30) XOR c_32(2) XOR DI(34) XOR c_32(3) XOR DI(35) XOR c_32(5) XOR DI(37) XOR c_32(6) XOR DI(38);
   c_40(23) <= c_32(31) XOR c_32(3) XOR DI(35) XOR c_32(4) XOR DI(36) XOR c_32(6) XOR DI(38) XOR c_32(7) XOR DI(39);
   c_40(24) <= c_32(0) XOR DI(32) XOR c_32(2) XOR DI(34) XOR c_32(4) XOR DI(36) XOR c_32(5) XOR DI(37) XOR c_32(7) XOR DI(39);
   c_40(25) <= c_32(1) XOR DI(33) XOR c_32(2) XOR DI(34) XOR c_32(3) XOR DI(35) XOR c_32(5) XOR DI(37) XOR c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38);
   c_40(26) <= c_32(2) XOR DI(34) XOR c_32(3) XOR DI(35) XOR c_32(4) XOR DI(36) XOR c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38) XOR c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);
   c_40(27) <= c_32(3) XOR DI(35) XOR c_32(4) XOR DI(36) XOR c_32(5) XOR DI(37) XOR c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);
   c_40(28) <= c_32(4) XOR DI(36) XOR c_32(5) XOR DI(37) XOR c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38);
   c_40(29) <= c_32(5) XOR DI(37) XOR c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38) XOR c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);
   c_40(30) <= c_32(6) XOR c_32(0) XOR DI(32) XOR DI(38) XOR c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);
   c_40(31) <= c_32(7) XOR c_32(1) XOR DI(33) XOR DI(39);

   c_48(0) <= c_40(8) XOR c_40(2) XOR DI(42);
   c_48(1) <= c_40(9) XOR c_40(0) XOR DI(40) XOR c_40(3) XOR DI(43);
   c_48(2) <= c_40(10) XOR c_40(0) XOR DI(40) XOR c_40(1) XOR DI(41) XOR c_40(4) XOR DI(44);
   c_48(3) <= c_40(11) XOR c_40(1) XOR DI(41) XOR c_40(2) XOR DI(42) XOR c_40(5) XOR DI(45);
   c_48(4) <= c_40(12) XOR c_40(2) XOR DI(42) XOR c_40(3) XOR DI(43) XOR c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46);
   c_48(5) <= c_40(13) XOR c_40(3) XOR DI(43) XOR c_40(4) XOR DI(44) XOR c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);
   c_48(6) <= c_40(14) XOR c_40(4) XOR DI(44) XOR c_40(5) XOR DI(45);
   c_48(7) <= c_40(15) XOR c_40(5) XOR DI(45) XOR c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46);
   c_48(8) <= c_40(16) XOR c_40(6) XOR DI(46) XOR c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);
   c_48(9) <= c_40(17) XOR c_40(7) XOR DI(47);
   c_48(10) <= c_40(18) XOR c_40(2) XOR DI(42);
   c_48(11) <= c_40(19) XOR c_40(3) XOR DI(43);
   c_48(12) <= c_40(20) XOR c_40(0) XOR DI(40) XOR c_40(4) XOR DI(44);
   c_48(13) <= c_40(21) XOR c_40(0) XOR DI(40) XOR c_40(1) XOR DI(41) XOR c_40(5) XOR DI(45);
   c_48(14) <= c_40(22) XOR c_40(1) XOR DI(41) XOR c_40(2) XOR DI(42) XOR c_40(6) XOR DI(46);
   c_48(15) <= c_40(23) XOR c_40(2) XOR DI(42) XOR c_40(3) XOR DI(43) XOR c_40(7) XOR DI(47);
   c_48(16) <= c_40(24) XOR c_40(0) XOR DI(40) XOR c_40(2) XOR DI(42) XOR c_40(3) XOR DI(43) XOR c_40(4) XOR DI(44);
   c_48(17) <= c_40(25) XOR c_40(0) XOR DI(40) XOR c_40(1) XOR DI(41) XOR c_40(3) XOR DI(43) XOR c_40(4) XOR DI(44) XOR c_40(5) XOR DI(45);
   c_48(18) <= c_40(26) XOR c_40(1) XOR DI(41) XOR c_40(2) XOR DI(42) XOR c_40(4) XOR DI(44) XOR c_40(5) XOR DI(45) XOR c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46);
   c_48(19) <= c_40(27) XOR c_40(2) XOR DI(42) XOR c_40(3) XOR DI(43) XOR c_40(5) XOR DI(45) XOR c_40(6) XOR DI(46) XOR c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);
   c_48(20) <= c_40(28) XOR c_40(3) XOR DI(43) XOR c_40(4) XOR DI(44) XOR c_40(6) XOR DI(46) XOR c_40(7) XOR DI(47);
   c_48(21) <= c_40(29) XOR c_40(2) XOR DI(42) XOR c_40(4) XOR DI(44) XOR c_40(5) XOR DI(45) XOR c_40(7) XOR DI(47);
   c_48(22) <= c_40(30) XOR c_40(2) XOR DI(42) XOR c_40(3) XOR DI(43) XOR c_40(5) XOR DI(45) XOR c_40(6) XOR DI(46);
   c_48(23) <= c_40(31) XOR c_40(3) XOR DI(43) XOR c_40(4) XOR DI(44) XOR c_40(6) XOR DI(46) XOR c_40(7) XOR DI(47);
   c_48(24) <= c_40(0) XOR DI(40) XOR c_40(2) XOR DI(42) XOR c_40(4) XOR DI(44) XOR c_40(5) XOR DI(45) XOR c_40(7) XOR DI(47);
   c_48(25) <= c_40(1) XOR DI(41) XOR c_40(2) XOR DI(42) XOR c_40(3) XOR DI(43) XOR c_40(5) XOR DI(45) XOR c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46);
   c_48(26) <= c_40(2) XOR DI(42) XOR c_40(3) XOR DI(43) XOR c_40(4) XOR DI(44) XOR c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46) XOR c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);
   c_48(27) <= c_40(3) XOR DI(43) XOR c_40(4) XOR DI(44) XOR c_40(5) XOR DI(45) XOR c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);
   c_48(28) <= c_40(4) XOR DI(44) XOR c_40(5) XOR DI(45) XOR c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46);
   c_48(29) <= c_40(5) XOR DI(45) XOR c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46) XOR c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);
   c_48(30) <= c_40(6) XOR c_40(0) XOR DI(40) XOR DI(46) XOR c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);
   c_48(31) <= c_40(7) XOR c_40(1) XOR DI(41) XOR DI(47);

   c_56(0) <= c_48(8) XOR c_48(2) XOR DI(50);
   c_56(1) <= c_48(9) XOR c_48(0) XOR DI(48) XOR c_48(3) XOR DI(51);
   c_56(2) <= c_48(10) XOR c_48(0) XOR DI(48) XOR c_48(1) XOR DI(49) XOR c_48(4) XOR DI(52);
   c_56(3) <= c_48(11) XOR c_48(1) XOR DI(49) XOR c_48(2) XOR DI(50) XOR c_48(5) XOR DI(53);
   c_56(4) <= c_48(12) XOR c_48(2) XOR DI(50) XOR c_48(3) XOR DI(51) XOR c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54);
   c_56(5) <= c_48(13) XOR c_48(3) XOR DI(51) XOR c_48(4) XOR DI(52) XOR c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);
   c_56(6) <= c_48(14) XOR c_48(4) XOR DI(52) XOR c_48(5) XOR DI(53);
   c_56(7) <= c_48(15) XOR c_48(5) XOR DI(53) XOR c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54);
   c_56(8) <= c_48(16) XOR c_48(6) XOR DI(54) XOR c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);
   c_56(9) <= c_48(17) XOR c_48(7) XOR DI(55);
   c_56(10) <= c_48(18) XOR c_48(2) XOR DI(50);
   c_56(11) <= c_48(19) XOR c_48(3) XOR DI(51);
   c_56(12) <= c_48(20) XOR c_48(0) XOR DI(48) XOR c_48(4) XOR DI(52);
   c_56(13) <= c_48(21) XOR c_48(0) XOR DI(48) XOR c_48(1) XOR DI(49) XOR c_48(5) XOR DI(53);
   c_56(14) <= c_48(22) XOR c_48(1) XOR DI(49) XOR c_48(2) XOR DI(50) XOR c_48(6) XOR DI(54);
   c_56(15) <= c_48(23) XOR c_48(2) XOR DI(50) XOR c_48(3) XOR DI(51) XOR c_48(7) XOR DI(55);
   c_56(16) <= c_48(24) XOR c_48(0) XOR DI(48) XOR c_48(2) XOR DI(50) XOR c_48(3) XOR DI(51) XOR c_48(4) XOR DI(52);
   c_56(17) <= c_48(25) XOR c_48(0) XOR DI(48) XOR c_48(1) XOR DI(49) XOR c_48(3) XOR DI(51) XOR c_48(4) XOR DI(52) XOR c_48(5) XOR DI(53);
   c_56(18) <= c_48(26) XOR c_48(1) XOR DI(49) XOR c_48(2) XOR DI(50) XOR c_48(4) XOR DI(52) XOR c_48(5) XOR DI(53) XOR c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54);
   c_56(19) <= c_48(27) XOR c_48(2) XOR DI(50) XOR c_48(3) XOR DI(51) XOR c_48(5) XOR DI(53) XOR c_48(6) XOR DI(54) XOR c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);
   c_56(20) <= c_48(28) XOR c_48(3) XOR DI(51) XOR c_48(4) XOR DI(52) XOR c_48(6) XOR DI(54) XOR c_48(7) XOR DI(55);
   c_56(21) <= c_48(29) XOR c_48(2) XOR DI(50) XOR c_48(4) XOR DI(52) XOR c_48(5) XOR DI(53) XOR c_48(7) XOR DI(55);
   c_56(22) <= c_48(30) XOR c_48(2) XOR DI(50) XOR c_48(3) XOR DI(51) XOR c_48(5) XOR DI(53) XOR c_48(6) XOR DI(54);
   c_56(23) <= c_48(31) XOR c_48(3) XOR DI(51) XOR c_48(4) XOR DI(52) XOR c_48(6) XOR DI(54) XOR c_48(7) XOR DI(55);
   c_56(24) <= c_48(0) XOR DI(48) XOR c_48(2) XOR DI(50) XOR c_48(4) XOR DI(52) XOR c_48(5) XOR DI(53) XOR c_48(7) XOR DI(55);
   c_56(25) <= c_48(1) XOR DI(49) XOR c_48(2) XOR DI(50) XOR c_48(3) XOR DI(51) XOR c_48(5) XOR DI(53) XOR c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54);
   c_56(26) <= c_48(2) XOR DI(50) XOR c_48(3) XOR DI(51) XOR c_48(4) XOR DI(52) XOR c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54) XOR c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);
   c_56(27) <= c_48(3) XOR DI(51) XOR c_48(4) XOR DI(52) XOR c_48(5) XOR DI(53) XOR c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);
   c_56(28) <= c_48(4) XOR DI(52) XOR c_48(5) XOR DI(53) XOR c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54);
   c_56(29) <= c_48(5) XOR DI(53) XOR c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54) XOR c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);
   c_56(30) <= c_48(6) XOR c_48(0) XOR DI(48) XOR DI(54) XOR c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);
   c_56(31) <= c_48(7) XOR c_48(1) XOR DI(49) XOR DI(55);

   c_64(0) <= c_56(8) XOR c_56(2) XOR DI(58);
   c_64(1) <= c_56(9) XOR c_56(0) XOR DI(56) XOR c_56(3) XOR DI(59);
   c_64(2) <= c_56(10) XOR c_56(0) XOR DI(56) XOR c_56(1) XOR DI(57) XOR c_56(4) XOR DI(60);
   c_64(3) <= c_56(11) XOR c_56(1) XOR DI(57) XOR c_56(2) XOR DI(58) XOR c_56(5) XOR DI(61);
   c_64(4) <= c_56(12) XOR c_56(2) XOR DI(58) XOR c_56(3) XOR DI(59) XOR c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62);
   c_64(5) <= c_56(13) XOR c_56(3) XOR DI(59) XOR c_56(4) XOR DI(60) XOR c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);
   c_64(6) <= c_56(14) XOR c_56(4) XOR DI(60) XOR c_56(5) XOR DI(61);
   c_64(7) <= c_56(15) XOR c_56(5) XOR DI(61) XOR c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62);
   c_64(8) <= c_56(16) XOR c_56(6) XOR DI(62) XOR c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);
   c_64(9) <= c_56(17) XOR c_56(7) XOR DI(63);
   c_64(10) <= c_56(18) XOR c_56(2) XOR DI(58);
   c_64(11) <= c_56(19) XOR c_56(3) XOR DI(59);
   c_64(12) <= c_56(20) XOR c_56(0) XOR DI(56) XOR c_56(4) XOR DI(60);
   c_64(13) <= c_56(21) XOR c_56(0) XOR DI(56) XOR c_56(1) XOR DI(57) XOR c_56(5) XOR DI(61);
   c_64(14) <= c_56(22) XOR c_56(1) XOR DI(57) XOR c_56(2) XOR DI(58) XOR c_56(6) XOR DI(62);
   c_64(15) <= c_56(23) XOR c_56(2) XOR DI(58) XOR c_56(3) XOR DI(59) XOR c_56(7) XOR DI(63);
   c_64(16) <= c_56(24) XOR c_56(0) XOR DI(56) XOR c_56(2) XOR DI(58) XOR c_56(3) XOR DI(59) XOR c_56(4) XOR DI(60);
   c_64(17) <= c_56(25) XOR c_56(0) XOR DI(56) XOR c_56(1) XOR DI(57) XOR c_56(3) XOR DI(59) XOR c_56(4) XOR DI(60) XOR c_56(5) XOR DI(61);
   c_64(18) <= c_56(26) XOR c_56(1) XOR DI(57) XOR c_56(2) XOR DI(58) XOR c_56(4) XOR DI(60) XOR c_56(5) XOR DI(61) XOR c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62);
   c_64(19) <= c_56(27) XOR c_56(2) XOR DI(58) XOR c_56(3) XOR DI(59) XOR c_56(5) XOR DI(61) XOR c_56(6) XOR DI(62) XOR c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);
   c_64(20) <= c_56(28) XOR c_56(3) XOR DI(59) XOR c_56(4) XOR DI(60) XOR c_56(6) XOR DI(62) XOR c_56(7) XOR DI(63);
   c_64(21) <= c_56(29) XOR c_56(2) XOR DI(58) XOR c_56(4) XOR DI(60) XOR c_56(5) XOR DI(61) XOR c_56(7) XOR DI(63);
   c_64(22) <= c_56(30) XOR c_56(2) XOR DI(58) XOR c_56(3) XOR DI(59) XOR c_56(5) XOR DI(61) XOR c_56(6) XOR DI(62);
   c_64(23) <= c_56(31) XOR c_56(3) XOR DI(59) XOR c_56(4) XOR DI(60) XOR c_56(6) XOR DI(62) XOR c_56(7) XOR DI(63);
   c_64(24) <= c_56(0) XOR DI(56) XOR c_56(2) XOR DI(58) XOR c_56(4) XOR DI(60) XOR c_56(5) XOR DI(61) XOR c_56(7) XOR DI(63);
   c_64(25) <= c_56(1) XOR DI(57) XOR c_56(2) XOR DI(58) XOR c_56(3) XOR DI(59) XOR c_56(5) XOR DI(61) XOR c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62);
   c_64(26) <= c_56(2) XOR DI(58) XOR c_56(3) XOR DI(59) XOR c_56(4) XOR DI(60) XOR c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62) XOR c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);
   c_64(27) <= c_56(3) XOR DI(59) XOR c_56(4) XOR DI(60) XOR c_56(5) XOR DI(61) XOR c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);
   c_64(28) <= c_56(4) XOR DI(60) XOR c_56(5) XOR DI(61) XOR c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62);
   c_64(29) <= c_56(5) XOR DI(61) XOR c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62) XOR c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);
   c_64(30) <= c_56(6) XOR c_56(0) XOR DI(56) XOR DI(62) XOR c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);
   c_64(31) <= c_56(7) XOR c_56(1) XOR DI(57) XOR DI(63);

with MASK select
   DO          <= c_64 when "000",
                  c_56 when "001",
                  c_48 when "010",
                  c_40 when "011",
                  c_32 when "100",
                  c_24 XOR (X"000000" & DI(31 downto 24)) when "101",
                  c_16 XOR (  X"0000" & DI(31 downto 16)) when "110",
                  c_8  XOR (    X"00" & DI(31 downto  8)) when "111",
                  (others => '0') when others;

end architecture crc32_64b_tab_arch;



