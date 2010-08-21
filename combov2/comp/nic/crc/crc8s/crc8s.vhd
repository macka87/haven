--   crc.vhd : Component which computes crc
--   Copyright (C) 2003 CESNET
--   Author(s): Martin Zadnik <xzadni00@stud.fit.vutbr.cz>
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
--      - what I have to do
-- 


library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

entity crc8s is
  port (
         CLK     : in std_logic;
         RESET   : in std_logic;
         INIT    : in std_logic;
         DATA    : in std_logic_vector(7 downto 0);--incoming data
         REG_OUT : out std_logic_vector(31 downto 0);--32 registr with CRC
         DATA_VALID  : in std_logic  --enables register

      );
end crc8s;

architecture Behavioral of crc8s is

   signal crc_reg:std_logic_vector(31 downto 0);
   signal next_crc:std_logic_vector(31 downto 0);

begin

  process (CLK,RESET,DATA_VALID)
  begin
   if RESET='1' then   --asynchronous PRESET active High , preset to "FFFF"
      crc_reg <= "11111111111111111111111111111111";
   elsif (CLK'event and CLK='1') then  --CLK rising edge
      if (INIT='1') then
         crc_reg <= (others =>'1');
      elsif DATA_VALID='1' then
         crc_reg <= next_crc;
		end if;
	end if;
  end process;


   REG_OUT <= crc_reg;

	------------Xor equations for CALCulating next value of CRC---
   next_crc(0) <= DATA(6) xor DATA(0) xor crc_reg(24) xor crc_reg(30);
   next_crc(1) <= DATA(7) xor DATA(6) xor DATA(1) xor DATA(0) xor crc_reg(24)
                  xor crc_reg(25) xor crc_reg(30) xor crc_reg(31);
   next_crc(2) <= DATA(7) xor DATA(6) xor DATA(2) xor DATA(1) xor DATA(0) xor
                  crc_reg(24) xor crc_reg(25) xor crc_reg(26) xor crc_reg(30)
                  xor crc_reg(31);
   next_crc(3) <= DATA(7) xor DATA(3) xor DATA(2) xor DATA(1) xor crc_reg(25)
                  xor crc_reg(26) xor crc_reg(27) xor crc_reg(31);
   next_crc(4) <= DATA(6) xor DATA(4) xor DATA(3) xor DATA(2) xor DATA(0) xor
                  crc_reg(24) xor crc_reg(26) xor crc_reg(27) xor crc_reg(28)
                  xor crc_reg(30);
   next_crc(5) <= DATA(7) xor DATA(6) xor DATA(5) xor DATA(4) xor DATA(3) xor
                  DATA(1) xor DATA(0) xor crc_reg(24) xor crc_reg(25) xor
                  crc_reg(27) xor crc_reg(28) xor crc_reg(29) xor crc_reg(30)
                  xor crc_reg(31);
   next_crc(6) <= DATA(7) xor DATA(6) xor DATA(5) xor DATA(4) xor DATA(2) xor
                  DATA(1) xor crc_reg(25) xor crc_reg(26) xor crc_reg(28) xor
                  crc_reg(29) xor crc_reg(30) xor crc_reg(31);
   next_crc(7) <= DATA(7) xor DATA(5) xor DATA(3) xor DATA(2) xor DATA(0) xor
                  crc_reg(24) xor crc_reg(26) xor crc_reg(27) xor crc_reg(29)
                  xor crc_reg(31);
   next_crc(8) <= DATA(4) xor DATA(3) xor DATA(1) xor DATA(0) xor crc_reg(0)
                  xor crc_reg(24) xor crc_reg(25) xor crc_reg(27) xor
                  crc_reg(28);
   next_crc(9) <= DATA(5) xor DATA(4) xor DATA(2) xor DATA(1) xor crc_reg(1)
                  xor crc_reg(25) xor crc_reg(26) xor crc_reg(28) xor
                  crc_reg(29);
   next_crc(10) <= DATA(5) xor DATA(3) xor DATA(2) xor DATA(0) xor crc_reg(2)
                   xor crc_reg(24) xor crc_reg(26) xor crc_reg(27) xor
                   crc_reg(29);
   next_crc(11) <= DATA(4) xor DATA(3) xor DATA(1) xor DATA(0) xor crc_reg(3)
                   xor crc_reg(24) xor crc_reg(25) xor crc_reg(27) xor
                   crc_reg(28);
   next_crc(12) <= DATA(6) xor DATA(5) xor DATA(4) xor DATA(2) xor DATA(1) xor
                   DATA(0) xor crc_reg(4) xor crc_reg(24) xor crc_reg(25) xor
                   crc_reg(26) xor crc_reg(28) xor crc_reg(29) xor crc_reg(30);
   next_crc(13) <= DATA(7) xor DATA(6) xor DATA(5) xor DATA(3) xor DATA(2) xor
                   DATA(1) xor crc_reg(5) xor crc_reg(25) xor crc_reg(26) xor
                   crc_reg(27) xor crc_reg(29) xor crc_reg(30) xor crc_reg(31);
   next_crc(14) <= DATA(7) xor DATA(6) xor DATA(4) xor DATA(3) xor DATA(2) xor
                   crc_reg(6) xor crc_reg(26) xor crc_reg(27) xor crc_reg(28)
                   xor crc_reg(30) xor crc_reg(31);
   next_crc(15) <= DATA(7) xor DATA(5) xor DATA(4) xor DATA(3) xor crc_reg(7)
                   xor crc_reg(27) xor crc_reg(28) xor crc_reg(29) xor
                   crc_reg(31);
   next_crc(16) <= DATA(5) xor DATA(4) xor DATA(0) xor crc_reg(8) xor
                   crc_reg(24) xor crc_reg(28) xor crc_reg(29);
   next_crc(17) <= DATA(6) xor DATA(5) xor DATA(1) xor crc_reg(9) xor
                   crc_reg(25) xor crc_reg(29) xor crc_reg(30);
   next_crc(18) <= DATA(7) xor DATA(6) xor DATA(2) xor crc_reg(10) xor
                   crc_reg(26) xor crc_reg(30) xor crc_reg(31);
   next_crc(19) <= DATA(7) xor DATA(3) xor crc_reg(11) xor crc_reg(27)
                   xor crc_reg(31);
   next_crc(20) <= DATA(4) xor crc_reg(12) xor crc_reg(28);
   next_crc(21) <= DATA(5) xor crc_reg(13) xor crc_reg(29);
   next_crc(22) <= DATA(0) xor crc_reg(14) xor crc_reg(24);
   next_crc(23) <= DATA(6) xor DATA(1) xor DATA(0) xor crc_reg(15) xor crc_reg(24)
                   xor crc_reg(25) xor crc_reg(30);
   next_crc(24) <= DATA(7) xor DATA(2) xor DATA(1) xor crc_reg(16) xor crc_reg(25)
                   xor crc_reg(26) xor crc_reg(31);
   next_crc(25) <= DATA(3) xor DATA(2) xor crc_reg(17) xor crc_reg(26) xor
                   crc_reg(27);
   next_crc(26) <= DATA(6) xor DATA(4) xor DATA(3) xor DATA(0) xor crc_reg(18) xor
                   crc_reg(24) xor crc_reg(27) xor crc_reg(28) xor crc_reg(30);
   next_crc(27) <= DATA(7) xor DATA(5) xor DATA(4) xor DATA(1) xor crc_reg(19) xor
                   crc_reg(25) xor crc_reg(28) xor crc_reg(29) xor crc_reg(31);
   next_crc(28) <= DATA(6) xor DATA(5) xor DATA(2) xor crc_reg(20) xor crc_reg(26)
                   xor crc_reg(29) xor crc_reg(30);
   next_crc(29) <= DATA(7) xor DATA(6) xor DATA(3) xor crc_reg(21) xor crc_reg(27)
                   xor crc_reg(30) xor crc_reg(31);
   next_crc(30) <= DATA(7) xor DATA(4) xor crc_reg(22) xor crc_reg(28) xor
                   crc_reg(31);
   next_crc(31) <= DATA(5) xor crc_reg(23) xor crc_reg(29);
--------------------------------------------------------------------------
end Behavioral;
