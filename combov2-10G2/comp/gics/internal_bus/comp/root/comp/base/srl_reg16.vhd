--
-- shr_reg16.vhd: 16 Bit Shift register
-- Copyright (C) 2008 CESNET
-- Author(s): Petr Kobierský <kobiersky@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
 
-- ----------------------------------------------------------------------------
--                           ENTITY DECLARATION                              --
-- ---------------------------------------------------------------------------- 
entity SRL_REG16 is 
   port (
      CLK            : in  std_logic;
      DATA           : in  std_logic;
      CE             : in  std_logic;
      A              : in  std_logic_vector(3 downto 0);
      Q              : out std_logic
   );
end entity SRL_REG16;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------
architecture FULL of SRL_REG16 is
   
   constant DEPTH_WIDTH : integer := 16;
   type     SRL_ARRAY is array (0 to DEPTH_WIDTH-1) of std_logic;
   signal   SRL_SIG : SRL_ARRAY;

begin

-- ----------------------------------------------------------------------------
srlp : process (CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (CE = '1') then
            SRL_SIG <= DATA & SRL_SIG(0 to DEPTH_WIDTH-2);
         end if;
      end if;
   end process;

Q <= SRL_SIG(conv_integer(A));

end architecture FULL;
