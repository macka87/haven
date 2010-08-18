-- xgmiii_dec_pdec.vhd: Priority decoder for cmd signal
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity xgmii_dec_pdec is
   port(
      -- Input interface
      DI    : in std_logic_vector(7 downto 0); -- CMD mask signal

      -- Output interface
      -- Position of 1st command byte (one hot)
      DO1   : out std_logic_vector(7 downto 0);
      -- Bits lower than 1st command are set to '1', others to '0'
      DO2   : out std_logic_vector(7 downto 0)
   );
end entity xgmii_dec_pdec;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of xgmii_dec_pdec is

begin

process(DI)
begin
   DO1 <= (others => '0');
   DO2 <= (others => '0');

   for i in 0 to 7 loop
      if (DI(i downto 0)=conv_std_logic_vector((2**i),i+1)) then
         if (i > 0) then
            DO1(i-1 downto 0) <= (others => '0');
            DO2(i-1 downto 0) <= (others => '1');
         end if;
         DO1(i) <= '1';
         DO2(i) <= '0';
         if (i < 7) then
            DO1(7 downto i+1) <= (others => '0');
            DO2(7 downto i+1) <= (others => '0');
         end if;
      end if;
   end loop;
end process;

end architecture behavioral;

