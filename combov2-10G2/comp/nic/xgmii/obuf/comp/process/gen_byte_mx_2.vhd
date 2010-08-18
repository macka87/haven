-- gen_byte_mx_2.vhd: generic_2 inputs byte multiplexer
-- Copyright (C) 2008 CESNET
-- Author(s): Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use IEEE.std_logic_arith.all;


-- ----------------------------------------------------------------------------
--                                Entity
-- ----------------------------------------------------------------------------

entity gen_byte_mx_2 is

   generic(
      -- number of byte_mx_with 2 inputs
      SIZE : integer
   );
   
   port(
      -- data inputs
      DATA_IN_1, DATA_IN_2    : in std_logic_vector (SIZE*8-1 downto 0);
      -- select signal
      SEL                     : in std_logic_vector (SIZE-1 downto 0);
      -- data output
      DATA_OUT                : out std_logic_vector (SIZE*8-1 downto 0)
   );
   
end entity gen_byte_mx_2;


-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture gen_byte_mx_2_arch of gen_byte_mx_2 is

begin

   -- generic byte multiplexer with 2 inputs
   gen_mx: for i in 1 to SIZE generate
      process (SEL, DATA_IN_1, DATA_IN_2)
      begin
         case SEL(i-1) is
            when '1' =>
               DATA_OUT(i*8-1 downto (i-1)*8)
               <= DATA_IN_2(i*8-1 downto (i-1)*8);
            when '0' =>
               DATA_OUT(i*8-1 downto (i-1)*8)
               <= DATA_IN_1(i*8-1 downto (i-1)*8);
            when others => null;
         end case;
      end process;
   end generate gen_mx;

end architecture gen_byte_mx_2_arch;
