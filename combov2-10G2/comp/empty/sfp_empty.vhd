--
-- sfp_empty.vhd: SFP empty entity
--
-- Copyright (C) 2006 CESNET
-- Author(s): Tomas Malek tomalek@liberouter.org
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
-- $ID:$
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all; 

-- ----------------------------------------------------------------------------
--                    ENTITY DECLARATION                                     --
-- ---------------------------------------------------------------------------- 

entity SFP_EMPTY is
   port(
      -- SFP:
      TXDIS    : out   std_logic;
      TXFAULT  : in    std_logic;
      RXLOSS   : in    std_logic;
      MODDEF   : inout std_logic_vector(2 downto 0);
      RS       : out   std_logic
   );                    
end entity SFP_EMPTY;


-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture SFP_EMPTY_arch of SFP_EMPTY is

   signal empty_sig : std_logic_vector(4 downto 0);

begin

   empty_sig <=   TXFAULT  & --  1
                  RXLOSS   & --  1
                  MODDEF;    --  3
                             --------------
                             --  5

   MODDEF   <= (others => 'Z');
   TXDIS    <= '0';
   RS       <= '0';

end architecture SFP_EMPTY_arch;  


