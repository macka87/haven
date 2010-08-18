
-- cmd_decoder.vhd: Decoder from RocketIO to Command Protocol 
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on
use work.commands.all;
use work.rio_codes.ALL;

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity cmd_decoder is
   port (
      -- Input: RocketIO characters
      DI       : in std_logic_vector(7 downto 0);
      DIISK    : in std_logic;

      -- Output: Command protocol
      DO       : out std_logic_vector(7 downto 0);
      DO_CMD   : out std_logic
   );
end cmd_decoder;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of cmd_decoder is

signal command          : std_logic_vector(7 downto 0);

begin

   -- decode K-Chars
   with DI select
      command <=
                  C_CMD_SOP   when K_SOP,
                  C_CMD_TERM  when K_TERM,
                  C_CMD_TERM  when K_EOP,
                  C_CMD_SOC   when K_SOC,
                  C_CMD_IDLE  when others;

   -- decode K-Chars only
   DO <= command when DIISK = '1' else
         DI;
   DO_CMD <= DIISK;

end behavioral;

