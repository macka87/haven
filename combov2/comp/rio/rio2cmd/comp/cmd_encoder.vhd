
-- cmd_encoder.vhd: Command Protocol to RocketIO Encoder 
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

entity cmd_encoder is
   port (
      -- Input: command protocol
      DI       : in std_logic_vector(7 downto 0);
      DI_CMD   : in std_logic;

      -- Output: RocketIO characters
      DO       : out std_logic_vector(7 downto 0);
      DOISK    : out std_logic
   );
end cmd_encoder;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of cmd_encoder is

signal kchar        : std_logic_vector(7 downto 0);

begin

   -- encode Commands
   with DI select
      kchar <= 
               K_SOP    when C_CMD_SOP,
               K_TERM   when C_CMD_TERM,
               K_SOC    when C_CMD_SOC,
               K_IDLE   when others;

   -- encode commands only
   DO <= kchar when DI_CMD = '1' else
         DI;
   DOISK <= DI_CMD;         

end behavioral;


