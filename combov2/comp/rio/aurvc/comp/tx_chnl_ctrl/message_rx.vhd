
-- message_rx.vhd: Message receiver and decoder 
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
use work.aurvc_pkg.all; 
use work.math_pack.all; 

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity message_rx is
   generic (
      DATA_PATHS  : integer      -- Number of bytes of data port
   );
   port (
      -- Common Input
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Aurora UFC RX Interface
      UFC_RX_DATA       : in std_logic_vector((DATA_PATHS*8)-1 downto 0);
      UFC_RX_SRC_RDY_N  : in std_logic;
      UFC_RX_SOF_N      : in std_logic;
      UFC_RX_EOF_N      : in std_logic;
      UFC_RX_REM        : in std_logic_vector(log2(DATA_PATHS)-1 downto 0);

      -- Decoded Output
      IFC_ID            : out std_logic_vector(7 downto 0);
      XON               : out std_logic;
      XOFF              : out std_logic
   );
end message_rx;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of message_rx is

   signal output_valid  : std_logic;
   
begin
-- -------------------------------------------------------------
-- Message structure:
--
-- UFC_RX_DATA(15 downto 8) -> IFC_ID
-- UFC_RX_DATA(0)           -> XON/XOFF switch
-- UFC_RX_DATA(others)      -> RESERVED (tied to '0')

output_valid <= UFC_RX_SOF_N nor UFC_RX_SRC_RDY_N;

XON <= '1' when (UFC_RX_DATA(0) = C_XON) and (output_valid = '1') else
       '0';
XOFF <= '1' when (UFC_RX_DATA(0) = C_XOFF) and (output_valid = '1') else
        '0';
        
IFC_ID <= UFC_RX_DATA(DATA_PATHS*8 - 1 downto DATA_PATHS*7);

end behavioral;

