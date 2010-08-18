
-- message_tx.vhd: Message coder and transmitter 
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

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity message_tx is
   generic (
      DATA_PATHS  : integer      -- Number of bytes of data port
   );
   port (
      -- Common Input
      CLK   : in std_logic;
      RESET : in std_logic;

      -- Flow Controller Interface
      IFC_ID   : in std_logic_vector(7 downto 0);
      XON      : in std_logic;
      XOFF     : in std_logic;
      BUSY     : out std_logic;

      -- Aurora UFC TX Interface
      UFC_TX_DATA    : out std_logic_vector((DATA_PATHS*8)-1 downto 0); -- Big Endian format!!!
      UFC_TX_REQ_N   : out std_logic;
      UFC_TX_MS      : out std_logic_vector(0 to 2);
      UFC_TX_ACK_N   : in std_logic
   );
end message_tx;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of message_tx is

type t_state is (WAIT_FOR_REQ, WAIT_FOR_ACK, TRANSMIT_MSG);
signal present_state, next_state: t_state;  

signal ifc_id_padding   : std_logic_vector((DATA_PATHS*8)-9 downto 1);
   signal reg_xon_xoff : std_logic;

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_REQ;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, XON, XOFF, UFC_TX_ACK_N)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_REQ => 
      next_state <= WAIT_FOR_REQ;
      if (XON = '1') or (XOFF = '1') then
         next_state <= WAIT_FOR_ACK;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_ACK => 
      next_state <= WAIT_FOR_ACK;
      if (UFC_TX_ACK_N = '0') then
         next_state <= TRANSMIT_MSG;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when TRANSMIT_MSG => 
      next_state <= WAIT_FOR_REQ;
      if (XON = '1') or (XOFF = '1') then
         next_state <= WAIT_FOR_ACK;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      next_state <= WAIT_FOR_REQ;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;
      

process(RESET, CLK)
begin
   if (RESET = '1') then
      reg_xon_xoff <= '0';
   elsif (CLK'event AND CLK = '1') then
      if (XON = '1') then
         reg_xon_xoff <= C_XON;
      elsif (XOFF = '1') then
         reg_xon_xoff <= C_XOFF;
      end if;
   end if;
end process;

-- -------------------------------------------------------
output_logic: process(present_state, IFC_ID, ifc_id_padding, reg_xon_xoff)
begin
   BUSY           <= '0';
   ifc_id_padding <= (others => '0');
   UFC_TX_DATA    <= IFC_ID & ifc_id_padding & reg_xon_xoff;
   UFC_TX_REQ_N   <= '1';
   UFC_TX_MS      <= "011";

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_ACK => 
      BUSY <= '1'; 
      UFC_TX_REQ_N <= '0';
   -- - - - - - - - - - - - - - - - - - - - -
   when others => 
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

end behavioral;

