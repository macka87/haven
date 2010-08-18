
-- flow_ctrl_fsm.vhd: AURVC Flow Control Unit FSM 
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

entity flow_ctrl_fsm is
   port (
      -- Common Input
      CLK      : in std_logic;
      RESET    : in std_logic;

      -- Input
      CHNL_VALID     : in std_logic;
      XON_XOFF       : in std_logic;
      BUSY           : in std_logic;

      -- Output
      READ           : out std_logic;
      XON            : out std_logic;
      XOFF           : out std_logic;
      REG_CHNL_MASK_RST  : out std_logic 
   );
end flow_ctrl_fsm;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of flow_ctrl_fsm is

type t_state is (WAIT_FOR_CHNL, REQ_TXMSG, WAIT_FOR_TXMSG);
signal present_state, next_state: t_state;  
signal xon_i, xoff_i : std_logic;

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_CHNL;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, CHNL_VALID, XON_XOFF, BUSY)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_CHNL => 
      next_state <= WAIT_FOR_CHNL;
      if (CHNL_VALID = '1') then
         next_state <= REQ_TXMSG;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when REQ_TXMSG => 
      next_state <= WAIT_FOR_TXMSG;
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_TXMSG => 
      next_state <= WAIT_FOR_TXMSG;
      if (BUSY = '0') then
         next_state <= WAIT_FOR_CHNL;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when others => 
      next_state <= WAIT_FOR_CHNL;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;
      
xon_i <= '1' when XON_XOFF = C_XON else
       '0';
xoff_i <= '1' when XON_XOFF = C_XOFF else
        '0';

-- -------------------------------------------------------
output_logic: process(present_state, CHNL_VALID, xon_i, xoff_i, BUSY)
begin
   READ           <= '0';
   XON            <= '0';
   XOFF           <= '0';
   REG_CHNL_MASK_RST  <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when REQ_TXMSG => 
      READ <= '1'; 
      XON <= xon_i; 
      XOFF <= xoff_i;
   -- - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_TXMSG => 
      REG_CHNL_MASK_RST <= not BUSY;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

end behavioral;

