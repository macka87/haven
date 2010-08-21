--
-- pcs_mx_in_fsm.vhd: RXLOST FSM
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity pcs_mx_in_fsm is
   port(
      -- Common signals
      RESET    : in std_logic;
      CLK      : in std_logic;

      -- Input signals
      RXLOST   : in std_logic;
      PPS      : in std_logic;

      -- Output signals
      FSM_INIT : out std_logic;
      FSM_CNTCE: out std_logic
   );
end entity pcs_mx_in_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of pcs_mx_in_fsm is
   type t_state is (WAIT_FOR_RXLOST, WAIT_FOR_PPS);
   signal present_state, next_state : t_state;

begin


-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_RXLOST;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, RXLOST, PPS)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_RXLOST =>
      next_state <= WAIT_FOR_RXLOST;
      if (RXLOST='1') then
         next_state <= WAIT_FOR_PPS;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_PPS =>
      next_state <= WAIT_FOR_PPS;
      if (PPS='1') then
         next_state <= WAIT_FOR_RXLOST;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when others =>
      next_state <= WAIT_FOR_RXLOST;
   -- - - - - - - - - - - - - - - - - - - - - - -
   end case;
end process next_state_logic;

-- -------------------------------------------------------
output_logic : process(present_state, RXLOST)
begin
   FSM_CNTCE   <= '0';
   FSM_INIT    <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_RXLOST =>
      if (RXLOST='1') then
         FSM_INIT    <= '1';
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when WAIT_FOR_PPS =>
      FSM_CNTCE   <= '1';
   -- - - - - - - - - - - - - - - - - - - - - - -
   when others =>
   end case;
end process output_logic;

end architecture behavioral;

