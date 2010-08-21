-- packet_fsm.vhd: Notifies about "in packet"/"out packet" state
-- Copyright (C) 2010 CESNET
-- Author(s):  Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

use work.math_pack.ALL;

---
-- Entity
---
entity packet_fsm is
   port (
      CLK   : in std_logic;
      RESET : in std_logic;

      --+ Packet boundary
      SOP   : in std_logic;
      EOP   : in std_logic;

      --+ Product fo the FSM
      INSIDE_PACKET  : out std_logic
   );
end entity;


---
-- Architecture
---

architecture behav of packet_fsm is
   
   type state_t is (st_pkt, st_gap);

   signal state      : state_t;
   signal next_state : state_t;
begin

   fsm_state: process(CLK, RESET, next_state)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            state <= st_gap;
         else
            state <= next_state;
         end if;
      end if;
   end process;

   fsm_next: process(CLK, state, SOP, EOP)
   begin
      next_state  <= state;

      case state is
         when st_gap =>
            if SOP = '1' and EOP = '0' then
               next_state  <= st_pkt;
            end if;

         when st_pkt =>
            if SOP = '0' and EOP = '1' then
               next_state <= st_gap;
            end if;

      end case;
   end process;

   fsm_output: process(CLK, state, SOP, EOP)
   begin
      case state is
         when st_gap =>
            INSIDE_PACKET  <= SOP and not EOP;

         when st_pkt =>
            INSIDE_PACKET  <= '1';

      end case;
   end process;

end architecture;
