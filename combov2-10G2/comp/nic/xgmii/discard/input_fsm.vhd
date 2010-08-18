-- input_fsm.vhd: Skips packet gaps
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

entity discard_input_fsm is
port (
   CLK            : in std_logic;
   RESET          : in std_logic;

   RX_SOP         : in std_logic;
   RX_EOP         : in std_logic;

   FIFO_PKT_WR    : out std_logic
);
end entity;

architecture arch of discard_input_fsm is
   
   type fsm_t  is (st_wait_sop, st_wait_eop);
   
   signal state      : fsm_t;
   signal next_state     : fsm_t;

begin
   
   fsm_state : process(CLK, RESET, next_state)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            state <= st_wait_sop;
         else
            state <= next_state;
         end if;
      end if;
   end process;

   fsm_next : process(CLK, state, RX_SOP, RX_EOP)
   begin
      next_state <= state;

      case state is
         when st_wait_sop =>
            if RX_SOP = '1' and RX_EOP = '0' then
               next_state <= st_wait_eop;
            end if;

         when st_wait_eop =>
            if RX_EOP = '1' then
               next_state <= st_wait_sop;
            end if;

      end case;
   end process;

   fsm_output : process(CLK, state, RX_SOP)
   begin
      FIFO_PKT_WR <= '0';

      case state is
         when st_wait_sop =>
            FIFO_PKT_WR <= RX_SOP;

         when st_wait_eop =>
            FIFO_PKT_WR <= '1';

      end case;
   end process;

end architecture;

