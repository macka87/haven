-- tx_fsm.vhd: TX operation control FSM for GMII repeater
-- Copyright (C) 2005 CESNET
-- Author(s):  Stepan Friedl <friedl@liberouter.org>
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

entity rep_tx_fsm is
   port (
      RESET       : in  std_logic;   -- Asynchronous Reset
      CLK         : in  std_logic;   -- Clock
      -- Control inputs
      FIFO_EMPTY  : in  std_logic;
      START       : in  std_logic;
      EOP         : in  std_logic;
      -- Outputs
      UNDERFLOW   : out std_logic;  --
      TX_EN       : out std_logic;  -- Assert TX enable
      TX_ERR      : out std_logic;  -- Assert TX error
      FIFO_RD     : out std_logic;  -- FIFO read enable
      TIMER_START : out std_logic;  -- TX delay counter start
      TIMER_SEL   : out std_logic   -- Select between startup and gap timer
   );
end rep_tx_fsm;

architecture behavioral of rep_tx_fsm is

type TX_FSM_TYPE is (IDLE, STARTUP_WAIT, TX, TX_NEXT, S_UNDERFLOW, DISCARD);

signal present_state : TX_FSM_TYPE;
signal next_state    : TX_FSM_TYPE;

begin

FSM_COMB : process(present_state, FIFO_EMPTY, START, EOP)
begin
   TX_EN       <= '0';
   TX_ERR      <= '0';
   UNDERFLOW   <= '0';
   FIFO_RD     <= '0';
   TIMER_START <= '0';
   TIMER_SEL   <= '0';
   case present_state is
      when IDLE =>
         if (FIFO_EMPTY = '0') then
            TIMER_START <= '1';
            next_state  <= STARTUP_WAIT;
         else
            next_state  <= IDLE;
         end if;

      when STARTUP_WAIT =>
         if START = '1' then
            next_state  <= TX;
         else
            next_state  <= STARTUP_WAIT;
         end if;

      when TX =>
         TX_EN   <= '1';
         FIFO_RD <= '1';
         if (EOP = '1') then
            TX_EN       <= '0';
            next_state  <= TX_NEXT;
         elsif (FIFO_EMPTY = '1') then
            TX_ERR     <= '1';
            UNDERFLOW  <= '1';
            next_state <= S_UNDERFLOW;
         else
            next_state  <= TX;
         end if;

      when TX_NEXT =>
         if (FIFO_EMPTY = '0') then
            TX_EN       <= '0';
            TIMER_START <= '1';
            TIMER_SEL   <= '1';
            next_state  <= STARTUP_WAIT;
         else
            next_state  <= IDLE;
         end if;

      when S_UNDERFLOW =>
         FIFO_RD <= '1';
         TX_EN   <= '0';
         if (EOP = '1') and (FIFO_EMPTY = '1') then
            next_state  <= IDLE;
         elsif (EOP = '1') and (FIFO_EMPTY = '0') then
            TIMER_START <= '1';
            TIMER_SEL   <= '1';
            next_state  <= STARTUP_WAIT;
         else
            next_state  <= DISCARD;
         end if;

      when DISCARD =>
         FIFO_RD <= '1';
         if (EOP = '1') and (FIFO_EMPTY = '1') then
            next_state  <= IDLE;
         elsif (EOP = '1') and (FIFO_EMPTY = '0') then
            TIMER_START <= '1';
            TIMER_SEL   <= '1';
            next_state  <= STARTUP_WAIT;
         else
            next_state  <= DISCARD;
         end if;

      when others =>
         next_state <= IDLE;
   end case;
end process;

FSM_SEQ : process(RESET,CLK)
begin
   if (RESET = '1') then
      present_state    <= IDLE;
   elsif CLK'event and CLK = '1' then
      present_state    <= next_state;
   end if;
end process;

end behavioral;
