-- rx_fsm.vhd: RX operation control FSM for GMII repeater
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

entity rep_rx_fsm is
   port (
      RESET       : in  std_logic;   -- Asynchronous Reset
      CLK         : in  std_logic;   -- Clock
      -- Control inputs
      RX_DV       : in  std_logic;
      RX_ERR      : in  std_logic;
      FIFO_FULL   : in  std_logic;
      -- Outputs
      OVERFLOW    : out std_logic;  -- FIFO overflow pulse
      FIFO_WR     : out std_logic;  -- FIFO write enable
      EOP         : out std_logic;  -- END of packet indicator
      ERR         : out std_logic   -- Error indicator
   );
end rep_rx_fsm;

architecture behavioral of rep_rx_fsm is

type RX_FSM_TYPE is (IDLE, RX, WRITE_EOP, S_OVERFLOW, EOP_DISCARD, DISCARD);

signal present_state : RX_FSM_TYPE;
signal next_state    : RX_FSM_TYPE;

begin

FSM_COMB : process(present_state, FIFO_FULL, RX_DV, RX_ERR)
begin
   EOP         <= '0';
   ERR         <= '0';
   FIFO_WR     <= '0';
   OVERFLOW    <= '0';
   case present_state is
      -- Idle state
      when IDLE =>
         if (RX_DV = '1') and (RX_ERR = '0') then
            FIFO_WR     <= '1';
            next_state  <= RX;
         else
            next_state  <= IDLE;
         end if;

      -- Packet receive operation
      when RX =>
         FIFO_WR <= '1';
         if (RX_DV = '1') and (FIFO_FULL = '1') then
            next_state <= S_OVERFLOW; -- FIFO full within the packet
            OVERFLOW   <= '1';
         elsif (RX_DV = '0') and (FIFO_FULL = '1') then
            next_state <= WRITE_EOP;  -- FIFO full at the end of the packet
         elsif (RX_DV = '0') and (FIFO_FULL = '0') then
            EOP  <= '1';              -- Normal end of the packet
            next_state <= IDLE;
         else
            next_state <= RX;         -- Receive continues
         end if;

      -- Write EOP flag into the FIFO
      when WRITE_EOP =>
         FIFO_WR <= '1';
         EOP     <= '1';
         if (FIFO_FULL = '0') then
            next_state <= IDLE;
         else
            next_state <= WRITE_EOP;
         end if;

      -- Write Error flag into the FIFO
      when S_OVERFLOW =>
         FIFO_WR <= '1';
         ERR        <= '1';
         if (FIFO_FULL = '0') then
            next_state <= EOP_DISCARD;
         else
            next_state <= S_OVERFLOW;
         end if;

      -- Write EOP flag into the FIFO and discard the rest of packet
      when EOP_DISCARD =>
         FIFO_WR <= '1';
         EOP     <= '1';
         if (FIFO_FULL = '0') then
            next_state <= DISCARD;
         else
            next_state <= EOP_DISCARD;
         end if;

      -- Discard the rest of the packet
      when DISCARD =>
         if (RX_DV = '0') then
            next_state <= IDLE;
         else
            next_state <= DISCARD;
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
