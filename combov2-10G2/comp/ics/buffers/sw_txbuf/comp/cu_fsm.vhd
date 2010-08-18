-- cu_fsm.vhd: Control Unit FSM
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity SWT_CU_FSM is
   generic(
      HW_HEADER_LENGTH : integer
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      EMPTY          : in  std_logic;
      HEADER_LAST_WORD : in std_logic;
      PACKET_LAST_WORD : in  std_logic;
      SEND_ACK_RDY   : in  std_logic;

      -- output signals
      READ_CTRL      : out std_logic;
      SEND_ACK       : out std_logic;
      PACKET_ENABLE  : out std_logic;
      HEADER_ENABLE  : out std_logic
   );
end entity SWT_CU_FSM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of SWT_CU_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_IDLE, S_SEND_HEADER, S_SEND_PACKET, S_FINALIZE );
   
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin

   -- ------------------ Sync logic -------------------------------------------
   sync_logic  : process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            present_state <= S_IDLE;
         else
            present_state <= next_state;
         end if;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process(present_state, EMPTY, HEADER_LAST_WORD, 
                              PACKET_LAST_WORD, SEND_ACK_RDY)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_IDLE =>
         if EMPTY = '0' then
            if HW_HEADER_LENGTH > 0 then
               next_state <= S_SEND_HEADER;
            else
               next_state <= S_SEND_PACKET;
            end if;
         else
            next_state <= S_IDLE;
         end if;
      
      -- ---------------------------------------------
      when S_SEND_HEADER =>
         if HEADER_LAST_WORD = '1' then
            next_state <= S_SEND_PACKET;
         else
            next_state <= S_SEND_HEADER;
         end if;

      -- ---------------------------------------------
      when S_SEND_PACKET =>
         if PACKET_LAST_WORD = '1' then
            next_state <= S_FINALIZE;
         else
            next_state <= S_SEND_PACKET;
         end if;

      -- ---------------------------------------------
      when S_FINALIZE =>
         if SEND_ACK_RDY = '1' then
            next_state <= S_IDLE;
         else
            next_state <= S_FINALIZE;
         end if;

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, EMPTY, SEND_ACK_RDY )
   begin
   
      -- ---------------------------------------------
      -- Initial values
      READ_CTRL         <= '0';
      SEND_ACK          <= '0';
      PACKET_ENABLE     <= '0';
      HEADER_ENABLE     <= '0';

      case (present_state) is
      
      -- ---------------------------------------------
      when S_IDLE =>
         READ_CTRL   <= not EMPTY;
      
      -- ---------------------------------------------
      when S_SEND_HEADER =>
         HEADER_ENABLE   <= '1';

      -- ---------------------------------------------
      when S_SEND_PACKET =>
         PACKET_ENABLE   <= '1';

      -- ---------------------------------------------
      when S_FINALIZE =>
         SEND_ACK   <= SEND_ACK_RDY;

      end case;
   end process output_logic;

end architecture full;
