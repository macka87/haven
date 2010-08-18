--
-- sh_fifo_fsm.vhd: Shift-registers FIFO FSM
--
-- Copyright (C) 2007 CESNET
-- Author(s): Petr Mikusek <petr.mikusek@liberouter.org>
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
entity sh_fifo_fsm is
   port (
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      WE             : in  std_logic;
      RE             : in  std_logic;
      CMP_FULL       : in  std_logic;
      CMP_EMPTY      : in  std_logic;

      FULL           : out std_logic;
      EMPTY          : out std_logic;
      CNT_ADDR_CE    : out std_logic;
      CNT_ADDR_DIR   : out std_logic;
      SHREG_CE       : out std_logic
   );
end entity sh_fifo_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of sh_fifo_fsm is

   type t_state is (S_RELAY, S_EMPTY, S_FULL);
   -- don't change state order! optimized generation of empty and full signals

   signal present_state, next_state : t_state;
  
begin -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   sync_fsm: process(RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= S_EMPTY;
      elsif (CLK'event and CLK = '1') then
         present_state <= next_state;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   next_state_logic: process(present_state, WE, RE, CMP_FULL, CMP_EMPTY)
   begin
      case (present_state) is
      -- ------------------------------
      when S_EMPTY =>
         next_state <= S_EMPTY;
         if (WE = '1') then
            next_state <= S_RELAY;
         end if;
      -- ------------------------------
      when S_RELAY =>
         next_state <= S_RELAY;
         if (WE = '1' and RE = '0' and CMP_FULL = '1') then
            next_state <= S_FULL;
         elsif (WE = '0' and RE = '1' and CMP_EMPTY = '1') then
            next_state <= S_EMPTY;
         end if;
      -- ------------------------------
      when S_FULL =>
         next_state <= S_FULL;
         if (RE = '1') then
            next_state <= S_RELAY;
         end if;
      -- ------------------------------
      when others =>
         next_state <= S_EMPTY;
      -- ------------------------------
      end case;
   end process;

   -- -------------------------------------------------------------------------
   output_logic: process(present_state, WE, RE, CMP_EMPTY)
   begin
      FULL           <= '0';
      EMPTY          <= '1';
      CNT_ADDR_CE    <= '0';
      CNT_ADDR_DIR   <= not RE; -- down ('0') for reading or relaying
      SHREG_CE       <= '0';

      case (present_state) is
      -- ------------------------------
      when S_EMPTY =>
         FULL           <= '0';
         EMPTY          <= '1';
         CNT_ADDR_CE    <= '0';
         SHREG_CE       <= WE;
      -- ------------------------------
      when S_RELAY =>
         FULL           <= '0';
         EMPTY          <= '0';
         CNT_ADDR_CE    <= WE xor RE;
         SHREG_CE       <= WE;

         if (WE = '0' and RE = '1' and CMP_EMPTY = '1') then
            CNT_ADDR_CE <= '0';
         end if;
      -- ------------------------------
      when S_FULL =>
         FULL           <= '1';
         EMPTY          <= '0';
         CNT_ADDR_CE    <= RE;
         SHREG_CE       <= '0';
      -- ------------------------------
      when others =>
         null;
      -- ------------------------------
      end case;
   end process;

end architecture behavioral;
