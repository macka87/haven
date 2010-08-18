-- new_packet_fsm.vhd: FSM for packet transmission.
-- Copyright (C) 2009 CESNET
-- Author(s): Petr Kastovsky <kastovsky@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity TX_NEW_PACKET_FSM is
   port(
      -- global signals 
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      RUN            : in  std_logic; -- indicates activity
      REG_LEN_DV     : in  std_logic; -- valid length in reg_len register (!=0)
      ENOUGH_SPACE   : in  std_logic; -- enough space in tx buffer
      DESC_DV        : in  std_logic; -- descriptor fifo data valid
      DESC_EMPTY     : in  std_logic; -- descriptor fifo is empty
      FIFO_FULL      : in  std_logic; -- full signal of new->release fifo
      BM_ACK         : in  std_logic; -- bus master acknowledge
      
      -- output signals
      GET_DESC       : out std_logic; -- read from desc fifo
      NEXT_CHID      : out std_logic; -- move to next channel id
      BM_REQ         : out std_logic; -- bus master request
      BM_REQW1       : out std_logic; -- write first word of bm. request
      BM_REQW2       : out std_logic; -- write second word of bm. request
      LENGTH_WE      : out std_logic; -- write length (+ flags)
      UPDATE         : out std_logic  -- update when bm request sent
   );
end entity TX_NEW_PACKET_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of TX_NEW_PACKET_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_INIT, S_LENFLAGS, S_REQ_W1, S_REQ_W2, S_WACK);
   -- S_INIT     -- initial state
   -- S_LENFLAGS -- get first part of descriptor - length + flags
   -- S_REQ_W1   -- store first part of bm req
   -- S_REQ_W2   -- store second part of bm req
   -- S_WACK     -- wait for bm ack
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin

   -- --------------- Sync logic -------------------------------------------
   sync_logic  : process( CLK )
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            present_state <= S_INIT;
         else
            present_state <= next_state;
         end if;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process( present_state, RUN, REG_LEN_DV, ENOUGH_SPACE,
                               DESC_EMPTY, DESC_DV, FIFO_FULL, BM_ACK)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         next_state <= S_INIT;

         if (RUN = '1' and DESC_EMPTY = '0' and REG_LEN_DV = '1' and
             ENOUGH_SPACE = '1' and FIFO_FULL = '0') then
            next_state <= S_REQ_W1;
         end if;

         if (RUN = '1' and DESC_EMPTY = '0' and REG_LEN_DV = '0' and 
             FIFO_FULL = '0') then
            next_state <= S_LENFLAGS;
         end if;

      -- ---------------------------------------------
      when S_LENFLAGS =>
         if (DESC_DV = '1') then -- we have got length
            -- not enough space in tx buff or fifo to release logic full
            if (ENOUGH_SPACE = '0' or FIFO_FULL = '1') then
               next_state <= S_INIT;
            else
               next_state <= S_REQ_W1;
            end if;
         else
            next_state <= S_LENFLAGS;
         end if;  

      -- ---------------------------------------------
      when S_REQ_W1 =>
         next_state <= S_REQ_W2;

      -- ---------------------------------------------
      when S_REQ_W2 =>
         if (DESC_DV = '1') then
            next_state <= S_WACK;
         else
            next_state <= S_REQ_W2;
         end if;    

      -- ---------------------------------------------
      when S_WACK =>
         if (BM_ACK = '1') then
            next_state <= S_INIT;
         else
            next_state <= S_WACK;
         end if;
      -- ---------------------------------------------
      when others =>
         next_state <= S_INIT;
      -- ---------------------------------------------  
      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, RUN, REG_LEN_DV, ENOUGH_SPACE, 
                          DESC_EMPTY, DESC_DV, FIFO_FULL, BM_ACK)
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      -- ---------------------------------------------
      GET_DESC     <= '0';
      NEXT_CHID    <= '0';
      BM_REQ       <= '0';
      BM_REQW1     <= '0';
      BM_REQW2     <= '0';
      LENGTH_WE    <= '0';
      UPDATE       <= '0';

      case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (RUN = '0' or DESC_EMPTY = '1' or 
             ENOUGH_SPACE = '0' or FIFO_FULL = '1') then
            NEXT_CHID <= '1';
         end if;

         if (RUN = '1' and DESC_EMPTY = '0' and 
             REG_LEN_DV = '0' and FIFO_FULL = '0') then
            GET_DESC <= '1'; -- get length from desc fifo
         end if;

      -- ---------------------------------------------
      when S_LENFLAGS =>
         if (DESC_DV = '1') then -- we have got length
            LENGTH_WE <= '1'; 
            if (ENOUGH_SPACE = '0' or FIFO_FULL = '1') then -- not enough space in tx buff
               NEXT_CHID <= '1'; 
            end if;
         else
            if (DESC_EMPTY = '0') then
               GET_DESC <= '1'; -- get length from desc fifo
             end if;
         end if;  
      -- ---------------------------------------------
      when S_REQ_W1 =>
         BM_REQW1 <= '1';
         GET_DESC <= '1'; -- get length from desc fifo

      -- ---------------------------------------------
      when S_REQ_W2 =>
         if (DESC_DV = '1') then
            BM_REQW2 <= '1';
            BM_REQ   <= '1';
         else
            -- hold until we get what we want
            GET_DESC <= '1';
         end if;    

      -- ---------------------------------------------
      when S_WACK =>
         if (BM_ACK = '0') then
            -- BM_REQ <= '1';
            null;
         else
            -- ack strobe - update registers and write to fifo
            UPDATE      <= '1';
            -- move to next interface
            NEXT_CHID   <= '1';
         end if;

      -- ---------------------------------------------
      when others =>
         null;
      -- ---------------------------------------------  
      end case;
   end process output_logic;

end architecture full;

