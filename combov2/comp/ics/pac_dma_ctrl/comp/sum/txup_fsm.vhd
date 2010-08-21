-- txup_fsm.vhd: FSM for tx status update
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

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity TXUP_FSM is
   port(
      -- global signals 
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      ENABLE            : in std_logic; -- enable fsm
      FLAG_GET          : in std_logic; -- get synchronization flag
      TIMEOUT           : in std_logic; -- timeout has expired
      SYNCINT           : in std_logic; -- INTF spotted
      FLUSH             : in std_logic; -- flush has been forced
      TX_STATUS         : in std_logic; -- 0 un/, 1 changed since last upload
      BM_ACK            : in std_logic; -- bus master acknowledgement
      
      -- output signals
      NEXT_CHID      : out std_logic; -- move to next channel id
      BM_REQ         : out std_logic; -- bus master request
      REQ_W1         : out std_logic; -- write 1st part of bm req.
      REQ_W2         : out std_logic; -- write 2nd part of bm req.
      FLAG_SET       : out std_logic; -- set synchronization flag
      UPDATE         : out std_logic  -- update registers
   );
end entity TXUP_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of TXUP_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_INIT, S_GETREQ, S_REQ_W1, S_REQ_W2, S_WACK);
   -- S_INIT     -- initial state
   -- S_GETREQ   -- get length and global address
   -- S_REQ_W1   -- write first part of request to req. memory
   -- S_REQ_W2   -- write second part of request to req. memory
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
   next_state_logic : process( present_state, ENABLE, FLAG_GET, TIMEOUT, 
                              SYNCINT, TX_STATUS , BM_ACK, FLUSH)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (ENABLE = '1') then
         -- fsm enabled
            if (FLAG_GET = '0') then
            -- sync flag is clear - we could process further
               if (TIMEOUT = '1' or SYNCINT = '1' or FLUSH = '1') then
               -- timeout occured
                  if (TX_STATUS = '1') then
                  -- one or more of the counters has changed
                     next_state <= S_REQ_W1;
                  else
                     next_state <= S_INIT;
                  end if;
               else
                  next_state <= S_INIT;
               end if;
            else
               next_state <= S_INIT; -- move to next interface
            end if;
         else
            next_state <= S_INIT; -- do nothing
         end if;

      -- ---------------------------------------------
      when S_REQ_W1   =>
         next_state <= S_REQ_W2;

      -- ---------------------------------------------
      when S_REQ_W2   =>
         next_state <= S_WACK;

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
   output_logic: process( present_state, ENABLE, FLAG_GET, TIMEOUT, FLUSH,
                              SYNCINT, TX_STATUS , BM_ACK)
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      -- ---------------------------------------------
      NEXT_CHID   <= '0';
      BM_REQ      <= '0';
      FLAG_SET    <= '0';
      UPDATE      <= '0';
      REQ_W1      <= '0';
      REQ_W2      <= '0';

      case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (ENABLE = '1') then
         -- fsm enabled
            if (FLAG_GET = '0') then
            -- sync flag is clear - we could process further
               if (TIMEOUT = '1' or SYNCINT = '1' or FLUSH = '1') then
               -- timeout occured
                  if (TX_STATUS = '1') then
                  -- one or more of the counters has changed
                     null;
                  else
                  -- timeout occured but no packet sent
                     NEXT_CHID <= '1';
                  end if;
               else
                  NEXT_CHID <= '1';
               end if;
            else
               NEXT_CHID <= '1';
            end if;
         end if;

      -- ---------------------------------------------
      when S_REQ_W1   =>
         REQ_W1 <= '1';

      -- ---------------------------------------------
      when S_REQ_W2   =>
         REQ_W2 <= '1';
         BM_REQ <= '1';

      -- ---------------------------------------------
      when S_WACK =>
         if (BM_ACK = '1') then
            NEXT_CHID <= '1';
            FLAG_SET  <= '1';
            UPDATE    <= '1';
         end if;
 
      -- ---------------------------------------------
      when others =>
         null;
      -- ---------------------------------------------  
      end case;
   end process output_logic;

end architecture full;

