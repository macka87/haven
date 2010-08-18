-- rxup_fsm.vhd: FSM for rx status update
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
entity RXUP_FSM is
   port(
      -- global signals 
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      ENABLE            : in std_logic; -- enable fsm
      FLAG_GET          : in std_logic; -- get synchronization flag
      LENGTH_NZ         : in std_logic; -- length is non zero
      STATUS_NZ         : in std_logic; -- status is non zero
      LENGTH_LTE_STATUS : in std_logic; -- length lower than or equal to status
      FLUSH             : in std_logic; -- force upload of statuses
      REQ_FIFO_EMPTY    : in std_logic; -- rx desc req fifo is empty
      REQ_FIFO_DV       : in std_logic; -- rx desc req fifo data valid
      TIMEOUT           : in std_logic; -- timeout has expired
      BM_ACK            : in std_logic; -- bus master acknowledgement
      SWHW_CNT_DIFF     : in std_logic; -- sw and hw cnt differ
      
      -- output signals
      NEXT_CHID      : out std_logic; -- move to next channel id
      BM_REQ         : out std_logic; -- bus master request
      LENGTH_WE      : out std_logic; -- length register write enable
      REQ_W1         : out std_logic; -- write 1st part of bm req.
      REQ_W2         : out std_logic; -- write 2nd part of bm req.
      FLAG_SET       : out std_logic; -- set synchronization flag
      REQ_FIFO_RD    : out std_logic; -- read from request fifo
      UPDATE         : out std_logic; -- update from increments
      UPDATE_WE      : out std_logic; -- update length&gaddr registers
      TINT           : out std_logic  -- timeout interrupt
   );
end entity RXUP_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of RXUP_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_INIT, S_GETREQ, S_SEL, S_REQ_W1, S_REQ_W2, S_WACK);
   -- S_INIT     -- initial state
   -- S_GETREQ   -- get length and global address
   -- S_SEL      -- select state
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
   next_state_logic : process( present_state, ENABLE, FLAG_GET, LENGTH_NZ,
    STATUS_NZ, LENGTH_LTE_STATUS, REQ_FIFO_EMPTY, REQ_FIFO_DV, TIMEOUT, BM_ACK,
    FLUSH, SWHW_CNT_DIFF)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (ENABLE = '1' and FLAG_GET = '0') then 
            -- fsm enabled and sync flag is clear
            if (LENGTH_NZ = '0') then
            -- length is zero -> get new request
               if (REQ_FIFO_EMPTY = '1') then
                  next_state <= S_INIT;
               else
                  next_state <= S_GETREQ;
               end if;
            else
            -- length is non zero
-- generaly - rx status is updated only under 3 circumstances:
--    1) timeout elapsed - all available stats are uploaded
--    2) there are enough data to upload whole block of statuses
--    3) flush is forced
               if ((TIMEOUT = '1' or LENGTH_LTE_STATUS = '1' or FLUSH = '1')
                  and (STATUS_NZ = '1')) then
               -- timeout elapsed or length <= status
                  next_state <= S_REQ_W1; -- upload status
               else
                  next_state <= S_INIT; -- do nothing
               end if;
            end if;
         else
            next_state <= S_INIT; -- do nothing
         end if;

      -- ---------------------------------------------
      when S_GETREQ =>
         if (REQ_FIFO_DV = '1') then
            next_state <= S_SEL; -- select which way to go
         else
            next_state <= S_GETREQ; -- wait for fifo dv
         end if;

      -- ---------------------------------------------
      when S_SEL =>
         if ((TIMEOUT = '1' or LENGTH_LTE_STATUS = '1' or FLUSH = '1')
            and (STATUS_NZ = '1')) then
         -- timeout elapsed or length <= status
            next_state <= S_REQ_W1; --upload status
         else
            next_state <= S_INIT; -- go to next interface
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
   output_logic: process( present_state, ENABLE, FLAG_GET, LENGTH_NZ, FLUSH,
    STATUS_NZ, LENGTH_LTE_STATUS, REQ_FIFO_EMPTY, REQ_FIFO_DV, TIMEOUT, BM_ACK,
    SWHW_CNT_DIFF)
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      -- ---------------------------------------------
      NEXT_CHID    <= '0';
      BM_REQ       <= '0';
      LENGTH_WE    <= '0';
      FLAG_SET     <= '0';
      REQ_FIFO_RD  <= '0';
      UPDATE       <= '0';
      UPDATE_WE    <= '0';
      REQ_W1       <= '0';
      REQ_W2       <= '0';
      TINT         <= '0';

      case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (ENABLE = '1') then
         -- fsm enabled
            if (FLAG_GET = '0') then
            -- sync flag is clear - we could process further
               if (LENGTH_NZ = '0') then
               -- length is zero -> get new request
                  if (REQ_FIFO_EMPTY = '1') then
                     NEXT_CHID <= '1'; -- fifo is empty -> next interface
                     if (TIMEOUT = '1' and SWHW_CNT_DIFF = '1' and STATUS_NZ = '0') then
                        TINT <= '1';
                     end if;
                  else
                     REQ_FIFO_RD <= '1';
                  end if;
               else
               -- length is non zero
                  if ((TIMEOUT = '1' or LENGTH_LTE_STATUS = '1' or FLUSH = '1')
                     and (STATUS_NZ = '1')) then
                  -- timeout elapsed or length <= status
                     LENGTH_WE <= '1';
                  else
                     NEXT_CHID <= '1';
                     if (TIMEOUT = '1' and SWHW_CNT_DIFF = '1' and STATUS_NZ = '0') then
                        TINT <= '1';
                     end if;
                  end if;
               end if;
            else
               NEXT_CHID <= '1'; -- move to next interface
            end if;
         end if;

      -- ---------------------------------------------
      when S_GETREQ =>
         if (REQ_FIFO_DV = '1') then
            UPDATE_WE <= '1';
         else
            REQ_FIFO_RD <= '1'; -- wait for fifo dv
         end if;

      -- ---------------------------------------------
      when S_SEL =>
         if ((TIMEOUT = '1' or LENGTH_LTE_STATUS = '1' or FLUSH = '1')
            and (STATUS_NZ = '1')) then
         -- timeout elapsed or length <= status
            LENGTH_WE <= '1';
         else
            NEXT_CHID <= '1'; -- go to next interface
            if (TIMEOUT = '1' and SWHW_CNT_DIFF = '1' and STATUS_NZ = '0') then
               TINT <= '1';
            end if;
         end if;

      -- ---------------------------------------------
      when S_REQ_W1   =>
         REQ_W1 <= '1';

      -- ---------------------------------------------
      when S_REQ_W2   =>
         UPDATE    <= '1'; -- update gaddr and length from increments
         UPDATE_WE <= '1';
         REQ_W2    <= '1';
         BM_REQ    <= '1';
      -- ---------------------------------------------
      when S_WACK =>
         if (BM_ACK = '1') then
            NEXT_CHID <= '1';
            FLAG_SET  <= '1';
         end if;
 
      -- ---------------------------------------------
      when others =>
         null;
      -- ---------------------------------------------  
      end case;
   end process output_logic;

end architecture full;

