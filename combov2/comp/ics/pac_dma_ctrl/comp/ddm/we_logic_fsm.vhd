-- we_logic_fsm.vhd: Input FSM for controling write logic.
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
entity WE_LOGIC_FSM is
   port(
      -- global signals 
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      WR_REQ         : in  std_logic;  -- ib write request
      STOPPED        : in  std_logic;  -- status register contains stopped
      DESC_TYPE      : in  std_logic;  -- last bit from write data
      DESC_INIT      : in  std_logic;  -- desc. init addr. space is accessed
      LAST_ONE       : in  std_logic;  -- last descriptor in block indication
      
      WL_S1          : out std_logic;
      WL_S2          : out std_logic;
      WL_S3          : out std_logic;
      WL_S4          : out std_logic;
      WL_S5          : out std_logic;
      -- output signals
      FLAG_CLEAR     : out std_logic;   -- clear selected flag
      FIFO_WE        : out std_logic;   -- write enable to store descriptor in fifo
      BLOCK_CNT      : out std_logic;   -- block transfer size counter
      NEXTD_WE       : out std_logic;   -- write enable to store next descriptor
                                        -- (pointer) in reg_array
      NEXTD_SELECT   : out std_logic;   -- select if nextd will be updated by 
                                        -- ib.data (0) or nextd increment (1)
      CNT_CLR        : out std_logic    -- clear request to cnt_ibwords
   );
end entity WE_LOGIC_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of WE_LOGIC_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_INIT, S_D2FIFO_W1, S_D2FIFO_W2, S_NEXTD, S_DROP );
      -- S_INIT - default state
      -- S_D2FIFO - store incoming data to NFIFO 
      --          W1 = first word of desc
      --          W2 = second word of desc
      -- S_NEXTD - descriptor type 1 was spotted - update next desc
      -- S_DROP - drop everything until last one
  
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
   next_state_logic : process( present_state, WR_REQ, DESC_INIT, STOPPED,
                                              DESC_TYPE, LAST_ONE)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (WR_REQ = '1') then
            if (DESC_INIT = '1') then     -- desc. initialization 
               next_state <= S_INIT;
            elsif(DESC_TYPE = '1') then   -- type 1
               next_state <= S_NEXTD;
            else                          -- type 0
               next_state <= S_D2FIFO_W1;
            end if;
         else
            next_state <= S_INIT;
         end if;
      
      -- ---------------------------------------------
      when S_D2FIFO_W1 =>
         next_state <= S_D2FIFO_W1;
         if (WR_REQ = '1') then
            if (LAST_ONE = '1') then
               next_state <= S_INIT;
            else
               next_state <= S_D2FIFO_W2;  -- get ready for second word
            end if;
         end if;

      -- ---------------------------------------------
      when S_D2FIFO_W2 =>
         next_state <= S_D2FIFO_W2;
         if (WR_REQ = '1') then
            if(DESC_TYPE = '1') then   -- type 1
               next_state <= S_NEXTD; -- update nextd desc
            else
               next_state <= S_D2FIFO_W1; -- first word of new descriptor
            end if;
         end if;
      
      -- ---------------------------------------------
      when S_NEXTD =>
         next_state <= S_NEXTD;
         if (WR_REQ = '1') then
            if (LAST_ONE = '1') then
               next_state <= S_INIT;
            else
               next_state <= S_DROP;
            end if;
         end if;

      -- ---------------------------------------------
      when S_DROP =>
         next_state <= S_DROP;
         if (LAST_ONE = '1') then
            next_state <= S_INIT;
         end if;       

      -- ---------------------------------------------
      when others =>
         next_state <= S_INIT;

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, WR_REQ, DESC_INIT, STOPPED,
                                         DESC_TYPE, LAST_ONE )
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      -- ---------------------------------------------
      FLAG_CLEAR     <= '0';
      FIFO_WE        <= '0';
      NEXTD_WE       <= '0';
      NEXTD_SELECT   <= '0';
      BLOCK_CNT      <= '0';
      CNT_CLR        <= LAST_ONE;
      WL_S1          <= '0';
      WL_S2          <= '0';
      WL_S3          <= '0';
      WL_S4          <= '0';
      WL_S5          <= '0';

      case (present_state) is

      when S_INIT =>
         WL_S1          <= '1';
         if(WR_REQ = '1') then
            if (DESC_INIT = '1') then   -- write new pointer to ra_nextd
               NEXTD_WE       <= '1'; 
               NEXTD_SELECT   <= '0'; 
            elsif (STOPPED = '0') then
               if(DESC_TYPE = '0') then   -- type 1
                  FIFO_WE        <= '1';  -- store first word of desc to fifo
                  BLOCK_CNT      <= '1';
              end if; 
            end if;
         end if;                 

      -- ---------------------------------------------
      when S_D2FIFO_W1 =>
         WL_S2          <= '1';
         if (WR_REQ = '1' and STOPPED = '0') then
            FIFO_WE        <= '1';  -- store second word of descriptor
            NEXTD_WE       <= '1';
            NEXTD_SELECT   <= '1';  -- increment next desc pointer
         end if;
         if (LAST_ONE = '1') then
            FLAG_CLEAR <= '1'; -- if it was last desc, clear semafor
         end if;

      -- ---------------------------------------------
      when S_D2FIFO_W2 =>
         WL_S3          <= '1';
         if (WR_REQ = '1' and STOPPED = '0') then
            if(DESC_TYPE = '0') then   -- type 1
               FIFO_WE   <= '1';
               BLOCK_CNT <= '1';
            end if;
            -- for desc_type = 1 first word of desc is dropped
         end if;

      -- ---------------------------------------------
      when S_NEXTD =>
         WL_S4          <= '1';
         if (WR_REQ = '1' and STOPPED = '0') then
            NEXTD_WE       <= '1';
            NEXTD_SELECT   <= '0';  -- store new next desc pointer
            FLAG_CLEAR     <= '1';
         end if;

      -- ---------------------------------------------
      when S_DROP =>
         WL_S5          <= '1';
         null;
      -- ---------------------------------------------

      when others =>
         null;
      -- ---------------------------------------------  
      end case;
   end process output_logic;

end architecture full;

