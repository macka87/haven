-- next_desc_fsm.vhd: FSM for generating DMA requests.
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
entity NEXT_DESC_FSM is
   port(
      -- global signals 
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      ENABLED        : in  std_logic;  -- flow/channel is enabled
      HEAD_TAIL_DIFF : in  std_logic;  -- head and tail differ
      FIFO_HEMPTY    : in  std_logic;  -- fifo is half empty (or half full :-)
      DMA_ACK        : in  std_logic;  -- DMA acknowledge
      DESC_FLAG      : in  std_logic;  -- semafor flag
      
      DEC_S_INIT     : out std_logic;
      DEC_S_REQ_W1   : out std_logic;
      DEC_S_REQ_W2   : out std_logic;
      DEC_S_WACK     : out std_logic;
      -- output signals
      NEXT_FLOW      : out std_logic;  -- move index cnt
      DESC_FLAG_SET  : out std_logic;  -- set semafor flag
      BM_REQ        : out std_logic;  -- dma request
      BM_REQW1       : out std_logic;  -- write first part of bm to req. memory
      BM_REQW2       : out std_logic;  -- write second part of bm to req. memory
      REGISTER_LEN   : out std_logic;  -- store head - tail into register
      LENGTH_WE      : out std_logic   -- write req length to rag_array
   );
end entity NEXT_DESC_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of NEXT_DESC_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_INIT, S_REQ_W1, S_REQ_W2, S_WACK );
      -- S_INIT - default state, cycling trough flows
      -- S_WACK - generate DMA request and wait for ack
   
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
   next_state_logic : process( present_state, ENABLED, HEAD_TAIL_DIFF,
                                 FIFO_HEMPTY, DESC_FLAG, DMA_ACK)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_INIT =>
         if (ENABLED = '1' and HEAD_TAIL_DIFF = '1' and
             FIFO_HEMPTY = '1' and DESC_FLAG = '0') then

            next_state <= S_REQ_W1;
         else
            next_state <= S_INIT;
         end if;

      -- ---------------------------------------------
      when S_REQ_W1 =>
            next_state <= S_REQ_W2;

      -- ---------------------------------------------
      when S_REQ_W2 =>
            next_state <= S_WACK;
      
      -- ---------------------------------------------
      when S_WACK =>
         next_state <= S_WACK;
         if (DMA_ACK = '1') then
            next_state <= S_INIT;
         end if;
         
      -- ---------------------------------------------
      when others =>
         next_state <= S_INIT;

      -- ---------------------------------------------
      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, ENABLED, HEAD_TAIL_DIFF,
                                 FIFO_HEMPTY, DESC_FLAG, DMA_ACK)
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      -- ---------------------------------------------
      NEXT_FLOW      <= '0';
      DESC_FLAG_SET  <= '0';
      BM_REQ         <= '0';
      BM_REQW1       <= '0';
      BM_REQW2       <= '0';
      LENGTH_WE      <= '0';
      REGISTER_LEN   <= '0';
      DEC_S_INIT     <= '0';
      DEC_S_REQ_W1   <= '0';
      DEC_S_REQ_W2   <= '0';
      DEC_S_WACK     <= '0';
 
      case (present_state) is

      when S_INIT =>
         DEC_S_INIT     <= '1';
         if (ENABLED = '0' or HEAD_TAIL_DIFF = '0' or 
             FIFO_HEMPTY = '0' or DESC_FLAG = '1') then

            NEXT_FLOW <= '1';
         else
            REGISTER_LEN <= '1';
         end if;                 

      -- ---------------------------------------------
      when S_REQ_W1 =>
         DEC_S_REQ_W1   <= '1';
         BM_REQW1 <= '1';

      -- ---------------------------------------------
      when S_REQ_W2 =>
         DEC_S_REQ_W2   <= '1';
         BM_REQW2 <= '1';
         BM_REQ <= '1';
     
      -- ---------------------------------------------
      when S_WACK =>
         DEC_S_WACK     <= '1';
         if(DMA_ACK = '1') then
            NEXT_FLOW      <= '1';
            DESC_FLAG_SET  <= '1';
            LENGTH_WE      <= '1';
         end if;
      -- ---------------------------------------------

      when others =>
         null;
      -- ---------------------------------------------  
      end case;
   end process output_logic;

end architecture full;

