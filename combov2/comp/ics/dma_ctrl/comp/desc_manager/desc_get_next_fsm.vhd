-- desc_get_next_fsm.vhd: Controls downloading depending on fifo status.
-- Copyright (C) 2008 CESNET
-- Author(s): Pavol Korcek <korcek@liberouter.org>
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
entity DESC_GET_NEXT_FSM is
   port(
      -- global signals 
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- input signals
      ENABLE      : in  std_logic;  -- enable signal (depends on channel)   
      STATUS      : in  std_logic;  -- get actual status from fifo (depends on channel)
      FLAG_GET    : in  std_logic;  -- get actual flag from flags (depends on channel)
      DMA_ACK     : in  std_logic;  -- get DMA ack

      -- output signals
      NEXT_ADDR   : out std_logic;  -- enable address counter
      DMA_REQ     : out std_logic;  -- start DMA request
      FLAG_SET    : out std_logic;  -- sets actual flag to flags (depends on channel)
      STATE_DEC   : out std_logic_vector(1 downto 0) -- Current state
   );
end entity DESC_GET_NEXT_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of DESC_GET_NEXT_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_POLL, S_GET_NEXT );
   
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin
   
   -- --------------- Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK )
   begin
      if (RESET = '1') then
         present_state <= S_POLL;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process( present_state, ENABLE, STATUS, FLAG_GET, DMA_ACK )
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_POLL =>
         -- channel enabled and half of fifo free and not actually working
         if (ENABLE = '1' and STATUS = '0' and FLAG_GET = '0') then      
            next_state <= S_GET_NEXT;
         else                                      -- otherwise polling
            next_state <= S_POLL;
         end if;
      -- ---------------------------------------------
      when S_GET_NEXT =>
         if(DMA_ACK = '1') then        -- if DMA ack comes, next polling
            next_state <= S_POLL;
         else
            next_state <= S_GET_NEXT;  -- otherwise, wait here
         end if;
      -- ---------------------------------------------

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, ENABLE, STATUS, FLAG_GET, DMA_ACK )
   begin
  
      -- ---------------------------------------------
      -- Initial values
      -- no active signals
      NEXT_ADDR   <= '1'; -- always counting
      DMA_REQ     <= '0';
      FLAG_SET    <= '0';
      STATE_DEC   <= "00";
      -- ---------------------------------------------
      case (present_state) is
         when S_POLL =>
            STATE_DEC   <= "01";
            if(ENABLE = '1' and STATUS = '0' and FLAG_GET = '0') then  
               NEXT_ADDR   <= '0';  -- going to new state, stop here
               DMA_REQ     <= '1';  -- set request 
               FLAG_SET    <= '0';  
            else  
               NEXT_ADDR   <= '1';  -- in poll, check all addresses   
               DMA_REQ     <= '0';  
               FLAG_SET    <= '0';  
            end if;
      -- ---------------------------------------------
         when S_GET_NEXT =>
            STATE_DEC   <= "10";
            if(DMA_ACK = '0') then   
               NEXT_ADDR   <= '0'; -- stop counting
               DMA_REQ     <= '0';  
               FLAG_SET    <= '0'; 
            else -- ack comes
               NEXT_ADDR   <= '1'; -- going to new state, start counting 
               DMA_REQ     <= '0';
               FLAG_SET    <= '1'; -- can set flag here, done
            end if;   
      -- ---------------------------------------------
      end case;
   end process output_logic;

end architecture full;

