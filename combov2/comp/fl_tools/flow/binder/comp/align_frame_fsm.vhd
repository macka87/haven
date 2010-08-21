-- align_frame_fsm.vhd: FrameLink Binder Align frame FSM
-- Copyright (C) 2008 CESNET
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
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FLB_ALIGN_FRAME_FSM is
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- input signals
      DV             : in  std_logic;
      CNT_ROW_MAX    : in  std_logic;
      EOP            : in  std_logic;
      FIFO_FULL      : in  std_logic;

      -- output signals
      INSERT_IDLE    : out std_logic
   );
end entity FLB_ALIGN_FRAME_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FLB_ALIGN_FRAME_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( BUSY, ALIGN_EOP );
   
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin

   -- ------------------ Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= BUSY;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;
   
   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process(present_state, DV, CNT_ROW_MAX, EOP, FIFO_FULL)
   begin
   case (present_state) is
      
      -- ---------------------------------------------
      when BUSY =>
         if ( EOP = '1' and CNT_ROW_MAX = '0' and FIFO_FULL = '0' and DV = '1') then
            next_state <= ALIGN_EOP;
         else
            next_state <= BUSY;
         end if;

      -- ---------------------------------------------
      when ALIGN_EOP =>
         if ( CNT_ROW_MAX = '1' and FIFO_FULL = '0' ) then
            next_state <= BUSY;
         else
            next_state <= ALIGN_EOP;
         end if;

   end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state, DV, FIFO_FULL, EOP )
   begin
   
      -- ---------------------------------------------
      -- Initial values
      INSERT_IDLE       <= '0';
      
      case (present_state) is

      -- ---------------------------------------------
      when BUSY =>
         null;

      -- ---------------------------------------------
      when ALIGN_EOP =>
         INSERT_IDLE    <= '1';

      end case;
   end process output_logic;

end architecture full;
