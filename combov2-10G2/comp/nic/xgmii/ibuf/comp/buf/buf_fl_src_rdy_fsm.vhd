-- buf_fl_src_rdy_fsm: FSM to generate FL SRC RDY signals properly
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity BUF_FL_SRC_RDY_FSM is

   port (

      -- Common signals
      CLK               : in std_logic;
      RESET             : in std_logic;
      
      -- Input SOP signal, active in '0'
      RX_SOP_N          : in std_logic;
      -- Input EOP signal, active in '0'
      RX_EOP_N          : in std_logic;
      -- Input destination ready signal, active in '0'.
      TX_DST_RDY_N      : in std_logic;

      -- Output source ready signal, active in '0'
      TX_SRC_RDY_N      : out std_logic;
      -- Frame was discarded due to buffer overflow, active in '1'
      FRAME_DISCARDED   : out std_logic;
      -- Buffer overflow occured during transmission, active in '1'
      BUFFER_OVERFLOW   : out std_logic

   );

end entity BUF_FL_SRC_RDY_FSM;



-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture BUF_FL_SRC_RDY_FSM_ARCH of BUF_FL_SRC_RDY_FSM is

   -- Type definition
   type fsm_states is (st_reset, st_wait, st_frame, st_discard);
   attribute SAFE_FSM : boolean;
   attribute SAFE_FSM of fsm_states : type is true;

   -- Signal declaration
   signal curr_state, next_state: fsm_states;

begin

   -- ------------------------------------------------------------
   fsmp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         curr_state <= st_reset;
      elsif (CLK'event AND CLK = '1') then
         curr_state <= next_state;
      end if;
   end process;

   -- ------------------------------------------------------------
   next_state_logic: process(curr_state, RX_SOP_N, RX_EOP_N, TX_DST_RDY_N)
   begin

      case (curr_state) is

         -- st_reset
         when st_reset =>
            next_state <= st_wait;

         -- st_wait
         when st_wait =>
            if (RX_SOP_N = '0' AND TX_DST_RDY_N = '0') then
               if (RX_EOP_N = '0') then
                  next_state <= st_wait;
               else
                  next_state <= st_frame;
               end if;
            elsif (RX_SOP_N = '0' AND TX_DST_RDY_N = '1') then
               next_state <= st_discard;
            else
               next_state <= st_wait;
            end if;

         -- st_frame
         when st_frame =>
            if (RX_EOP_N = '0') then
               next_state <= st_wait;
            else
               next_state <= st_frame;
            end if;

         -- st_discard
         when st_discard =>
            if (RX_EOP_N = '0') then
               next_state <= st_wait;
            else
               next_state <= st_discard;
            end if;

         when others =>
            next_state <= st_wait;

      end case;

   end process next_state_logic;

   -- ------------------------------------------------------------
   output_logic: process(curr_state, RX_SOP_N, TX_DST_RDY_N)
   begin

      case (curr_state) is

         -- st_reset
         when st_reset =>
            TX_SRC_RDY_N <= '1';
            FRAME_DISCARDED <= '0';
            BUFFER_OVERFLOW <= '0';

         -- st_wait
         when st_wait =>
            TX_SRC_RDY_N <= RX_SOP_N;
            FRAME_DISCARDED <= '0';
            BUFFER_OVERFLOW <= '0';

         -- st_frame
         when st_frame =>
            TX_SRC_RDY_N <= '0';
            FRAME_DISCARDED <= '0';
            BUFFER_OVERFLOW <= TX_DST_RDY_N;

         -- st_discard
         when st_discard =>
            TX_SRC_RDY_N <= '1';
            FRAME_DISCARDED <= '1';
            BUFFER_OVERFLOW <= '0';

      end case;

   end process output_logic;
            

end architecture BUF_FL_SRC_RDY_FSM_ARCH;




