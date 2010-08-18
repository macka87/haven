-- first_insert_arch.vhd: Full architecture of FIRST INSERT unit.
-- Copyright (C) 2008 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
--  Architecture: FIRST_INSERT
-- ----------------------------------------------------------------------------
architecture full of FL_FIRST_INSERT is
   type tstates is (START, FIRST, READ);
   
   signal current_state  : tstates;
   signal next_state     : tstates;
begin
   -- FSM state register
   state_register: process (RESET, CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            current_state <= START;
         else
            current_state <= next_state;
         end if;
      end if;
   end process state_register;

  -- transitions in FSM
  transitions_FSM: process (current_state, RX_SRC_RDY_N, RX_EOF_N, RX_SOF_N, TX_DST_RDY_N)
  begin
     next_state <= current_state;
     case current_state is
        when START =>
           -- if packet is ready we will isert data
           if RX_SRC_RDY_N = '0' and RX_SOF_N = '0' and TX_DST_RDY_N = '0' then
              next_state <= FIRST;
           else
              next_state <= current_state;
           end if;
        when FIRST =>
           -- if packet is ready we will isert data
           if RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' then
              if RX_EOF_N = '0' then
	         next_state <= START;
              else
	         next_state <= READ;
              end if;
           else
              next_state <= current_state;
           end if;
        when READ =>
           -- packet is send wait for another
           if RX_SRC_RDY_N = '0' and RX_EOF_N = '0' and TX_DST_RDY_N = '0' then
              next_state <= START;
           else
              next_state <= current_state;
           end if;
        when others =>
     end case;
  end process transitions_FSM;

  -- outputs of FSM
  outputs_FSM: process (current_state, RX_SRC_RDY_N, TX_DST_RDY_N, RX_EOF_N,
                        RX_SOF_N, RX_EOP_N, RX_SOP_N, RX_DATA, RX_REM, DATA,
                        DREM)
  begin
     RX_DST_RDY_N <= TX_DST_RDY_N;
     TX_SRC_RDY_N <= RX_SRC_RDY_N;
     TX_SOF_N <= RX_SOF_N;
     TX_SOP_N <= RX_SOP_N;
     TX_EOF_N <= RX_EOF_N;
     TX_EOP_N <= RX_EOP_N;
     TX_DATA  <= RX_DATA;
     TX_REM   <= RX_REM;
     case current_state is
        when START =>
           -- if packet is ready we will isert data
           if RX_SRC_RDY_N = '0' and RX_SOF_N = '0' and TX_DST_RDY_N = '0' then
              RX_DST_RDY_N <= '1';
              TX_SRC_RDY_N <= '0';
              TX_DATA <= DATA;
              TX_REM  <= DREM; -- conv_std_logic_vector((DATA_WIDTH / 8) - 1, log2(DATA_WIDTH / 8));
              TX_SOF_N <= '0';
              TX_SOP_N <= '0';
	      TX_EOP_N <= '0';
	      TX_EOF_N <= '1';
           end if;
        when FIRST =>
           TX_SOF_N <= '1';
           TX_SOP_N <= '0';
        when READ =>

        when others =>
     end case;
  end process outputs_FSM;
end architecture full;
