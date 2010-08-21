-- fsm_transmit.vhd: FrameLink cutter: FSM Transmit
-- (extract and optionally remove data on defined offset in defined frame part)
-- Copyright (C) 2008 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fsm_transmit is

   -- ============================== TYPES =====================================

   type t_fsm_transmit is (st_idle, st_transmit, st_pause, st_end);


   -- ============================== SIGNALS ===================================
   
   signal transmit_c_state : t_fsm_transmit;
   signal transmit_n_state : t_fsm_transmit;
   
   
begin

   -- current state register
   Transmit_fsm_current_state: process(CLK, RESET)
   begin
      if (RESET = '1') then
         transmit_c_state <= st_idle;
      elsif (CLK'event and CLK ='1') then
         transmit_c_state <= transmit_n_state;
      end if;
   end process;


   -- next state logic
   Transmit_fsm_next_state:
   process(transmit_c_state, SOF, SRC_RDY, DST_RDY, EOF)
   begin
      transmit_n_state <= st_idle;

      case transmit_c_state is

         -- idle
         when st_idle =>
            if (SOF = '1' and SRC_RDY = '1' and DST_RDY = '1') then
               transmit_n_state <= st_transmit;
            else
               transmit_n_state <= st_idle;
            end if;

         -- transmit
         when st_transmit =>
            if (SRC_RDY = '0' or DST_RDY = '0') then
               transmit_n_state <= st_pause;
            elsif (EOF = '1') then
               transmit_n_state <= st_end;
            else
               transmit_n_state <= st_transmit;
            end if;

         -- pause
         when st_pause =>
            if (EOF = '1' and SRC_RDY = '1' and DST_RDY = '1') then
               transmit_n_state <= st_end;
            elsif (SRC_RDY = '1' and DST_RDY = '1') then
               transmit_n_state <= st_transmit;
            else
               transmit_n_state <= st_pause;
            end if;

         -- end
         when st_end =>
            if (SOF = '1' and SRC_RDY = '1' and DST_RDY = '1') then
               transmit_n_state <= st_transmit;
            else
               transmit_n_state <= st_idle;
            end if;

         -- undefined
         when others =>

      end case;
   end process;


   -- output logic
   Transmit_fsm_output: process(transmit_c_state)
   begin
      TRANSMIT_PROGRESS  <= '0';
      TRANSMIT_PAUSE <= '0';

      case transmit_c_state is

         -- idle
         when st_idle =>
            TRANSMIT_PROGRESS  <= '0';

         -- transmit
         when st_transmit =>
            TRANSMIT_PROGRESS  <= '1';

         -- pause
         when st_pause =>
            TRANSMIT_PROGRESS  <= '0';
            TRANSMIT_PAUSE <= '1';

         -- end
         when st_end =>
            TRANSMIT_PROGRESS  <= '1';

         -- undefined
         when others =>

      end case;
   end process;

end architecture full;
