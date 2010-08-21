-- fsm.pf: FSM for FL_COMPOSER for frames with footer and no header
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
entity FL_COMPOSER_FSM_PF is

   port(
      -- Common signals
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- Input
      -- End of payload part, active in '0'
      EOP_N          : in std_logic;
      -- End of header/footer part, active in '0'
      HEOP_N         : in std_logic;

      -- Output
      -- Selects header FIFO ('1') or data FIFO ('0')
      FIFO_SEL       : out std_logic;
      -- Enables/disables SOF_N, active in '0'
      SOF_N          : out std_logic;
      -- Enables/disables SOF_N, active in '0'
      EOF_N          : out std_logic
   );

end entity FL_COMPOSER_FSM_PF;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture FL_COMPOSER_FSM_PF_ARCH of FL_COMPOSER_FSM_PF is


   -- Type definition
   type fsm_states is (st_pld, st_ftr);

   -- Signals declaration
   signal curr_state, next_state : fsm_states;

begin

   -- -------------------------------------------------------
   fsmp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         curr_state <= st_pld;
      elsif (CLK'event AND CLK = '1') then
         curr_state <= next_state;
      end if;
   end process;

   -- -------------------------------------------------------
   next_state_logic: process(curr_state, EOP_N, HEOP_N)
   begin
      case (curr_state) is

         -- payload
         when st_pld =>
            if EOP_N = '0' then
               next_state <= st_ftr;
            else
               next_state <= st_pld;
            end if;

         -- footer
         when st_ftr =>
            if HEOP_N = '0' then
               next_state <= st_pld;
            else
               next_state <= st_ftr;
            end if;

      end case;
   end process;

   -- -------------------------------------------------------
   output_logic: process(curr_state)
   begin
      case (curr_state) is

         -- payload
         when st_pld =>
            FIFO_SEL <= '0';
            SOF_N    <= '0';
            EOF_N    <= '1';

         -- footer
         when st_ftr =>
            FIFO_SEL <= '1';
            SOF_N    <= '1';
            EOF_N    <= '0';

      end case;
   end process;

end architecture FL_COMPOSER_FSM_PF_ARCH;
