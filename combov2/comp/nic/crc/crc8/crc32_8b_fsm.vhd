
--
-- FSM_CRC32.vhd: Finite State Controller for CRC32_8bit
-- Copyright (C) 2004 CESNET
-- Author(s): Bidlo Michal <bidlom@fit.vutbr.cz>
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
--
library IEEE;
use IEEE.std_logic_1164.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity crc32_8b_fsm is
   port(
      CLK: in std_logic;
      RESET: in std_logic;
      DI_DV: in std_logic;
      EOP: in std_logic;

      DI_CTL: out std_logic;
      TVAL_CTL: out std_logic;
      DO_DV: out std_logic;
      DV_CTL: out std_logic;
      FSM_DV: out std_logic
   );
end entity crc32_8b_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FSM_CRC32_arch of crc32_8b_fsm is
   type fsm_states is (SL, L2, L3, L4, A1, A2, A3, B1, B2, C1,
      SC, ID, F1, F2, F3, F4, SF);
   signal curr_state, next_state : fsm_states;

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if RESET = '1' then
      curr_state <= SL;
   elsif CLK'event AND CLK = '1' then
      curr_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(curr_state, DI_DV, EOP)
begin
   case (curr_state) is
      when SL =>
         if EOP = '0' AND DI_DV = '1' then
            next_state <= L2;
         elsif EOP = '1' AND DI_DV = '1' then
            next_state <= A1;
         else
            next_state <= SL;
         end if;
      when L2 =>
         if EOP = '0' AND DI_DV = '1' then
            next_state <= L3;
         elsif EOP = '1' AND DI_DV = '1' then
            next_state <= B1;
         else
            next_state <= L2;
         end if;
      when L3 =>
         if EOP = '0' AND DI_DV = '1' then
            next_state <= L4;
         elsif EOP = '1' AND DI_DV = '1' then
            next_state <= C1;
         else
            next_state <= L3;
         end if;
      when L4 =>
         if EOP = '0' AND DI_DV = '1' then
            next_state <= SC;
         elsif EOP = '1' AND DI_DV = '1' then
            next_state <= F1;
         else
            next_state <= L4;
         end if;
      when A1 => next_state <= A2;
      when A2 => next_state <= A3;
      when A3 => next_state <= F4;
      when B1 => next_state <= B2;
      when B2 => next_state <= F3;
      when C1 => next_state <= F2;
      when SC =>
         if EOP = '0' AND DI_DV = '1' then
            next_state <= SC;
         elsif EOP = '1' AND DI_DV = '1' then
            next_state <= F1;
         else
            next_state <= SC;
         end if;
      when ID =>
         if DI_DV = '1' then
            next_state <= SC;
         else
            next_state <= ID;
         end if;
      when F1 => next_state <= F2;
      when F2 => next_state <= F3;
      when F3 => next_state <= F4;
      when F4 => next_state <= SF;
      when SF => next_state <= SL;
      when others => next_state <= SL;
   end case;
end process next_state_logic;

-- -------------------------------------------------------
output_logic : process(curr_state, DI_DV)
begin
   case (curr_state) is
      when SL | L2 | L3 | L4 =>
         DI_CTL <= '0';
         TVAL_CTL <= '1';
         DO_DV <= '0';
		 FSM_DV <= '0';
      when A1 | A2 | A3 | B1 | B2 | C1 =>
         DI_CTL <= '1';
         TVAL_CTL <= '1';
         DO_DV <= '0';
		 FSM_DV <= '1';
      when SC | ID =>
         DI_CTL <= '0';
         TVAL_CTL <= '0';
         DO_DV <= '0';
	     FSM_DV <= '0';
      when F1 | F2 | F3 | F4 =>
         DI_CTL <= '1';
         TVAL_CTL <= '0';
         DO_DV <= '0';
		 FSM_DV <= '1';
      when SF =>
         DI_CTL <= '1';
         TVAL_CTL <= '1';
         DO_DV <= '1';
		 FSM_DV <= '0';
      when others =>
         DI_CTL <= '1';
         TVAL_CTL <= '1';
         DO_DV <= '0';
		 FSM_DV <= '0';
   end case;
end process output_logic;

DV_CTL <= DI_DV;

end architecture FSM_CRC32_arch;

