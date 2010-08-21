
--
-- crc32_32b_fsm.vhd: FSm for crc32_32b module
-- Copyright (C) 2005 CESNET
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
entity crc32_32b_fsm is
   port(
      CLK: in std_logic;
      RESET: in std_logic;
      DI_DV: in std_logic;
      DI_MASK: in std_logic_vector(1 downto 0);
      EOP: in std_logic;

      DI_CTL: out std_logic;
      TVAL_CTL: out std_logic;
      MASK: out std_logic;
      DO_DV: out std_logic;
	  FSM_DV: out std_logic
   );
end entity crc32_32b_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture crc32_32b_fsm_arch of crc32_32b_fsm is

   type fsm_states is (SL, SC, F1, F2, F3, SF);
   signal curr_state, next_state : fsm_states;

begin
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      curr_state <= SL;
   elsif (CLK'event AND CLK = '1') then
      curr_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(curr_state, DI_DV, DI_MASK, EOP)
begin
   case (curr_state) is
      when SL =>
         if EOP = '0' AND DI_DV = '1' then
            next_state <= SC;
         elsif EOP = '1' AND DI_DV = '1' then
		 	next_state <= F1;
         else
            next_state <= SL;
         end if;
      when SC =>
         if EOP = '1' AND DI_DV = '1' then
		 	next_state <= F1;
         else
            next_state <= SC;
         end if;
      when F1 =>
         if DI_MASK = "00" OR DI_MASK = "01" then next_state <= SF;
         elsif DI_MASK = "10" then next_state <= F3;
         elsif DI_MASK = "11" then next_state <= F2;
         else next_state <= SL; end if;
      when F2 => next_state <= F3;
      when F3 => next_state <= SF;
      when SF => next_state <= SL;
      when others => next_state <= SL;
   end case;
end process next_state_logic;

-- -------------------------------------------------------
output_logic : process(curr_state)
begin
   case (curr_state) is
      when SL =>
         DI_CTL <= '0';
         TVAL_CTL <= '1';
         DO_DV <= '0';
         MASK <= '0';
		 FSM_DV <= '0';
      when SC =>
         DI_CTL <= '0';
         TVAL_CTL <= '0';
         DO_DV <= '0';
         MASK <= '0';
		 FSM_DV <= '0';
      when F1 =>
         DI_CTL <= '1';
         TVAL_CTL <= '0';
         DO_DV <= '0';
		 if DI_MASK = "00" then
            MASK <= '0';
		 else
		    MASK <= '1';
		 end if;
		 FSM_DV <= '1';
      when F2 | F3 =>
         DI_CTL <= '1';
         TVAL_CTL <= '0';
         DO_DV <= '0';
         MASK <= '1';
		 FSM_DV <= '1';
      when SF =>
         DI_CTL <= '1';
         TVAL_CTL <= '1';
         DO_DV <= '1';
         MASK <= '0';
		 FSM_DV <= '0';
      when others =>
         DI_CTL <= '1';
         TVAL_CTL <= '1';
         DO_DV <= '0';
         MASK <= '0';
		 FSM_DV <= '0';
   end case;
end process output_logic;

end architecture crc32_32b_fsm_arch;

