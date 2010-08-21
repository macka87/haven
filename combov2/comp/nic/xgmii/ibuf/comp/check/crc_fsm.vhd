-- crc_fsm.vhd: FSM that controls CRC component inputs
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
entity CHECK_CRC_FSM is

   port(

      -- Common signals
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Start of packet, active in '1'
      SOP               : in std_logic;
      -- End of packet, active in '1'
      EOP               : in std_logic;

      -- There are valid data on CRC DI port, active in '1'
      CRC_DI_DV         : out std_logic

   );

end entity CHECK_CRC_FSM;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture CHECK_CRC_FSM_ARCH of CHECK_CRC_FSM is

   -- Type definition
   type fsm_states is (st_start, st_data);

   -- Signal declaration
   signal curr_state, next_state: fsm_states;
   attribute SAFE_FSM : boolean;
   attribute SAFE_FSM of fsm_states : type is true;

begin

   -- ------------------------------------------------------------
   fsmp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         curr_state <= st_start;
      elsif (CLK'event AND CLK = '1') then
         curr_state <= next_state;
      end if;
   end process;

   -- ------------------------------------------------------------
   next_state_logic: process(SOP, EOP, curr_state)
   begin

      case (curr_state) is

         -- st_start
         when st_start =>
            if SOP = '1' then
               next_state <= st_data;
            else
               next_state <= st_start;
            end if;

         -- st_data
         when st_data =>
            if EOP = '1' then
               next_state <= st_start;
            else
               next_state <= st_data;
            end if;

         when others =>
            next_state <= st_start;
      end case;

   end process;
  
   -- ------------------------------------------------------------
   output_logic: process(curr_state)
   begin

      case (curr_state) is

         -- st_start
         when st_start =>
            CRC_DI_DV <= '0';

         -- st_data
         when st_data =>
            CRC_DI_DV <= '1';

      end case;

   end process;

end architecture CHECK_CRC_FSM_ARCH;
