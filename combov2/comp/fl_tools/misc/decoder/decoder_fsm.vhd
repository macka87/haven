-- decoder_fsm.vhd: main FSM
-- Copyright (C) 2006 CESNET
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
entity FL_DEC_FSM is
   generic(
      HEADER      : boolean;
      FOOTER      : boolean
   );
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- input signals
      EOP         : in  std_logic;
      EOF         : in  std_logic;

      -- output signals
      PART        : out std_logic_vector(1 downto 0)
   );
end entity FL_DEC_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_DEC_FSM is

   -- ------------------ Types declaration ------------------------------------
   type t_state is ( S_HEADER, S_PAYLOAD, S_FOOTER );
   
   -- ------------------ Signals declaration ----------------------------------
   signal present_state, next_state : t_state;

begin
   
   -- --------------- Sync logic -------------------------------------------
   sync_logic  : process( RESET, CLK)
   begin
      if (RESET = '1') then
         if (HEADER) then
            present_state <= S_HEADER;
         else
            present_state <= S_PAYLOAD;
         end if;
      elsif (CLK'event AND CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;

   -- ------------------ Next state logic -------------------------------------
   next_state_logic : process(present_state, EOP, EOF)
   begin
   case (present_state) is

      -- ---------------------------------------------
      when S_HEADER =>
         if (EOP = '1') then
            next_state <= S_PAYLOAD;
         else
            next_state <= S_HEADER;
         end if;
      
      -- ---------------------------------------------
      when S_PAYLOAD =>
         if (EOF = '1') then
            if (HEADER) then
               next_state <= S_HEADER;
            else
               next_state <= S_PAYLOAD;
            end if;
         elsif (EOP = '1') then
            if (FOOTER) then
               next_state <= S_FOOTER;
            else
               next_state <= S_PAYLOAD;
            end if;
         else
            next_state <= S_PAYLOAD;
         end if;

      -- ---------------------------------------------
      when S_FOOTER =>
         if (EOP = '1') then
            if (HEADER) then
               next_state <= S_HEADER;
            else
               next_state <= S_PAYLOAD;
            end if;
         else
            next_state <= S_FOOTER;
         end if;

      end case;
   end process next_state_logic;

   -- ------------------ Output logic -----------------------------------------
   output_logic: process( present_state )
   begin
   
      -- ---------------------------------------------
      -- Initial values
      PART           <= "00";

      case (present_state) is
      
      -- ---------------------------------------------
      when S_HEADER =>
         PART        <= "00";

      -- ---------------------------------------------
      when S_PAYLOAD =>
         PART        <= "01";

      -- ---------------------------------------------
      when S_FOOTER =>
         PART        <= "10";

      end case;
   end process output_logic;

end architecture full;
