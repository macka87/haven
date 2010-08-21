-- output_fsm.vhd: Performs discard of packets (replacing by gaps).
-- Copyright (C) 2010 CESNET
-- Author(s):  Jan Viktorin <xvikto03@liberouter.org>
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

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;

use work.math_pack.ALL;

entity discard_output_fsm is
port (
   CLK   : in std_logic;
   RESET : in std_logic;

   --+ SOP/EOP coming from fifo
   FIFO_SOP_OUT         : in std_logic;
   FIFO_EOP_OUT         : in std_logic;
   --+ discard flag coming from fifo
   FIFO_DISCARD_OUT     : in std_logic;
   --+ test for discard fifo
   FIFO_DISCARD_EMPTY   : in std_logic;
   --+ test for data fifo
   FIFO_DATA_EMPTY      : in std_logic;

   --+ read request to packet fifo
   FIFO_RD           : out std_logic;
   --+ read request to discard fifo
   FIFO_DISCARD_RD   : out std_logic;
   --+ MUX selector to make the discard
   SEL_DISCARD       : out std_logic
);
end entity;

architecture arch of discard_output_fsm is
   
   type fsm_t is (st_idle, st_pass_or_discard, st_pass, st_discard);

   signal state     : fsm_t;
   signal next_state    : fsm_t;

begin

   fsm_state : process(CLK, RESET, next_state)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            state <= st_idle;
         else
            state <= next_state;
         end if;
      end if;
   end process;

   fsm_next : process(CLK, state, FIFO_DISCARD_EMPTY,
                        FIFO_DISCARD_OUT, FIFO_EOP_OUT)
   begin
      next_state  <= state;

      case state is
         when st_idle   =>
            if FIFO_DISCARD_EMPTY = '0' then
               next_state <= st_pass_or_discard;
            end if;

         when st_pass_or_discard =>
            if FIFO_EOP_OUT = '1' then
               if FIFO_DISCARD_EMPTY = '1' then
                  next_state <= st_idle;
               end if;

            elsif FIFO_DISCARD_OUT = '1' then
               next_state <= st_discard;

            else
               next_state <= st_pass;

            end if;

         when st_pass | st_discard =>
            if FIFO_EOP_OUT = '1' then
               if FIFO_DISCARD_EMPTY = '1' then
                  next_state <= st_idle;

               else
                  next_state <= st_pass_or_discard;

               end if;
            end if;

      end case;
   end process;

   fsm_output : process(CLK, state, FIFO_DISCARD_EMPTY, FIFO_DISCARD_OUT, 
                           FIFO_DATA_EMPTY, FIFO_SOP_OUT, FIFO_EOP_OUT)
   begin
      FIFO_RD           <= '0'; -- don't read from fifo at first
      FIFO_DISCARD_RD   <= '0';
      SEL_DISCARD       <= '1'; -- do not pass anything at first

      case state is
         when st_idle   => null;

         when st_pass_or_discard =>
            FIFO_RD  <= not FIFO_DATA_EMPTY;
            FIFO_DISCARD_RD   <= not FIFO_DISCARD_EMPTY;
            SEL_DISCARD <= FIFO_DISCARD_OUT;

         when st_discard =>
            FIFO_RD     <= not FIFO_DATA_EMPTY;
            SEL_DISCARD <= '1';

         when st_pass =>
            FIFO_RD     <= not FIFO_DATA_EMPTY;
            SEL_DISCARD <= '0';

      end case;
   end process;
end architecture;
