-- buf_fsm.vhd: FSM of buf part of XGMII OBUF
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
use work.math_pack.all;
use work.fifo_pkg.all;
use work.lb_pkg.all;


-- -----------------------------------------------------------------------------
--                             Entity
-- -----------------------------------------------------------------------------
entity obuf_xgmii_buf_fsm is

   port(
      -- Clock signal
      CLK               : in std_logic;
      -- Synchronous reset
      RESET             : in std_logic;

      -- Input interface
      REG_OBUF_EN       : in std_logic;
      EOP               : in std_logic;
      FRAME_RDY         : in std_logic;

      -- Output interface
      DFIFO_RD          : out std_logic

   );

end entity obuf_xgmii_buf_fsm;


architecture obuf_xgmii_buf_fsm_arch of obuf_xgmii_buf_fsm is

   -- Type definition
   type fsm_states is (st_idle, st_ready, st_packet);

   -- Signals declaration
   signal curr_state, next_state : fsm_states;

begin

   -- --------------------------------------------------------------------------
   fsmp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            curr_state <= st_idle;
         else
            curr_state <= next_state;
         end if;
      end if;
   end process;


   -- --------------------------------------------------------------------------
   next_state_logic: process(curr_state, FRAME_RDY, EOP, REG_OBUF_EN)
   begin
      case (curr_state) is

         -- st_idle
         when st_idle =>
            if (REG_OBUF_EN = '1') then
               next_state <= st_ready;
            else
               next_state <= st_idle;
            end if;

         -- st_ready
         when st_ready =>
            if (REG_OBUF_EN = '0') then
               next_state <= st_idle;
            elsif (FRAME_RDY = '1') then
               next_state <= st_packet;
            else
               next_state <= st_ready;
            end if;

         -- st_packet
         when st_packet =>
            if (EOP = '1') then
               if (REG_OBUF_EN = '1' and FRAME_RDY = '1') then
                  next_state <= st_packet;
               else
                  next_state <= st_ready;
               end if;
            else
               next_state <= st_packet;
            end if;

      end case;
   end process next_state_logic;

   -- --------------------------------------------------------------------------
   output_logic: process(curr_state, REG_OBUF_EN, FRAME_RDY)
   begin

      case (curr_state) is

         -- st_idle
         when st_idle =>
            DFIFO_RD <= '0';

         -- st_ready
         when st_ready =>
            if (FRAME_RDY = '1' and REG_OBUF_EN = '0') then
               DFIFO_RD <= '1';
            else
               DFIFO_RD <= '0';
            end if;

         -- st_packet
         when st_packet =>
            DFIFO_RD <= '1';

      end case;

   end process output_logic;

end architecture obuf_xgmii_buf_fsm_arch;
