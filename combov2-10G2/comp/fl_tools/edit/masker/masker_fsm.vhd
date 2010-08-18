-- masker_arch.vhd: Frame Link component to mask bits
-- Copyright (C) 2006 CESNET
-- Author(s): Radim Janalik <radim.janalik@gmail.com>
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
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

entity FL_MASKER_FSM is

   port(            
      CLK           : in  std_logic;
      RESET         : in  std_logic;

      RX_SRC_RDY_N  : in  std_logic;
      TX_DST_RDY_N  : in  std_logic;
      RX_EOF_N      : in  std_logic;
      RX_SOF_N      : in  std_logic;
      WR_REQ        : in std_logic;

      WR_ACK        : out std_logic
   );   
end entity FL_MASKER_FSM;

architecture fsm of FL_MASKER_FSM is

   type t_state is (ST_IDLE, ST_FRAME, ST_CONFIG);
   signal present_state, next_state : t_state;
 
begin

   fsm_proc : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            present_state <= ST_IDLE;
         else
            present_state <= next_state;
         end if;
      end if;
   end process;

   fsm_next_state_proc : process(present_state, RX_SOF_N, RX_EOF_N, RX_SRC_RDY_N, TX_DST_RDY_N, WR_REQ)
   begin
      next_state <= ST_IDLE;

      case present_state is
         when ST_IDLE =>
            if RX_SOF_N = '0' and RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and WR_REQ = '0' then
               next_state <= ST_FRAME;
            elsif WR_REQ = '1' then
               next_state <= ST_CONFIG;
            else
               next_state <= ST_IDLE;
            end if;
         when ST_FRAME =>
            if RX_EOF_N = '0' and RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and WR_REQ = '0' then
               next_state <= ST_IDLE;
            elsif RX_EOF_N = '0' and RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and WR_REQ = '1' then
               next_state <= ST_CONFIG;
            else
               next_state <= ST_FRAME;
            end if;
         when ST_CONFIG =>
            if WR_REQ = '0' then
               next_state <= ST_IDLE;
            else
               next_state <= ST_CONFIG;
            end if;
         when others => null;
      end case;
   end process;

   fsm_output_proc : process(present_state)
   begin
      case present_state is
         when ST_IDLE =>
            WR_ACK <= '0';
         when ST_FRAME =>
            WR_ACK <= '0';
         when ST_CONFIG =>
            WR_ACK <= '1';
      end case;
   end process;

end architecture fsm;
