--
-- ib_switch_out_fsm.vhd: Switch output controler
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
--            Patrik beck <beck@liberouter.org>
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
entity CB_SWITCH_IN_FSM is
   port(
   -- Common Interface
   CLK             : in std_logic;
   RESET           : in std_logic;

   -- BUS IN Interface
   DATA_VLD        : in  std_logic;
   DST_RDY         : out std_logic;
   SOP             : in  std_logic;
   EOP             : in  std_logic;
   
   -- SH_REG_WE
   SHREG_WE        : out std_logic;

   IF_RQ           : out std_logic;
   IF_ACK          : in std_logic;

   -- Interface Status
   IF_RDY          : in  std_logic
   );
end entity CB_SWITCH_IN_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CB_SWITCH_IN_FSM_ARCH of CB_SWITCH_IN_FSM is

   -- Control FSM declaration
   type   t_states is (st_idle, st_rq, st_eop_rq, st_data);
   signal present_state, next_state : t_states;

begin

-- SWITCH INPUT FSM -----------------------------------------------------------
-- next state clk logic
clk_d: process(CLK, RESET)
  begin
    if RESET = '1' then
      present_state <= st_idle;
    elsif (CLK='1' and CLK'event) then
      present_state <= next_state;
    end if;
  end process;

-- next state logic
state_trans: process(present_state, DATA_VLD, IF_ACK, EOP)
  begin
    case present_state is

      when st_idle =>
         -- New Routable Transaction
         if (DATA_VLD = '1' and IF_ACK = '1' and EOP = '0') then  
           next_state <= st_data; -- Data
         
         elsif (DATA_VLD = '1' and IF_ACK = '0' and EOP = '0') then  
           next_state <= st_rq; -- Port Rq
         
         elsif (DATA_VLD = '1' and IF_ACK = '0' and EOP = '1') then  
           next_state <= st_eop_rq; -- Port Rq

         -- New UnRoutable Transaction  
         else
           next_state <= st_idle; -- Idle
         end if;

      -- ST_RQ
      when st_rq =>
         -- Port Ack and not EOP
         if (IF_ACK = '1' and EOP = '0') then
           next_state <= st_data;
         -- Port Ack and EOP
         elsif (IF_ACK = '1' and EOP = '1' and DATA_VLD = '1') then
           next_state <= st_idle;
         -- not Ack and EOP
         elsif (IF_ACK = '0' and EOP = '1' and DATA_VLD = '1') then
           next_state <= st_eop_rq;
         else
           next_state <= st_rq;
         end if;

      -- EOP_RQ   
      when st_eop_rq =>
         if (IF_ACK = '1') then
           next_state <= st_idle;
         else
           next_state <= st_eop_rq;
         end if;

      -- ST_DATA
      when st_data =>
         if (DATA_VLD = '1' and EOP = '1') then
            next_state <= st_idle;
         else
            next_state <= st_data;
         end if;
          
      end case;
  end process;

-- output logic
output_logic: process(present_state, DATA_VLD, SOP, IF_RDY)
  begin
   DST_RDY           <= '0';
   SHREG_WE          <= '0';
   IF_RQ             <= '0';

   case present_state is

      -- ST_IDLE
      when st_idle =>
         DST_RDY      <= '1'; -- Set DST Ready

         if (DATA_VLD = '1') then  
            SHREG_WE <= '1'; -- Enable Shift Reg
         end if;           

         IF_RQ <= DATA_VLD and SOP;
           
      -- ST_RQ
      when st_rq =>
         DST_RDY <= '0';
         SHREG_WE          <= '1'; -- Enable Shift Reg
         IF_RQ <= '1';
      
      -- EOP_RQ   
      when st_eop_rq =>
         DST_RDY <= '0';
         SHREG_WE <= '1';
         IF_RQ <= '1';
         
      -- ST_DATA
      when st_data =>
         SHREG_WE          <= '1'; -- Enable Shift Reg
         if (IF_RDY = '1') then
           DST_RDY <= '1';         -- Set DST Ready
         end if;
   
      end case;
  end process;

end architecture CB_SWITCH_IN_FSM_ARCH;

