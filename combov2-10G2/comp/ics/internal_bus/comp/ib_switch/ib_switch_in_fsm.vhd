--
-- ib_switch_out_fsm.vhd: Switch output controler
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
entity IB_SWITCH_IN_FSM is
   generic (
     PORT_NO       : integer
     );
   port(
   -- Common Interface
   CLK             : in std_logic;
   RESET           : in std_logic;

   -- BUS IN Interface
   DATA_VLD        : in  std_logic;
   SOP             : in  std_logic;
   EOP             : in  std_logic;
   
   -- Address Decoder
   ADDR_DEC_MATCH  : in  std_logic;
   IF_SELECT       : in  std_logic_vector(2 downto 0);

   -- Shift Register WR Enable 
   SHR_WR_EN       : out std_logic;

   -- Interface RQ
   IF_RQ           : out std_logic_vector(2 downto 0);
   IF_ACK          : in  std_logic_vector(2 downto 0)
   );
end entity IB_SWITCH_IN_FSM;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SWITCH_IN_FSM_ARCH of IB_SWITCH_IN_FSM is

   -- Control FSM declaration
   type   t_states is (st_idle, st_rq, st_eop_rq, st_drop, st_data);
   signal present_state, next_state : t_states;

   -- Aux Signals
   signal if_select_reg     : std_logic_vector(2 downto 0);
   signal if_select_reg_we  : std_logic;
   signal aux_if_ack        : std_logic;
   signal req_en            : std_logic;
   signal if_select_mux     : std_logic_vector(2 downto 0);
   signal if_select_mux_sel : std_logic;

begin

-- Interface Request
IF_RQ      <= (if_select_mux(2) and req_en) & (if_select_mux(1) and req_en) & (if_select_mux(0) and req_en);

-- Interface Request Acknowledge (You can't get ACK without rq
GEN_AUX_ACK0: if (PORT_NO=0) generate
  aux_if_ack <= IF_ACK(1) or IF_ACK(2);
end generate;
GEN_AUX_ACK1: if (PORT_NO=1) generate
  aux_if_ack <= IF_ACK(0) or IF_ACK(2);
end generate;
GEN_AUX_ACK2: if (PORT_NO=2) generate
  aux_if_ack <= IF_ACK(0) or IF_ACK(1);
end generate;




-- register port_if_select_reg ------------------------------------------------
if_select_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      if_select_reg <= (others => '0');
   else
      if (CLK'event AND CLK = '1') then
         if (if_select_reg_we = '1') then
            if_select_reg <= IF_SELECT;
         end if;
      end if;
   end if;
end process;

-- multiplexor if_select_mux --------------------------------------------------
if_select_muxp: process(if_select_mux_sel, IF_SELECT, if_select_reg)
begin
   case if_select_mux_sel is
      when '0' => if_select_mux <= IF_SELECT;
      when '1' => if_select_mux <= if_select_reg;
      when others => if_select_mux <= (others => 'X');
   end case;
end process;


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
state_trans: process(present_state, DATA_VLD, ADDR_DEC_MATCH, aux_if_ack, EOP)
  begin
    case present_state is

      when st_idle =>
         -- New Routable Transaction
         if (DATA_VLD = '1' and ADDR_DEC_MATCH = '1' and aux_if_ack = '1') then  
           next_state <= st_data; -- Data
         elsif (DATA_VLD = '1' and ADDR_DEC_MATCH = '1' and aux_if_ack = '0') then  
           next_state <= st_rq; -- Port Rq
         -- New UnRoutable Transaction  
         elsif (DATA_VLD = '1' and ADDR_DEC_MATCH = '0') then 
           next_state <= st_drop; -- Drop
         else
           next_state <= st_idle; -- Idle
         end if;

      -- ST_RQ
      when st_rq =>
         -- Port Ack and EOP
         if (aux_if_ack = '1' and EOP = '1' and DATA_VLD = '1') then
           next_state <= st_idle;
         -- Port Ack
         elsif (aux_if_ack = '1') then
           next_state <= st_data;
         -- not Ack and EOP
         elsif (EOP = '1' and DATA_VLD = '1') then
           next_state <= st_eop_rq;
         else
           next_state <= st_rq;
         end if;

      -- EOP_RQ   
      when st_eop_rq =>
         if (aux_if_ack = '1') then
           next_state <= st_idle;
         else
           next_state <= st_eop_rq;
         end if;

      -- ST_DROP
      when st_drop =>
         if (DATA_VLD = '1' and EOP = '1') then
            next_state <= st_idle;
         else
            next_state <= st_drop;
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
output_logic: process(present_state, DATA_VLD, SOP, ADDR_DEC_MATCH)
  begin
   req_en            <= '0';
   SHR_WR_EN          <= '0';
   if_select_reg_we  <= '0';
   if_select_mux_sel <= '0';
   
   case present_state is

      -- ST_IDLE
      when st_idle =>
         if (DATA_VLD = '1' and SOP = '1') then
            if_select_reg_we  <= '1'; -- Write Actual Addr Decoder Output to Register
            if_select_mux_sel <= '0'; -- Select Actual Addr Decoder Output
            req_en            <= ADDR_DEC_MATCH; -- Interface Port Request
         end if;

         if (ADDR_DEC_MATCH = '1') then  
            SHR_WR_EN <= '1'; -- Enable Shift Reg
         end if;
           
      -- ST_RQ
      when st_rq =>
         if_select_mux_sel <= '1'; -- Select Reg Addr Decoder Output
         req_en            <= '1'; -- Interface Port Request
         SHR_WR_EN          <= '1'; -- Enable Shift Reg
      
      -- EOP_RQ   
      when st_eop_rq =>
         if_select_mux_sel <= '1'; -- Select Reg Addr Decoder Output
         req_en            <= '1'; -- Interface Port Request
         
      -- ST_DROP
      when st_drop =>
         
      -- ST_DATA
      when st_data =>
         SHR_WR_EN          <= '1'; -- Enable Shift Reg
   
      end case;
  end process;

end architecture IB_SWITCH_IN_FSM_ARCH;

