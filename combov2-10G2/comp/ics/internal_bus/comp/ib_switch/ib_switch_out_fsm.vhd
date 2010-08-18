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
entity IB_SWITCH_OUT_FSM is
   generic (
     PORT_NO    : integer
   );
   port(
   -- Common Interface
   CLK          : in std_logic;
   RESET        : in std_logic;

   -- Send RQ from Port 0
   PORT0_SEND_RQ   : in  std_logic;
   PORT0_SEND_ACK  : out std_logic;
   PORT0_DATA_VLD  : in  std_logic;
   PORT0_SOP       : in  std_logic;
   PORT0_EOP       : in  std_logic;
   PORT0_FSM_RDY   : out std_logic;

   -- Send RQ from Port 1
   PORT1_SEND_RQ   : in  std_logic;
   PORT1_SEND_ACK  : out std_logic;
   PORT1_DATA_VLD  : in  std_logic;
   PORT1_SOP       : in  std_logic;
   PORT1_EOP       : in  std_logic;
   PORT1_FSM_RDY   : out std_logic;
   
   -- Send RQ from Port 2
   PORT2_SEND_RQ   : in  std_logic;
   PORT2_SEND_ACK  : out std_logic;
   PORT2_DATA_VLD  : in  std_logic;
   PORT2_SOP       : in  std_logic;
   PORT2_EOP       : in  std_logic;
   PORT2_FSM_RDY   : out std_logic;

   -- Output control Interface
   MUX_SEL         : out std_logic_vector(1 downto 0);
   DST_RDY         : in  std_logic;
   SRC_RDY         : out std_logic;
   SOP             : out std_logic;
   EOP             : out std_logic

   
   );
end entity IB_SWITCH_OUT_FSM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SWITCH_OUT_FSM_ARCH of IB_SWITCH_OUT_FSM is

   signal priority_dec_en : std_logic;
   signal transaction_ack : std_logic;
   signal port0_ack       : std_logic;
   signal port1_ack       : std_logic;
   signal port2_ack       : std_logic;
   signal mux_sel_reg     : std_logic_vector(2 downto 0);
   signal data_vld_mux    : std_logic; 
   signal eop_mux         : std_logic;
   signal sop_mux         : std_logic;
   signal src_rdy_out     : std_logic;

   -- Control FSM declaration
   type t_states is (st_arbiter, st_sop, st_data);
   signal present_state, next_state: t_states;
   
   

begin


-- SOP and EOP out
SOP             <= sop_mux and data_vld_mux and src_rdy_out;
EOP             <= eop_mux and data_vld_mux and src_rdy_out;
SRC_RDY         <= src_rdy_out;
-- Ack to Input Interfaces
PORT0_SEND_ACK  <= port0_ack;
PORT1_SEND_ACK  <= port1_ack;
PORT2_SEND_ACK  <= port2_ack;

GEN_TRANS_ACK0: if (PORT_NO = 0) generate
  -- Ack from Round Robin Priority decoder
  transaction_ack <= port1_ack or port2_ack;
end generate;
GEN_TRANS_ACK1: if (PORT_NO = 1) generate
  -- Ack from Round Robin Priority decoder
  transaction_ack <= port0_ack or port2_ack;
end generate;
GEN_TRANS_ACK2: if (PORT_NO = 2) generate
  -- Ack from Round Robin Priority decoder
  transaction_ack <= port0_ack or port1_ack;
end generate;


-- Round Robin Priority Decoder -----------------------------------------------
IB_PRIORITY_DEC_U : entity work.IB_PRIORITY_DEC
   generic map (
     PORT_NO    => PORT_NO
   )
   port map (
      -- FPGA control
      CLK       => CLK,
      RESET     => RESET,
      ENABLE    => priority_dec_en,
      -- Input Interface
      PORT0_RQ  => PORT0_SEND_RQ,
      PORT1_RQ  => PORT1_SEND_RQ,
      PORT2_RQ  => PORT2_SEND_RQ,
      -- Output Interface
      PORT0_ACK => port0_ack,
      PORT1_ACK => port1_ack,
      PORT2_ACK => port2_ack
      );

GEN_DEC_MUX0: if (PORT_NO=0) generate
-- decoder dec_mux ------------------------------------------------------------
-- Select Signal for Data Multiplexor
dec_muxp: process(mux_sel_reg)
begin
   case mux_sel_reg is
      when "010"  => MUX_SEL <= "01";
      when "100"  => MUX_SEL <= "10";
      when others => MUX_SEL <= (others => 'X');
   end case;
end process;
end generate;

GEN_DEC_MUX1: if (PORT_NO=1) generate
-- decoder dec_mux ------------------------------------------------------------
-- Select Signal for Data Multiplexor
dec_muxp: process(mux_sel_reg)
begin
   case mux_sel_reg is
      when "001"  => MUX_SEL <= "00";
      when "100"  => MUX_SEL <= "10";
      when others => MUX_SEL <= (others => 'X');
   end case;
end process;
end generate;

GEN_DEC_MUX2: if (PORT_NO=2) generate
-- decoder dec_mux ------------------------------------------------------------
-- Select Signal for Data Multiplexor
dec_muxp: process(mux_sel_reg)
begin
   case mux_sel_reg is
      when "001"  => MUX_SEL <= "00";
      when "010"  => MUX_SEL <= "01";
      when others => MUX_SEL <= (others => 'X');
   end case;
end process;
end generate;

-- register mux_sel_reg --------------------------------------------------------
-- Interface Select Register
mux_sel_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      mux_sel_reg <= (others => '0');
   else 
      if (CLK'event AND CLK = '1') then
         if (transaction_ack = '1') then
            mux_sel_reg <= port2_ack & port1_ack & port0_ack;
         end if;
      end if;
   end if;
end process;

GEN_VLD_MUX0: if (PORT_NO=0) generate
-- multiplexor data_vld_mux ----------------------------------------------------
data_vld_muxp: process(mux_sel_reg, PORT1_DATA_VLD, PORT2_DATA_VLD)
begin
   case mux_sel_reg is
      when "010" => data_vld_mux <= PORT1_DATA_VLD;
      when "100" => data_vld_mux <= PORT2_DATA_VLD;
      when others => data_vld_mux <= '0';
   end case;
end process;
end generate;
GEN_VLD_MUX1: if (PORT_NO=1) generate
-- multiplexor data_vld_mux ----------------------------------------------------
data_vld_muxp: process(mux_sel_reg, PORT0_DATA_VLD, PORT2_DATA_VLD)
begin
   case mux_sel_reg is
      when "001" => data_vld_mux <= PORT0_DATA_VLD;
      when "100" => data_vld_mux <= PORT2_DATA_VLD;
      when others => data_vld_mux <= '0';
   end case;
end process;
end generate;
GEN_VLD_MUX2: if (PORT_NO=2) generate
-- multiplexor data_vld_mux ----------------------------------------------------
data_vld_muxp: process(mux_sel_reg, PORT0_DATA_VLD, PORT1_DATA_VLD)
begin
   case mux_sel_reg is
      when "001" => data_vld_mux <= PORT0_DATA_VLD;
      when "010" => data_vld_mux <= PORT1_DATA_VLD;
      when others => data_vld_mux <= '0';
   end case;
end process;
end generate;

GEN_SOP_MUX0: if (PORT_NO=0) generate
-- multiplexor sop_mux --------------------------------------------------------
sop_muxp: process(mux_sel_reg, PORT1_SOP, PORT2_SOP)
begin
   case mux_sel_reg is
      when "010" => sop_mux <= PORT1_SOP;
      when "100" => sop_mux <= PORT2_SOP;
      when others => sop_mux <= '0';
   end case;
end process;
end generate;
GEN_SOP_MUX1: if (PORT_NO=1) generate
-- multiplexor sop_mux --------------------------------------------------------
sop_muxp: process(mux_sel_reg, PORT0_SOP, PORT2_SOP)
begin
   case mux_sel_reg is
      when "001" => sop_mux <= PORT0_SOP;
      when "100" => sop_mux <= PORT2_SOP;
      when others => sop_mux <= '0';
   end case;
end process;
end generate;
GEN_SOP_MUX2: if (PORT_NO=2) generate
-- multiplexor sop_mux --------------------------------------------------------
sop_muxp: process(mux_sel_reg, PORT0_SOP, PORT1_SOP)
begin
   case mux_sel_reg is
      when "001" => sop_mux <= PORT0_SOP;
      when "010" => sop_mux <= PORT1_SOP;
      when others => sop_mux <= '0';
   end case;
end process;
end generate;

GEN_EOP_MUX0: if (PORT_NO=0) generate
-- multiplexor eop_mux --------------------------------------------------------
eop_muxp: process(mux_sel_reg, PORT1_EOP, PORT2_EOP)
begin
   case mux_sel_reg is
      when "010" => eop_mux <= PORT1_EOP;
      when "100" => eop_mux <= PORT2_EOP;
      when others => eop_mux <= '0';
   end case;
end process;
end generate;
GEN_EOP_MUX1: if (PORT_NO=1) generate
-- multiplexor eop_mux --------------------------------------------------------
eop_muxp: process(mux_sel_reg, PORT0_EOP, PORT2_EOP)
begin
   case mux_sel_reg is
      when "001" => eop_mux <= PORT0_EOP;
      when "100" => eop_mux <= PORT2_EOP;
      when others => eop_mux <= '0';
   end case;
end process;
end generate;
GEN_EOP_MUX2: if (PORT_NO=2) generate
-- multiplexor eop_mux --------------------------------------------------------
eop_muxp: process(mux_sel_reg, PORT0_EOP, PORT1_EOP)
begin
   case mux_sel_reg is
      when "001" => eop_mux <= PORT0_EOP;
      when "010" => eop_mux <= PORT1_EOP;
      when others => eop_mux <= '0';
   end case;
end process;
end generate;


-- SWITCH OUTPUT FSM ----------------------------------------------------------
-- next state clk logic
clk_d: process(clk, reset )
  begin
    if (RESET = '1') then
      present_state <= st_arbiter;
    elsif (CLK='1' and CLK'event) then
      present_state <= next_state;
    end if;
  end process;


-- next state logic
state_trans: process(present_state, data_vld_mux, sop_mux, eop_mux, DST_RDY, transaction_ack)
begin
    case present_state is

      -- ST_ARBITER
      when st_arbiter =>
         if (transaction_ack = '1') then
           next_state <= st_sop;
         else
           next_state <= st_arbiter;
         end if;

      -- ST_SOP
      when st_sop =>
         if (data_vld_mux = '1' and sop_mux = '1' and DST_RDY = '1') then
            next_state <= st_data;
         else
            next_state <= st_sop;
         end if;

      -- ST_DATA
      when st_data =>
--       if (data_vld_mux = '1' and eop_mux = '1' and DST_RDY = '1') then
         if (data_vld_mux = '1' and eop_mux = '1' and DST_RDY = '1' and transaction_ack = '0') then
           next_state <= st_arbiter;
         elsif (data_vld_mux = '1' and eop_mux = '1' and DST_RDY = '1' and transaction_ack = '1') then
           next_state <= st_sop;
         else
           next_state <= st_data;
         end if;

      end case;
end process;

-- output logic
output_logic: process(present_state, data_vld_mux, DST_RDY, sop_mux, eop_mux, mux_sel_reg)
  begin

    -- Default values
    priority_dec_en <= '0';
    src_rdy_out     <= '0';
    PORT0_FSM_RDY   <= '0';
    PORT1_FSM_RDY   <= '0';
    PORT2_FSM_RDY   <= '0';

   case present_state is
    
      -- ST_ARBITER
      when st_arbiter =>
         priority_dec_en <= '1';
    
      -- ST_SOP
      when st_sop =>
         if (data_vld_mux = '1' and sop_mux = '1') then
            src_rdy_out        <= '1';
            -- RDY must be set when SOP vld
            
            if not (PORT_NO = 0) then
               PORT0_FSM_RDY   <= DST_RDY and mux_sel_reg(0);
            else
               PORT0_FSM_RDY   <= '0';
            end if;
            if not (PORT_NO = 1) then
               PORT1_FSM_RDY   <= DST_RDY and mux_sel_reg(1);
            else
               PORT1_FSM_RDY   <= '0';
            end if;
            if not (PORT_NO = 2) then
               PORT2_FSM_RDY   <= DST_RDY and mux_sel_reg(2);
            else
               PORT2_FSM_RDY   <= '0';
            end if;
            
         end if;

      -- ST_DATA
      when st_data =>
            if not (PORT_NO = 0) then
               PORT0_FSM_RDY   <= DST_RDY and mux_sel_reg(0);
            else
               PORT0_FSM_RDY   <= '0';
            end if;
            if not (PORT_NO = 1) then
               PORT1_FSM_RDY   <= DST_RDY and mux_sel_reg(1);
            else
               PORT1_FSM_RDY   <= '0';
            end if;
            if not (PORT_NO = 2) then
               PORT2_FSM_RDY   <= DST_RDY and mux_sel_reg(2);
            else
               PORT2_FSM_RDY   <= '0';
            end if;

         if (data_vld_mux = '1') then
            src_rdy_out        <= '1';
            if (eop_mux = '1' and DST_RDY = '1') then
               priority_dec_en <= '1';
            end if;
         end if;
      end case;

end process;
  
end architecture IB_SWITCH_OUT_FSM_ARCH;


