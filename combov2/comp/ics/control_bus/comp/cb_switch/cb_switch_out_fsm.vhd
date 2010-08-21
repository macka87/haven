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
use work.math_pack.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity CB_SWITCH_OUT_FSM is
   generic(
      DS_PORTS          : integer := 2

   );
   port(
   -- Common Interface
   CLK          : in std_logic;
   RESET        : in std_logic;

   -- Downstream ports
   DS_SEND_RQ        : in std_logic_vector(DS_PORTS-1 downto 0);
   DS_SEND_ACK       : out std_logic_vector(DS_PORTS-1 downto 0);
   DS_DATA_VLD       : in std_logic_vector(DS_PORTS-1 downto 0);
   DS_SOP            : in std_logic_vector(DS_PORTS-1 downto 0);
   DS_EOP            : in std_logic_vector(DS_PORTS-1 downto 0);
   DS_FSM_RDY        : out std_logic_vector(DS_PORTS-1 downto 0);

   -- Output control Interface
   MUX_SEL         : out std_logic_vector(LOG2(DS_PORTS)-1 downto 0);
   DST_RDY         : in  std_logic;
   SRC_RDY         : out std_logic;
   SOP             : out std_logic;
   EOP             : out std_logic

   
   );
end entity CB_SWITCH_OUT_FSM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture CB_SWITCH_OUT_FSM_ARCH of CB_SWITCH_OUT_FSM is

   signal priority_dec_en : std_logic;
   signal transaction_ack : std_logic;
   signal mux_sel_reg     : std_logic_vector(DS_PORTS-1 downto 0);
   signal dec_mux         : std_logic_vector(DS_PORTS-1 downto 0);
   signal data_vld_mux    : std_logic; 
   signal eop_mux         : std_logic;
   signal sop_mux         : std_logic;
   signal aux_arbiter     : std_logic;

   signal ds_ack          : std_logic_vector(DS_PORTS-1 downto 0);

   -- Control FSM declaration
   type t_states is (st_arbiter, st_data);
   signal present_state, next_state: t_states;
   
begin

-- SOP and EOP out
SOP             <= sop_mux and data_vld_mux;
EOP             <= eop_mux and data_vld_mux;

DS_SEND_ACK     <= ds_ack;

-- Ready when Destination Ready, not Arbitr and Interface selected
FSM_G: for i in 0 to DS_PORTS-1 generate
   DS_FSM_RDY(i)   <= DST_RDY and not aux_arbiter and mux_sel_reg(i);
end generate;

-- Ack from Round Robin Priority decoder
transaction_ack <= '0' when ds_ack = conv_std_logic_vector(0, DS_PORTS) else '1';

-- Round Robin Priority Decoder -----------------------------------------------
CB_PRIORITY_DEC_U : entity work.RR_ARBITER
   generic map(
      PORTS => DS_PORTS
   )
   port map (
      -- FPGA control
      CLK       => CLK,
      RESET     => RESET,
      ENABLE    => priority_dec_en,
      
      -- Input Interface
      RQ  => DS_SEND_RQ,
      
      -- Output Interface
      ACK => ds_ack
      );

-- decoder dec_mux ------------------------------------------------------------
-- Select Signal for Data Multiplexor


dec_muxp: process(mux_sel_reg)
begin
   MUX_SEL <= (others => 'X');
   for i in 0 to DS_PORTS-1 loop
      if(mux_sel_reg(i) = '1') then
         MUX_SEL <= conv_std_logic_vector(i, LOG2(DS_PORTS));     
      end if;
--       case mux_sel_reg is
--          when "01"  => MUX_SEL <= "0";
--          when "10"  => MUX_SEL <= "1";
--          when others => MUX_SEL <= "X";
--       end case;
   end loop;
end process;

-- register mux_sel_reg --------------------------------------------------------
-- Interface Select Register
mux_sel_regp: process(RESET, CLK)
begin
   if (RESET = '1') then
      mux_sel_reg <= (others => '0');
   elsif (CLK'event AND CLK = '1') then
      if (transaction_ack = '1') then
         mux_sel_reg <= ds_ack;
      end if;
   end if;
end process;

-- multiplexor data_vld_mux ----------------------------------------------------
data_vld_muxp: process(mux_sel_reg, DS_DATA_VLD, DS_SOP, DS_EOP)
begin
   data_vld_mux <= '0';
   sop_mux <= '0';
   eop_mux <= '0';

   for i in 0 to DS_PORTS-1 loop
      if mux_sel_reg(i) = '1' then
         data_vld_mux <= DS_DATA_VLD(i);
         sop_mux <= DS_SOP(i);
         eop_mux <= DS_EOP(i);
      end if;
   end loop;

--    case mux_sel_reg is
--       when "01" => data_vld_mux <= DS_DATA_VLD(0);
--       when "10" => data_vld_mux <= DS_DATA_VLD(1);
--       when others => data_vld_mux <= '0';
--    end case;
end process;


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
state_trans: process(present_state, data_vld_mux, eop_mux, DST_RDY, transaction_ack)
begin
    case present_state is

      -- ST_ARBITER
      when st_arbiter =>
         if (transaction_ack = '1') then
           next_state <= st_data;
         else
           next_state <= st_arbiter;
         end if;
         
      -- ST_DATA
      when st_data =>
         if (data_vld_mux = '1' and eop_mux = '1' and DST_RDY = '1' and transaction_ack = '0') then
           next_state <= st_arbiter;
         else
           next_state <= st_data;
         end if;

      end case;
end process;

-- output logic
output_logic: process(present_state, data_vld_mux, DST_RDY, eop_mux)
  begin

    -- Default values
    priority_dec_en <= '0';
    SRC_RDY         <= '0';
    aux_arbiter     <= '0';

   case present_state is
    
      -- ST_ARBITER
      when st_arbiter =>
         priority_dec_en <= '1';
         aux_arbiter     <= '1';

      -- ST_DATA
      when st_data =>
         if (data_vld_mux = '1') then
            SRC_RDY         <= '1';
            if (eop_mux = '1' and DST_RDY = '1') then
               priority_dec_en <= '1';
            end if;
         end if;
      end case;

end process;

end architecture CB_SWITCH_OUT_FSM_ARCH;

