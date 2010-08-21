-- xgmii_dec_fsm.vhd: FSM foe xgmii_dec
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
entity XGMII_DEC_FSM is
   port(
      -- Common signals
      -- clock sigal
      CLK               : in std_logic;
      -- asynchronous reset, active in '1'
      RESET             : in std_logic;

      -- input
      SOP_IN         : in std_logic;
      EOP_IN         : in std_logic;
      ERR_IN         : in std_logic;

      -- output
      SOP_OUT        : out std_logic;
      EOP_OUT        : out std_logic;
      ERR_OUT        : out std_logic
   ); 
end entity XGMII_DEC_FSM;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture XGMII_DEC_FSM_ARCH of XGMII_DEC_FSM is
   -- Constant declaratiom
   constant CONST_PIPELINE_WAIT : integer := 5;

   -- Type definition
   type fsm_states is (st_reset, st_ready, st_packet);

   -- Signals declaration
   signal curr_state, next_state : fsm_states;
   attribute SAFE_FSM : boolean;
   attribute SAFE_FSM of fsm_states : type is true;

   signal cnt_pipeline_rdy : std_logic_vector(2 downto 0);
   signal pipeline_rdy : std_logic;

begin

   -- cnt_pipeline_rdy counter
   cnt_pipeline_rdyp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_pipeline_rdy <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         cnt_pipeline_rdy <= cnt_pipeline_rdy + 1;
      end if;
   end process;

   -- pipeline_rdy comparator
   pipeline_rdyp: process(cnt_pipeline_rdy)
   begin
      if (cnt_pipeline_rdy = CONST_PIPELINE_WAIT) then
         pipeline_rdy <= '1';
      else
         pipeline_rdy <= '0';
      end if;
   end process;

   -- -------------------------------------------------------
   fsmp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         curr_state <= st_reset;
      elsif (CLK'event AND CLK = '1') then
         curr_state <= next_state;
      end if;
   end process;

   -- -------------------------------------------------------
   next_state_logic: process(curr_state, SOP_IN, EOP_IN, ERR_IN,
                                               pipeline_rdy)
   begin
      case (curr_state) is

         -- st_reset
         when st_reset => 
            if (pipeline_rdy = '0') then
               next_state <= st_reset;
            else
               next_state <= st_ready;
            end if;

         -- st_ready
         when st_ready =>
            if (SOP_IN = '1' and EOP_IN = '0') then
               next_state <= st_packet;
            else
               next_state <= st_ready;
            end if;

         -- st_packet
         when st_packet =>
            if (EOP_IN = '1' or ERR_IN = '1') then
               next_state <= st_ready;
            else
               next_state <= st_packet;
            end if;

         when others =>
            next_state <= st_reset;

      end case;
   end process next_state_logic;

   -- -------------------------------------------------------
   output_logic: process(curr_state, SOP_IN, EOP_IN, ERR_IN)
   begin
      case (curr_state) is
         -- st_ready
         when st_ready =>
            SOP_OUT <= SOP_IN and not EOP_IN;
            EOP_OUT <= '0';
            ERR_OUT <= ERR_IN or EOP_IN;

         -- st_packet
         when st_packet =>
            SOP_OUT <= '0';
            EOP_OUT <= EOP_IN or ERR_IN;
            ERR_OUT <= ERR_IN or SOP_IN;

         -- other states
         when others =>
            SOP_OUT <= '0';
            EOP_OUT <= '0';
            ERR_OUT <= '0';

      end case;
   end process output_logic;

end architecture XGMII_DEC_FSM_ARCH;
