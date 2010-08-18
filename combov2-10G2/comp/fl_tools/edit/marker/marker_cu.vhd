-- marker_cu.vhd: FrameLink marker control unit.
-- Copyright (C) 2006 CESNET
-- Author(s): Michal Trs <trsm1@liberouter.org>
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
-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_MARKER_CU is
   generic(
      DATA_WIDTH   : integer := 32;
      FRAME_POS    : integer;
      MARK_SIZE    : integer
   );
   port(
      CLK          : in std_logic;
      RESET        : in std_logic;

      FRAME        : in std_logic;
      RX_SRC_RDY   : in std_logic;
      TX_DST_RDY   : in std_logic;
      RX_EOP       : in std_logic;
      RX_REM       : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

      RX_STALL     : out std_logic;
      TX_EOP       : out std_logic;
      TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      OUTPUT       : out std_logic_vector(1 downto 0)
   );
end entity FL_MARKER_CU;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture CU_BODY of FL_MARKER_CU is

   constant REM_MAX_VAL : integer := DATA_WIDTH/8 - MARK_SIZE - 1;
   constant ALIGN       : boolean := DATA_WIDTH / 8 = MARK_SIZE;

   constant cnt_width   : integer := log2(FRAME_POS+2);

   type t_state is (st_direct,st_ins,st_shift,st_add_last,st_wait);

   signal cur_state     : t_state;
   signal next_state    : t_state;

   signal cnt_hdr       : std_logic_vector(cnt_width downto 0);
   signal cnt_hdr_of    : std_logic;

   signal fsm_ins       : boolean;
   signal fsm_add_last  : boolean;
   signal fsm_reset     : boolean;

   signal rem_hold      : boolean;

   signal RDY           : std_logic;

   -- signal RDY2          : std_logic;

begin

  RDY <= RX_SRC_RDY and TX_DST_RDY;
   -- ------------------------------------------------------
   -- FSM
   process(CLK,RESET)
   begin
      if RESET = '1' then
         cur_state <= st_direct;
      elsif CLK = '1' and CLK'event then
         if TX_DST_RDY = '1' then
            cur_state <= next_state;
         end if;
      end if;
   end process;

   -- next state logic
   process(cur_state,fsm_ins,fsm_reset,fsm_add_last)
   begin
      next_state <= st_direct;

      case cur_state is
         when st_direct =>
            if fsm_ins and ALIGN then
               next_state <= st_wait;
            elsif fsm_ins and fsm_reset then
               next_state <= st_direct;
            elsif fsm_add_last then
               next_state <= st_add_last;
            elsif fsm_ins then
               next_state <= st_ins;
            end if;
         when st_ins =>
            if fsm_reset or ALIGN then
               next_state <= st_direct;
            elsif fsm_add_last then
               next_state <= st_add_last;
            else
               next_state <= st_shift;
            end if;
         when st_shift =>
            if fsm_add_last then
               next_state <= st_add_last;
            elsif fsm_reset then
               next_state <= st_direct;
            else
               next_state <= st_shift;
            end if;
         when st_wait =>
               next_state <= st_direct;
         when st_add_last => 
               next_state <= st_direct;
      end case;
   end process;

   -- output logic
   process(cur_state,fsm_ins,fsm_reset,fsm_add_last)
   begin
      OUTPUT <= "00";
      TX_EOP <= '0';
      RX_STALL <= '0';
      rem_hold <= false;

      case cur_state is
         when st_direct =>
            if fsm_ins or fsm_add_last then
               OUTPUT <= "01";
            end if;
            --
            if fsm_reset and ALIGN then
               TX_EOP <= '1';
            end if;
         when st_ins =>
            OUTPUT <= "10";
            if ALIGN then
               RX_STALL <= '1';
            end if;
            --
            if fsm_reset then
               TX_EOP <= '1';
            end if;
         when st_shift =>
            OUTPUT <= "10";
            if fsm_reset then
               TX_EOP <= '1';
            end if;
         when st_wait =>
            RX_STALL <= '1';
            OUTPUT <= "10"; -- stored data
            -- TX_EOP <= '1';
            rem_hold <= true;
         when st_add_last =>
            OUTPUT <= "11";
            TX_EOP <= '1';
            rem_hold <= true;
      end case;
   end process;

   -- ------------------------------------------------------
   -- others logic

   -- frame cycle counter
   process(CLK, RESET)
   begin
      if RESET = '1' then
         cnt_hdr <= (others => '0');
         cnt_hdr_of <= '0';
      elsif CLK = '1' and CLK'event then
         if (FRAME = '1') and (RDY = '1') then
            cnt_hdr <= cnt_hdr + '1';
            if (cnt_hdr = not conv_std_logic_vector(0,cnt_width)) then
              cnt_hdr_of <= '1'; -- catch counter overflow
            end if;
         elsif FRAME = '0' then
            cnt_hdr <= (others => '0');
            cnt_hdr_of <= '0';
         end if;
      end if;
   end process;


   -------------------------------------
   -- FSM driving signals
   fsm_ins <= (FRAME = '1') and (RDY = '1') and
      (cnt_hdr = conv_std_logic_vector(FRAME_POS,cnt_width)) and (cnt_hdr_of='0');
   fsm_reset <= (RX_EOP = '1') and (RDY = '1')
      and ((RX_REM <= REM_MAX_VAL) or ALIGN);
   fsm_add_last <= (RX_EOP = '1') and (RDY = '1') and (RX_REM > REM_MAX_VAL)
      and not ALIGN;


   -- TX_REM logic (adder + DFF)
   process(CLK,RESET)
   begin
      if RESET = '1' then
         TX_REM <= (others => '0');
      elsif CLK = '1' and CLK'event then
         if RDY = '1' then
            if RX_EOP = '1' then
               TX_REM <= RX_REM + MARK_SIZE;
            elsif not rem_hold then
               TX_REM <= RX_REM;
            end if;
         end if;
      end if;
   end process;

end architecture CU_BODY;
