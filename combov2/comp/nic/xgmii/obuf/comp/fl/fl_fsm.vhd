-- fl_fsm.vhd: FL part of XGMII OBUF - FSM
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


entity obuf_xgmii_fl_fsm is

   generic(
      -- Frames contain control part
      CTRL_CMD          : boolean
   );

   port(
      -- Clock
      CLK         : in std_logic;
      -- Synchronous reset
      RESET       : in std_logic;

      -- RX FrameLink signals
      SOP_N       : in std_logic;
      EOP_N       : in std_logic;
      SRC_RDY_N   : in std_logic;

      -- Signals from FIFOs
      DFIFO_OVF   : in std_logic;
      DFIFO_FULL  : in std_logic;
      HFIFO_FULL  : in std_logic;

      -- Output
      DST_RDY_N   : out std_logic;
      DFIFO_MARK  : out std_logic;
      DFIFO_WR    : out std_logic;
      HFIFO_WR    : out std_logic
   );

end entity obuf_xgmii_fl_fsm;

architecture obuf_xgmii_fl_fsm_arch of obuf_xgmii_fl_fsm is

   -- Type definition
   type fsm_states is (st_idle, st_data, st_overflow, st_footer, st_no_footer, st_first_data);

   -- Signals declaration
   signal curr_state, next_state : fsm_states;
   signal sop_ni                 : std_logic;
   signal eop_ni                 : std_logic;

begin

   sop_ni <= SOP_N or SRC_RDY_N;
   eop_ni <= EOP_N or SRC_RDY_N;

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
   next_state_logic: process(curr_state, HFIFO_FULL, DFIFO_FULL, DFIFO_OVF,
                             sop_ni, eop_ni, SRC_RDY_N)
   begin
      case (curr_state) is

         -- st_idle
         when st_idle =>
            if (DFIFO_FULL = '0') then -- and sop_ni = '0') then
               next_state <= st_data;
            else
               next_state <= st_idle;
            end if;
 
         -- st_data
         when st_data =>
            if (DFIFO_OVF = '1') then
               next_state <= st_overflow;
            elsif (DFIFO_FULL = '0' and eop_ni = '0' and CTRL_CMD = true) then
               next_state <= st_footer;
            elsif (DFIFO_FULL = '0' and eop_ni = '0' and CTRL_CMD = false) then
               if (HFIFO_FULL = '0') then
                  next_state <= st_first_data;
               else
                  next_state <= st_no_footer;
               end if;
            else
               next_state <= st_data;
            end if;

         -- st_overflow
         when st_overflow =>
            if (eop_ni = '0') then
               next_state <= st_idle;
            else
               next_state <= st_overflow;
            end if;

         -- st_footer
         when st_footer =>
            if (SRC_RDY_N = '0' and HFIFO_FULL = '0') then
               next_state <= st_idle;
            else
               next_state <= st_footer;
            end if;

         -- st_no_footer
         when st_no_footer =>
            if (HFIFO_FULL = '0') then
               next_state <= st_idle;
            else
               next_state <= st_no_footer;
            end if;

         -- st_first_data
         when st_first_data =>
            if (DFIFO_OVF = '1') then
               next_state <= st_overflow;
            elsif (DFIFO_FULL = '0' and eop_ni = '0' and CTRL_CMD = true) then
               next_state <= st_footer;
            elsif (DFIFO_FULL = '0' and eop_ni = '0' and CTRL_CMD = false) then
               if (HFIFO_FULL = '0') then
                  next_state <= st_first_data;
               else
                  next_state <= st_no_footer;
               end if;
            else
               next_state <= st_data;
            end if;

      end case;
   end process next_state_logic;

   -- --------------------------------------------------------------------------
   output_logic: process(curr_state, SRC_RDY_N, DFIFO_FULL, HFIFO_FULL, eop_ni)
   begin
      DST_RDY_N  <= '1';
      DFIFO_MARK <= '0';
      DFIFO_WR   <= '0';
      HFIFO_WR   <= '0';

      case (curr_state) is

         -- st_idle
         when st_idle =>
            DFIFO_MARK <= '1';

         -- st_data
         when st_data =>
            DFIFO_WR <= not SRC_RDY_N and not DFIFO_FULL;
            DST_RDY_N <= DFIFO_FULL;
            if (DFIFO_FULL = '0' and HFIFO_FULL = '0' and eop_ni = '0' and
                  CTRL_CMD = false) then
               HFIFO_WR <= not HFIFO_FULL;
            end if;

         -- st_overflow
         when st_overflow =>
            DST_RDY_N <= '0';

         -- st_footer
         when st_footer =>
            HFIFO_WR <= not SRC_RDY_N;
            DST_RDY_N <= HFIFO_FULL;

         -- st_no_footer
         when st_no_footer =>
            HFIFO_WR <= not HFIFO_FULL;

         -- st_first_data
         when st_first_data =>
            DFIFO_MARK <= '1';
            DFIFO_WR <= not SRC_RDY_N and not DFIFO_FULL;
            DST_RDY_N <= DFIFO_FULL;
            if (DFIFO_FULL = '0' and HFIFO_FULL = '0' and eop_ni = '0' and
                  CTRL_CMD = false) then
               HFIFO_WR <= not HFIFO_FULL;
            end if;

      end case;

   end process output_logic;
            
end architecture obuf_xgmii_fl_fsm_arch;
