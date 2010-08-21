-- buf_fsm.vhd: FSM for Buf component
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
entity BUF_FSM is

   port (

      -- Common signals
      CLK               : in std_logic;
      RESET             : in std_logic;

      -- Start of incoming packet, active in '0'
      SOP_RX_N          : in std_logic;
      -- End of incoming packet, active in '0'
      EOP_RX_N          : in std_logic;
      -- Control component is ready
      PACODAG_RDY       : in std_logic;
      -- Discard the packet because of stats or error, valid when EOP_RX_N,
      -- active in '1'
      DISCARD_RX        : in std_logic;
      -- Data FIFO is full
      DFIFO_FULL        : in std_logic;
      -- IBUF is enabled, active in '1'
      IBUF_EN           : in std_logic;

      -- Request to control component
      PACODAG_REQ       : out std_logic;
      -- Release actual packet from Data FIFO, active in '1'
      DFIFO_RELEASE     : out std_logic;
      -- Mark start of the packet in the Data FIFO, active in '1'
      DFIFO_MARK        : out std_logic;
      -- Write data to the Data FIFO, active in '1'
      DFIFO_WR          : out std_logic;
      -- DFIFO overflow occured when active in '1'
      DFIFO_OVF         : out std_logic;
      -- PACODAG overflow occured when active in '1'
      PACODAG_OVF       : out std_logic;

      -- Status for debug purposes
      STATUS_DEBUG      : out std_logic_vector(1 downto 0);

      -- CE signals for counters
      CFC               : out std_logic;
      DFC               : out std_logic;
      BODFC             : out std_logic

   );

end entity BUF_FSM;



-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture BUF_FSM_ARCH of BUF_FSM is

   -- Type definition
   type fsm_states is (st_wait, st_frame, st_discard);

   -- Signal declaration
   signal curr_state, next_state: fsm_states;

   signal sop_ok              : std_logic;
   signal release             : std_logic;
   signal eop_ok              : std_logic;

   signal cur_st_frame        : std_logic;
   signal cur_st_discard      : std_logic;
   signal next_st_discard     : std_logic;

   -- Registers important to generate counters CE in time
   signal reg_frame_accepted  : std_logic;
   signal frame_accepted      : std_logic;
   signal reg_frame_disc_eop  : std_logic;
   signal frame_disc_eop      : std_logic;
   signal reg_frame_disc_mid  : std_logic;
   signal frame_disc_mid      : std_logic;
   signal reg_dfifo_full      : std_logic;
   signal reg_pacodag_ovf     : std_logic;

begin

   sop_ok   <= EOP_RX_N and not SOP_RX_N and PACODAG_RDY and not DFIFO_FULL
               and IBUF_EN;
   release  <= not SOP_RX_N or DISCARD_RX or DFIFO_FULL;
   eop_ok   <= not (EOP_RX_N or DISCARD_RX or DFIFO_FULL);


   -- ------------------------------------------------------------
   -- Counters

   -- Asserted when current state is st_frame
   cur_st_framep: process(curr_state)
   begin
      if curr_state = st_frame then
         cur_st_frame <= '1';
      else
         cur_st_frame <= '0';
      end if;
   end process;

   -- Asserted when current state is st_discard
   cur_st_discardp: process(curr_state)
   begin
      if curr_state = st_discard then
         cur_st_discard <= '1';
      else
         cur_st_discard <= '0';
      end if;
   end process;

   -- Asserted when next state is st_discard
   next_st_discardp: process(next_state)
   begin
      if next_state = st_discard then
         next_st_discard <= '1';
      else
         next_st_discard <= '0';
      end if;
   end process;

   frame_accepted <= eop_ok and cur_st_frame;
   frame_disc_eop <= not eop_ok and not EOP_RX_N and cur_st_frame;
   frame_disc_mid <= not cur_st_discard and next_st_discard and IBUF_EN;

   -- register reg_frame_accepted
   reg_frame_acceptedp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_frame_accepted <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_frame_accepted <= frame_accepted;
      end if;
   end process;

   -- register reg_frame_disc_eop
   reg_frame_disc_eopp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_frame_disc_eop <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_frame_disc_eop <= frame_disc_eop;
      end if;
   end process;

   -- register reg_frame_disc_mid
   reg_frame_disc_midp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_frame_disc_mid <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_frame_disc_mid <= frame_disc_mid;
      end if;
   end process;

   -- register reg_dfifo_full
   reg_dfifo_fullp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_dfifo_full <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_dfifo_full <= DFIFO_FULL;
      end if;
   end process;

   -- register reg_dfifo_full
   reg_pacodag_ovfp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_pacodag_ovf <= '0';
      elsif (CLK'event AND CLK = '1') then
         reg_pacodag_ovf <= not PACODAG_RDY;
      end if;
   end process;

   CFC   <= reg_frame_accepted;
   DFC   <= reg_frame_disc_eop or reg_frame_disc_mid;
   BODFC <= (reg_frame_disc_eop or reg_frame_disc_mid) and
            (reg_dfifo_full or reg_pacodag_ovf);

   -- ------------------------------------------------------------
   fsmp: process(CLK, RESET)
   begin
      if (RESET = '1') then
         curr_state <= st_wait;
      elsif (CLK'event AND CLK = '1') then
         curr_state <= next_state;
      end if;
   end process;

   -- ------------------------------------------------------------
   next_state_logic: process(curr_state, SOP_RX_N, DFIFO_FULL, PACODAG_RDY,
                             EOP_RX_N, release, IBUF_EN, sop_ok)
   begin

      case (curr_state) is

         -- st_wait
         when st_wait =>
            if SOP_RX_N = '0' and IBUF_EN = '1' then
               if sop_ok = '0' then
                  next_state <= st_discard;
               else
                  next_state <= st_frame;
               end if;
            else
               next_state <= st_wait;
            end if;

         -- st_frame
         when st_frame =>
            if EOP_RX_N = '0' then
               next_state <= st_wait;
            else
               if release = '1' then
                  next_state <= st_discard;
               else
                  next_state <= st_frame;
               end if;
            end if;

         -- st_discard
         when st_discard =>
            if EOP_RX_N = '0' then
               next_state <= st_wait;
            else
               next_state <= st_discard;
            end if;

      end case;

   end process;

   -- ------------------------------------------------------------
   output_logic: process(curr_state, sop_ok, release, eop_ok, EOP_RX_N,
      SOP_RX_N, PACODAG_RDY, IBUF_EN, DFIFO_FULL)
   begin
      DFIFO_OVF <= '0';
      PACODAG_OVF <= '0';

      case (curr_state) is

         -- st_wait
         when st_wait =>
            PACODAG_REQ <= sop_ok;
            DFIFO_RELEASE <= '0';
            DFIFO_MARK <= '1';
            DFIFO_WR <= sop_ok;
            STATUS_DEBUG <= "00";
            if SOP_RX_N = '0' and PACODAG_RDY = '0' and IBUF_EN = '1' then
               PACODAG_OVF <= '1';
            end if;
            if SOP_RX_N = '0' and DFIFO_FULL = '1' and IBUF_EN = '1' then
               DFIFO_OVF <= '1';
            end if;

         -- st_frame
         when st_frame =>
            PACODAG_REQ <= '0';
            DFIFO_RELEASE <= release;
            DFIFO_MARK <= '0';
            DFIFO_WR <= not release;
            STATUS_DEBUG <= "01";
            if DFIFO_FULL = '1' then
               DFIFO_OVF <= '1';
            end if;

         -- st_discard
         when st_discard =>
            PACODAG_REQ <= '0';
            DFIFO_RELEASE <= '0';
            DFIFO_MARK <= '0';
            DFIFO_WR <= '0';
            STATUS_DEBUG <= "10";

      end case;

   end process;

end architecture BUF_FSM_ARCH;
