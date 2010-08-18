--
-- uh_fifo_fl.vhd: UH FIFO - FrameLink Architecture
--
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Mikusek <petr.mikusek@liberouter.org>
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
use work.fl_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of uh_fifo_fl is

   type t_state is (REQUEST, WAIT_FOR_SOF, WAIT_FOR_EOF);
   signal present_state, next_state : t_state;

   signal dout          : std_logic_vector(15 downto 0);
   signal addr          : std_logic_vector(5 downto 0);
   signal req           : std_logic;
   signal rdy           : std_logic;
   signal wen           : std_logic;
   signal cmpz_drem     : std_logic;

   signal hfe_sof       : std_logic;
   signal hfe_eof       : std_logic;
   signal hfe_sop       : std_logic;
   signal hfe_eop       : std_logic;
   signal hfe_src_rdy   : std_logic;
   signal hfe_dst_rdy   : std_logic;

begin

   -- UH FIFO -----------------------------------------------------------------
   uh_fifo_u: entity work.uh_fifo
   port map (
      -- Control signals
      HFE_CLK        => HFE_CLK,
      LUP_CLK        => LUP_CLK,
      RESET	     => RESET,
      -- HFE interface
      HFE_DOUT       => dout,
      HFE_ADDR       => addr,
      HFE_RDY        => rdy,
      HFE_REQ        => req,
      HFE_WEN        => wen,
      -- LUP interface
      LUP_SR_VALID   => LUP_SR_VALID,
      LUP_SR_CLEAN   => LUP_SR_CLEAN,
      LUP_DATA       => LUP_DATA,
      LUP_ADDR       => LUP_ADDR,
      -- Address Decoder interface
      ADC_RD         => ADC_RD,
      ADC_ADDR       => ADC_ADDR,
      ADC_DO         => ADC_DO
   );

   -- Signals mapping ---------------------------------------------------------
   addr           <= HFE_DATA(21 downto 16);
   dout           <= HFE_DATA(15 downto 0);

   hfe_sof        <= not HFE_SOF_N;
   hfe_eof        <= not HFE_EOF_N;
   hfe_sop        <= not HFE_SOP_N;
   hfe_eop        <= not HFE_EOP_N;
   hfe_src_rdy    <= not HFE_SRC_RDY_N;
   HFE_DST_RDY_N  <= not hfe_dst_rdy;

   -- Comparator of Data Remainder --------------------------------------------
   cmpz_drem      <= '1' when (HFE_DREM = "00") else '0';

   -- -------------------------------------------------------------------------
   sync_fsm: process(RESET, HFE_CLK)
   begin
      if (RESET = '1') then
         present_state <= REQUEST;
      elsif (HFE_CLK'event and HFE_CLK = '1') then
         present_state <= next_state;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   next_state_logic: process(present_state, rdy, hfe_sof, hfe_eof, hfe_src_rdy)
   begin
      case (present_state) is
      -- ------------------------------
      when REQUEST =>
         next_state <= REQUEST;
         if (rdy = '1') then
            next_state <= WAIT_FOR_SOF;
         end if;
      -- ------------------------------
      when WAIT_FOR_SOF =>
         next_state <= WAIT_FOR_SOF;
         if (hfe_sof = '1' and hfe_eof = '0' and hfe_src_rdy = '1') then
            next_state <= WAIT_FOR_EOF;
         elsif (hfe_sof = '1' and hfe_eof = '1' and hfe_src_rdy = '1') then
            next_state <= REQUEST;
         end if;
      -- ------------------------------
      when WAIT_FOR_EOF =>
         next_state <= WAIT_FOR_EOF;
         if (hfe_eof = '1' and hfe_src_rdy = '1') then
            next_state <= REQUEST;
         end if;
      -- ------------------------------
      when others =>
         next_state <= REQUEST;
      -- ------------------------------
      end case;
   end process;

   -- -------------------------------------------------------------------------
   output_logic: process(present_state, rdy, cmpz_drem, hfe_sof, hfe_src_rdy)
   begin
      req         <= '0';
      wen         <= '0';
      hfe_dst_rdy <= '0';

      case (present_state) is
      -- ------------------------------
      when REQUEST =>
         req         <= not rdy;
      -- ------------------------------
      when WAIT_FOR_SOF =>
         hfe_dst_rdy <= '1';
         wen         <= hfe_sof and hfe_src_rdy and (not cmpz_drem);
      -- ------------------------------
      when WAIT_FOR_EOF =>
         hfe_dst_rdy <= '1';
         wen         <= hfe_src_rdy;
      -- ------------------------------
      when others =>
         null;
      -- ------------------------------
      end case;
   end process;

end architecture full;

