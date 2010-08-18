-- decoder.vhd: FrameLink decoder
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_DEC is

   -- ------------------ Signals declaration ----------------------------------
   -- (de)multiplexers
   signal dmx_pairs_out    : std_logic_vector(5 downto 0);
   
   -- registers
   signal reg_packet       : std_logic;
   signal reg_packet_we    : std_logic;
   
   -- comparators
   signal cmp_header       : std_logic;
   signal cmp_payload      : std_logic;
   signal cmp_footer       : std_logic;
   
   -- FSM signals
   signal fsm_eop          : std_logic;
   signal fsm_eof          : std_logic;
   signal fsm_part         : std_logic_vector(1 downto 0);
   
   -- others
   signal sof_i            : std_logic;
   signal sop_i            : std_logic;
   signal eop_i            : std_logic;
   signal eof_i            : std_logic;
   signal input_pair       : std_logic_vector(1 downto 0);
   signal en               : std_logic;
   signal pkt_trans        : std_logic;   -- packet is transmitted now

begin
   -- directly mapped signals -------------------------------------------------
   sof_i          <= not SOF_N;
   sop_i          <= not SOP_N;
   eop_i          <= not EOP_N;
   eof_i          <= not EOF_N;

   en             <= (not SRC_RDY_N) and DST_RDY;
   input_pair     <= eop_i & sop_i;
   pkt_trans      <= sof_i or reg_packet;
   
   -- FSM signals
   fsm_eop        <= eop_i and en;
   fsm_eof        <= eof_i and en;
   
   -- register control signals
   reg_packet_we  <= sof_i or (eof_i and en);

   -- comparators
   cmp_header     <= '1' when fsm_part = "00" else '0';
   cmp_payload    <= '1' when fsm_part = "01" else '0';
   cmp_footer     <= '1' when fsm_part = "10" else '0';
   
   -- output interface mapping
   SOF            <= sof_i;
   SOHDR          <= dmx_pairs_out(0);
   EOHDR          <= dmx_pairs_out(1);
   HDR_FRAME      <= cmp_header and pkt_trans;
   
   SOPLD          <= dmx_pairs_out(2);
   EOPLD          <= dmx_pairs_out(3);
   PLD_FRAME      <= cmp_payload and pkt_trans;
   
   SOFTR          <= dmx_pairs_out(4);
   EOFTR          <= dmx_pairs_out(5);
   FTR_FRAME      <= cmp_footer and pkt_trans;
   
   EOF            <= eof_i;
   SRC_RDY        <= not SRC_RDY_N;
   DST_RDY_N      <= not DST_RDY;


   -- ------------------ register reg_packet ----------------------------------
   reg_packetp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_packet <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (reg_packet_we = '1') then
            reg_packet <= sof_i;
         end if;
      end if;
   end process;


   -- ---------------- generate right demultiplexer ---------------------------
   dmx_pairs_outp: process (fsm_part, input_pair)
   begin
      dmx_pairs_out <= (others => '0');
      case fsm_part is
         when "00" => dmx_pairs_out(1 downto 0) <= input_pair;
         when "01" => dmx_pairs_out(3 downto 2) <= input_pair;
         when "10" => dmx_pairs_out(5 downto 4) <= input_pair;
         when others => null;
      end case;
   end process;

   -- mapping main FSM
   FL_DEC_FSM_I : entity work.FL_DEC_FSM
   generic map(
      HEADER      => HEADER,
      FOOTER      => FOOTER
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      -- input signals
      EOP         => fsm_eop,
      EOF         => fsm_eof,
      -- output signals
      PART        => fsm_part
   );

end architecture full;
