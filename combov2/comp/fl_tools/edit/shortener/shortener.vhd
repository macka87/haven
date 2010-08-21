-- shortener.vhd: FrameLink Shortener architecture
-- Copyright (C) 2008 CESNET
-- Author(s): Michal Kajan <xkajan01@stud.fit.vutbr.cz>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Architecture: FL_SHORTENER
-- ----------------------------------------------------------------------------

architecture FL_SHORTENER_ARCH of FL_SHORTENER is 

   -- functions definitions
   ----------------------------------------------------------------------------
   -- function computing number of processed words from given number
   -- of kept bytes when width of data is known
   function words (bytes_kept, data_width : integer) return integer is
      variable result : integer;
   begin
      result := bytes_kept/(data_width/8);
      -- it is important to include last incomplete word as well
      if ((bytes_kept mod (data_width/8)) /= 0) then
         result := result + 1;
      end if;
      return result;
   end function words;

   -- constants definitions
   ---------------------------------------------------------------------------- 

   -- default value of REM signal used for output - FSM chooses correct value
   -- of REM signal from input and this constant depending on number of bytes
   -- currently received from input and number of bytes to be kept
   CONSTANT REM_CONST   : integer := (BYTES_KEPT-1) mod (DATA_WIDTH/8);

   -- internal signals
   ----------------------------------------------------------------------------
   -- information about readiness of source and destination for transfer
   signal transmit_en   : std_logic;

   -- EOP counter (number parts in FrameLink frame)
   signal cnt_eop       : std_logic_vector(log2(PARTS) downto 0);

   -- word counter (number of words in part of FrameLink frame)
   signal cnt_word      : std_logic_vector(log2(words(BYTES_KEPT, DATA_WIDTH))
                                                                     downto 0);
   -- count enable signal for counter of parts of FrameLink frame
   signal cnt_eop_en    : std_logic;

   -- count enable signal for counter of words in part of FrameLink frame
   signal cnt_word_en   : std_logic;

   -- reset signal for counter of parts of FrameLink frame
   signal cnt_eop_rst   : std_logic;

   -- reset signal for counter of words in part of FrameLink frame
   signal cnt_word_rst  : std_logic;

   -- internally used signal RX_DST_RDY_N
   signal pre_rx_dst_rdy_n   : std_logic;

begin

   -- connecting certain input RX signals with output TX signals
   TX_DATA      <= RX_DATA;
   TX_SOF_N     <= RX_SOF_N;
   TX_SOP_N     <= RX_SOP_N;

   -- connecting generated pre_rx_dst_rdy_n signal with output RX_DST_RDY_N signal
   RX_DST_RDY_N <= pre_rx_dst_rdy_n;

   -- setting transmit_en signal (important for FSM)
   transmit_en  <= RX_SRC_RDY_N or pre_rx_dst_rdy_n;

   -- setting count enable signal for counter of parts of FrameLink frame
   cnt_eop_en   <= RX_EOP_N or transmit_en;

   -- setting count enable signal for counter of words in part of FL frame
   cnt_word_en  <= transmit_en;

   -- setting reset signal for counter of parts of FrameLink frame
   -- RX_EOF can cause reset - but both components must be ready
   cnt_eop_rst  <= RESET or not(RX_EOF_N or transmit_en);

   -- setting reset signal for counter of words in part of FrameLink frame
   -- RX_EOP can cause reset - but both components must be ready
   cnt_word_rst <= RESET or not(RX_EOP_N or transmit_en);

   -- counter of parts in FrameLink frame
   cnt_eop_p : process(CLK, cnt_eop_en, cnt_eop_rst)
   begin
      if (CLK'event and CLK='1') then
         -- reseting value of counter
         if (cnt_eop_rst = '1') then
            cnt_eop <= (others => '0');
         -- counting enabled
         elsif (cnt_eop_en = '0') then
            cnt_eop <= cnt_eop + 1;
         end if;
      end if;
   end process cnt_eop_p;

   -- counter of words in part of FrameLink frame
   cnt_word_p : process(CLK, cnt_word_en, cnt_word_rst)
   begin
      if (CLK'event and CLK = '1') then
         -- reseting value of counter
         if (cnt_word_rst = '1') then
            cnt_word <= (others => '0');
         -- counting enabled
         elsif (cnt_word_en = '0') then
            cnt_word <= cnt_word + 1;
         end if;
      end if;
   end process cnt_word_p;   

   -- -------------------------------------------------------------------------
   --  FSM
   -- -------------------------------------------------------------------------
   fsmi : entity work.FL_SHORTENER_FSM
      generic map(
        DATA_WIDTH     => DATA_WIDTH,
        PART_NUM       => PART_NUM,
        WORDS_KEPT     => words(BYTES_KEPT, DATA_WIDTH),
        PARTS          => PARTS,
        REM_CONST      => REM_CONST
      )
      port map(            
         CLK           => CLK,
         RESET         => RESET,
         SRC_RDY       => RX_SRC_RDY_N,
         DST_RDY       => TX_DST_RDY_N,
         DREM          => RX_REM,
         EOP           => RX_EOP_N,
         EOF           => RX_EOF_N,
         CNT_EOP       => cnt_eop,
         CNT_WORD      => cnt_word,
         FSM_EOP       => TX_EOP_N,
         FSM_EOF       => TX_EOF_N,
         FSM_SRC_RDY   => TX_SRC_RDY_N,
         FSM_DST_RDY   => pre_rx_dst_rdy_n,
         FSM_REM       => TX_REM
      );   

end architecture FL_SHORTENER_ARCH;
