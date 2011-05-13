-- simple_marker_owr.vhd: Implementation of simple FrameLink marker
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
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
entity SIMPLE_FL_MARKER_OWR is
   generic(
      -- Frame link width
      DATA_WIDTH   : integer := 32;

      -- number of framelink parts
      PARTS        : integer := 3;

      -- which part will be marked or in which part will be inserted data
      MARK_PART    : integer := 1;

      -- mark options
      OFFSET       : integer := 4; -- "Mark" position - distance in bytes from start
                                   -- part

      MARK_SIZE    : integer := 1  -- Size of "Mark" in Bytes
   );
   port (
      CLK          : in  std_logic; -- clock
      RST          : in  std_logic; -- reset

      -- mark input
      MARK         : in  std_logic_vector(MARK_SIZE*8-1 downto 0);

      -- valid mark value
      MARK_VALID   : in  std_logic;
      -- mark was placed, next mark expected
      MARK_NEXT    : out std_logic;

      -- Framelink RX interface
      RX_DATA      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM       : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N     : in  std_logic;
      RX_EOF_N     : in  std_logic;
      RX_SOP_N     : in  std_logic;
      RX_EOP_N     : in  std_logic;
      RX_SRC_RDY_N : in  std_logic;
      RX_DST_RDY_N : out std_logic;

      -- Framelink TX interface
      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM       : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N     : out std_logic;
      TX_EOF_N     : out std_logic;
      TX_SOP_N     : out std_logic;
      TX_EOP_N     : out std_logic;
      TX_SRC_RDY_N : out std_logic;
      TX_DST_RDY_N : in std_logic
   );
end entity SIMPLE_FL_MARKER_OWR;


-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of SIMPLE_FL_MARKER_OWR is

   constant DATA_SIZE : integer := DATA_WIDTH/8;
   
   constant BEG_WORD : integer := OFFSET/DATA_SIZE;
   constant END_WORD : integer := (OFFSET+MARK_SIZE-1)/DATA_SIZE;

   -- counts number of words that mark affects
   function count_mark_words(OFFSET, MARK_SIZE, DATA_SIZE : integer) return integer is
      variable BEG_PAD : integer;
      variable END_PAD : integer;
   begin
      BEG_PAD := OFFSET mod DATA_SIZE;
      END_PAD := (DATA_SIZE - ((BEG_PAD + MARK_SIZE) mod DATA_SIZE)) mod DATA_SIZE;
     
      -- 1 word if BEG_PAD exists and 1 word if END_PAD exists
      return minimum(BEG_PAD, 1) + minimum(END_PAD, 1) + (MARK_SIZE - BEG_PAD - END_PAD)/DATA_SIZE;
   end function;

   -- number of words that mark affects
   constant MARK_WORDS : integer := count_mark_words(OFFSET, MARK_SIZE, DATA_SIZE);
   
   -- counter of position in the MARK (in words)
   signal cnt_mark_ce   : std_logic;
   signal cnt_mark_clr  : std_logic;
   signal cnt_mark      : std_logic_vector(max(log2(MARK_WORDS)-1, 0) downto 0);

   -- counter to know which part was reached
   signal cnt_part_ce   : std_logic;
   signal cnt_part_clr  : std_logic;
   signal cnt_part      : std_logic_vector(log2(PARTS) downto 0);

   -- counter to know which word was reached
   signal cnt_word_ce   : std_logic;
   signal cnt_word_clr  : std_logic;
   -- NOTE: it should be (OFFSET+MARK_SIZE-1), but the '-1' is not good
   --       when OFFSET = 0 and MARK_SIZE = 1 (leads to 0 downto 0)
   signal cnt_word      : std_logic_vector(log2(OFFSET + MARK_SIZE) downto 0);

   -- FrameLink values in positive form
   signal tx_dst_rdy    : std_logic;
   signal rx_src_rdy    : std_logic;

   -- is in MARK_PART
   signal is_markpart : std_logic;
   -- a word to be marked is now in the input (so we are marking NOW)
   signal is_markword : std_logic;
   -- marker is enabled (internal only), mostly extra control of counters
   signal marker_en : std_logic;
   -- data ready to output (through MARK_VALID)
   signal data_rdy : std_logic;
   -- value for MARK_NEXT
   signal mark_next_set : std_logic;

   -- finite state machine that manages the MARK
   type state_t is (NO_MARK, HOLD_MARK, NO_MARK_SKIP, HOLD_MARK_SKIP);
   signal cstate : state_t;
   signal nstate : state_t;

   -- help signals for the FSM
   signal rx_isreading_n : std_logic;
   signal tx_iswriting_n : std_logic;
   signal mark_rdy : std_logic;

   -- register for holding the MARK
   signal reg_mark : std_logic_vector((MARK_SIZE*8)-1 downto 0);
   signal reg_mark_ce : std_logic;

begin

-- ----------------------------------------------------------------------------
--                  Decodes FL signals and controls counters 
-- ----------------------------------------------------------------------------

   fl_decoder : process(CLK, RX_SOP_N, RX_SOF_N, RX_EOP_N, RX_EOF_N, marker_en, is_markpart, is_markword)
      -- current combination
      variable sel : std_logic_vector(3 downto 0);

      -- possible input combinations 
      constant SOF_SOP           : std_logic_vector(3 downto 0) := "0101";
      constant SOF_SOP_EOP       : std_logic_vector(3 downto 0) := "0100";
      constant SOF_SOP_EOP_EOF   : std_logic_vector(3 downto 0) := "0000";
      constant EOF_EOP           : std_logic_vector(3 downto 0) := "1010";
      constant EOF_SOP_EOP       : std_logic_vector(3 downto 0) := "1000";
      constant SOP               : std_logic_vector(3 downto 0) := "1101";
      constant SOP_EOP           : std_logic_vector(3 downto 0) := "1100";
      constant EOP               : std_logic_vector(3 downto 0) := "1110";
      constant NONE              : std_logic_vector(3 downto 0) := "1111";
   begin
      sel := RX_SOF_N & RX_EOF_N & RX_SOP_N & RX_EOP_N;
      
      cnt_part_ce <= '0';
      cnt_part_clr <= '0';
      cnt_mark_ce <= '0'; 
      cnt_mark_clr <= '0';
      cnt_word_clr <= '0';
      
      case sel is
         when SOF_SOP =>
            cnt_mark_ce <= is_markword; 

         when SOF_SOP_EOP =>
            cnt_part_ce <= '1';
            cnt_word_clr <= '1';
            
         when SOF_SOP_EOP_EOF =>
            cnt_mark_clr <= '1';
            cnt_word_clr <= '1';
            
         when EOF_EOP =>
            cnt_part_clr <= '1';
            cnt_word_clr <= '1';
            cnt_mark_clr <= '1';
            
         when EOF_SOP_EOP =>
            cnt_part_clr <= '1';
            cnt_word_clr <= '1';
            cnt_mark_clr <= '1';
            
         when SOP =>
            cnt_mark_ce <= is_markword; 

         when SOP_EOP =>
            cnt_part_ce <= '1';
            cnt_word_clr <= '1';
            
         when EOP =>
            cnt_part_ce <= '1';
            cnt_word_clr <= '1';
            
         when NONE =>
            cnt_mark_ce <= is_markword; 

         when others =>
      end case;
   end process;


-- ----------------------------------------------------------------------------
--                   Overwriting output module declaration
-- ----------------------------------------------------------------------------

   marker_out : entity work.SIMPLE_FL_MARKER_OWR_OUT
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      OFFSET => OFFSET,
      MARK_SIZE => MARK_SIZE,
      MARK_WORDS => MARK_WORDS
   )
   port map (
      MARK => reg_mark, 
      MARK_POS => cnt_mark,
      IS_MARKING => is_markword,

      RX_DATA => RX_DATA,
      RX_REM => RX_REM,
      TX_DATA => TX_DATA,
      TX_REM => TX_REM
   );


-- ----------------------------------------------------------------------------
--                           FSM for manage the mark
-- ----------------------------------------------------------------------------

   fsm_mark_state : process(CLK, RST, nstate)
   begin
      if CLK'event and CLK = '1' then
         if RST = '1' then
            cstate <= NO_MARK;
         else
            cstate <= nstate;
         end if;
      end if;
   end process;
  
   fsm_mark_next_output : process(CLK, cstate, is_markpart, is_markword, cnt_mark, tx_iswriting_n, rx_isreading_n, RX_EOP_N, MARK_VALID)
      variable end_of_mark : boolean;
      variable end_of_part : boolean;
   begin
      nstate <= cstate;
      mark_next_set <= '0';
      mark_rdy <= '0';
      reg_mark_ce <= '0';

      end_of_mark := (cnt_mark = conv_std_logic_vector(MARK_WORDS - 1, cnt_mark'length)) 
                     and is_markword = '1' and tx_iswriting_n = '0';
      end_of_part := RX_EOP_N = '0' and rx_isreading_n = '0'; 

      case cstate is
         when NO_MARK =>
            if MARK_VALID = '1' then
               nstate <= HOLD_MARK;

               -- outputs
               mark_next_set <= '1';
               reg_mark_ce <= '1';
            end if;

         when NO_MARK_SKIP =>
            if MARK_VALID = '1' then
               if end_of_part then
                  nstate <= HOLD_MARK;
               else
                  nstate <= HOLD_MARK_SKIP; 
               end if;

               -- outputs
               mark_next_set <= '1';
               reg_mark_ce <= '1';

            elsif end_of_part then
               nstate <= NO_MARK;
            end if;

         when HOLD_MARK_SKIP =>
            if end_of_part then
               nstate <= HOLD_MARK;
            end if;

         when HOLD_MARK =>
            if is_markpart = '1' and (end_of_part) then
               nstate <= NO_MARK;

            elsif is_markpart = '1' and (end_of_mark) then
               nstate <= NO_MARK_SKIP;

            end if;
               
            -- output
            mark_rdy <= '1';

      end case;
   end process;

   register_mark : process(CLK, reg_mark_ce, MARK)
   begin
      if CLK'event and CLK='1' then
         if reg_mark_ce = '1' then
            reg_mark <= MARK;
         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
--                  Comparators to detect words to be marked
-- ----------------------------------------------------------------------------

   cmp_is_markpart : process(CLK, cnt_part)
   begin
      if cnt_part = MARK_PART or (PARTS = 1 and MARK_PART = 0) then
         is_markpart <= '1';
      else
         is_markpart <= '0';
      end if;
   end process;

   cmp_is_markword : process(CLK, cnt_word, is_markpart)
   begin
      if cnt_word >= BEG_WORD and cnt_word <= END_WORD then
         is_markword <= is_markpart;
      else
         is_markword <= '0';
      end if;
   end process;

-- ----------------------------------------------------------------------------
--                               Counters 
-- ----------------------------------------------------------------------------

   counter_part : process(CLK, RST, cnt_part_ce, cnt_part_clr, marker_en)
   begin
      if CLK'event and CLK = '1' then
         if RST = '1' then
            cnt_part <= (others => '0');

         elsif marker_en = '1' then
            if cnt_part_clr = '1' then
               cnt_part <= (others => '0');
            
            elsif cnt_part_ce = '1' then
               cnt_part <= cnt_part + 1;
            
            end if;

         end if;
      end if;
   end process;

   counter_word : process(CLK, RST, cnt_word_ce, cnt_word_clr, marker_en)
   begin
      if CLK'event and CLK = '1' then
         if RST = '1' then
            cnt_word <= (others => '0');

         elsif marker_en = '1' then
            if cnt_word_clr = '1' then
               cnt_word <= (others => '0');

            elsif cnt_word_ce = '1' then
               if cnt_word + 1 = 0 then 
                  -- the max value was reached, stay on this value
                  cnt_word <= cnt_word;

               else 
                  cnt_word <= cnt_word + 1;

               end if;

            end if;
         end if;
      end if;
   end process;

   counter_mark : process(CLK, RST, cnt_mark_ce, cnt_mark_clr, marker_en)
   begin
      if CLK'event and CLK = '1' then
         if RST = '1' then
            cnt_mark <= (others => '0');

         elsif marker_en = '1' then
            if cnt_mark_clr = '1' then
               cnt_mark <= (others => '0');

            elsif cnt_mark_ce = '1' then
               cnt_mark <= cnt_mark + 1; 

            end if;

         end if;
      end if;
   end process;

-- ----------------------------------------------------------------------------
--                               Signal connections
-- ----------------------------------------------------------------------------

   tx_iswriting_n <= RX_SRC_RDY_N or TX_DST_RDY_N or not(data_rdy);
   rx_isreading_n <= RX_SRC_RDY_N or TX_DST_RDY_N or not(data_rdy);

   -- when not marking, data_rdy is always '1':
   RX_DST_RDY_N <= TX_DST_RDY_N or not(data_rdy);
   TX_SRC_RDY_N <= RX_SRC_RDY_N or not(data_rdy);
   TX_SOP_N <= RX_SOP_N;
   TX_SOF_N <= RX_SOF_N;
   TX_EOP_N <= RX_EOP_N;
   TX_EOF_N <= RX_EOF_N;
   MARK_NEXT <= mark_next_set;

   tx_dst_rdy <= not(TX_DST_RDY_N);
   rx_src_rdy <= not(RX_SRC_RDY_N);

   -- words are counted only when tha MARK_PART is currently processed:
   cnt_word_ce <= is_markpart;
   -- when not marking, data are not depend on MARK_VALID flag:
   data_rdy <= mark_rdy when is_markword = '1' else '1';
   -- when not marking, data_rdy is always '1':
   marker_en <= rx_src_rdy and tx_dst_rdy and data_rdy;

end architecture;
