-- simple_marker_ins.vhd: Implementation of simple FrameLink marker
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
entity SIMPLE_FL_MARKER_INS is
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
end entity SIMPLE_FL_MARKER_INS;


-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of SIMPLE_FL_MARKER_INS is

   constant DATA_SIZE : integer := DATA_WIDTH/8;
   constant MARK_WORDS : integer := MARK_SIZE/DATA_SIZE;
   constant OFFSET_WORDS : integer := OFFSET/DATA_SIZE;

   -- simple state machine
   type state_t is (MARK_BEFORE, MARK_AFTER);

   signal curr_state : state_t;
   signal next_state : state_t;

   -- counter of position in the MARK in words
   signal cnt_mark_ce   : std_logic;
   signal cnt_mark_clr  : std_logic;
   -- need to count at least one after mark word
   signal cnt_mark      : std_logic_vector(log2(MARK_WORDS + 1) downto 0);

   -- counter to know which word was reached
   signal cnt_word_ce   : std_logic;
   signal cnt_word_clr  : std_logic;
   -- need to count at least to 1 after OFFSET word
   signal cnt_word      : std_logic_vector(log2(OFFSET_WORDS + 1) downto 0);

   -- counter to know which part was reached
   signal cnt_part_ce   : std_logic;
   signal cnt_part_clr  : std_logic;
   signal cnt_part      : std_logic_vector(max(0, log2(PARTS)-1) downto 0);

   -- multiplexors' possible select values
   type sel_t is (
      SEL_BEFORE_INIT,  -- state BEFORE_MARK, remember EOF, EOP, DATA and REM, pass MARK
      SEL_BEFORE_MARK,  -- state BEFORE_MARK, no read input, pass MARK
      SEL_BEFORE_END,   -- state BEFORE_MARK, no read input, pass stored values in INIT
      SEL_AFTER_INIT,   -- state BEFORE_MARK (!), remember EOF, EOP, pass DATA
      SEL_AFTER_MARK,   -- state AFTER_MARK, no read input, pass MARK
      SEL_AFTER_END,    -- state AFTER_MARK, no read input, pass MARK, pass stored EOF, EOP
      SEL_PASS          -- pass data without change
   );
   
   -- selector instance
   signal sel : sel_t;
   
   -- current piece of MARK
   signal mark_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mark_next_set : std_logic;
   -- is in MARK_PART
   signal is_markpart   : std_logic;
   -- is on the word that is to be marked
   signal is_markword   : std_logic;
   -- is anywhere before the word to be marked
   signal is_before_markword : std_logic;

   -- register to remember EOP, EOF, DATA and REM
   signal reg_fl_ce     : std_logic;
   signal reg_fl_eop_n  : std_logic;
   signal reg_fl_eof_n  : std_logic;
   signal reg_fl_data   : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_fl_rem    : std_logic_vector(log2(DATA_SIZE)-1 downto 0);

   signal out_eof_n     : std_logic;
   signal out_eop_n     : std_logic;

begin

   assert (MARK_SIZE mod DATA_SIZE) = 0 report "MARK_SIZE must be fold of DATA_WIDTH/8" severity failure;
   assert (OFFSET mod DATA_SIZE) = 0 report "OFFSET must be fold of DATA_WIDTH/8" severity failure;


-- ----------------------------------------------------------------------------
--             FSM that controls the multiplexors by sel signal
-- ----------------------------------------------------------------------------

   fsm_state : process(CLK, RST, next_state)
   begin
      if RST = '1' then
         curr_state <= MARK_BEFORE;

      elsif CLK'event and CLK = '1' then
         curr_state <= next_state;

      end if;
   end process;

   fsm_next : process(CLK, curr_state, cnt_word, cnt_mark, is_markpart, RX_SRC_RDY_N, TX_DST_RDY_N, RX_EOP_N, MARK_VALID, RX_REM)
   begin
      next_state <= curr_state;

      case curr_state is
         when MARK_BEFORE =>
            if OFFSET_WORDS > 0 then
               if cnt_word + 1 = OFFSET_WORDS and is_markpart = '1' and RX_REM = (log2(DATA_SIZE)-1 downto 0 => '1') and
                     RX_EOP_N = '0' and RX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' then
                  next_state <= MARK_AFTER;
               end if;
            end if;
      
         when MARK_AFTER =>
            if is_markpart = '1' and cnt_mark + 1 = MARK_WORDS and TX_DST_RDY_N = '0' and MARK_VALID = '1' then
               next_state <= MARK_BEFORE;
            end if;

      end case;
   end process;

   fsm_output : process(CLK, curr_state, cnt_word, cnt_mark, is_markpart, is_markword, TX_DST_RDY_N, RX_SRC_RDY_N, RX_EOP_N, RX_REM)
   begin
      sel <= SEL_PASS;

      case curr_state is
         when MARK_BEFORE =>
            if is_markword = '1' then -- => is in mark part
               if cnt_mark = 0 then
                  sel <= SEL_BEFORE_INIT;
               
               elsif cnt_mark > 0 and cnt_mark < MARK_WORDS then
                  sel <= SEL_BEFORE_MARK;
               
               else
                  sel <= SEL_BEFORE_END;
               
               end if;

            elsif is_markpart = '1' and OFFSET_WORDS > 0 then
               if cnt_word + 1 = OFFSET_WORDS and RX_EOP_N = '0' and RX_SRC_RDY_N = '0' and
                  RX_REM = (log2(DATA_SIZE)-1 downto 0 => '1') then
                  sel <= SEL_AFTER_INIT; -- next state is MARK_AFTER

               end if;
            end if;


         when MARK_AFTER =>
            if is_markword = '1' and cnt_mark + 1 < MARK_WORDS then
               sel <= SEL_AFTER_MARK;

            else
               sel <= SEL_AFTER_END;

            end if;

      end case;
   end process;


-- ----------------------------------------------------------------------------
--             Set of multiplexors controlled by sel signal
-- ----------------------------------------------------------------------------

   mark_next_set <= not(TX_DST_RDY_N) and MARK_VALID when sel = SEL_BEFORE_END else
                    not(TX_DST_RDY_N) and MARK_VALID when sel = SEL_AFTER_END else
                    is_markpart and is_before_markword and not(RX_SRC_RDY_N 
                        or TX_DST_RDY_N or RX_EOP_N) when sel = SEL_PASS else
                    '0';

   reg_fl_ce <= not(RX_SRC_RDY_N) when sel = SEL_BEFORE_INIT else
                not(RX_SRC_RDY_N) when sel = SEL_AFTER_INIT else
                '0';

   TX_SRC_RDY_N <= not(MARK_VALID) or RX_SRC_RDY_N 
                                    when sel = SEL_BEFORE_INIT else
                   not(MARK_VALID)  when sel = SEL_BEFORE_MARK else
                   '0'              when sel = SEL_BEFORE_END  else
                   RX_SRC_RDY_N     when sel = SEL_AFTER_INIT else
                   not(MARK_VALID)  when sel = SEL_AFTER_MARK else
                   not(MARK_VALID)  when sel = SEL_AFTER_END  else
                   not(MARK_VALID) or RX_SRC_RDY_N 
                                    when sel = SEL_PASS and mark_next_set = '1' else
                   RX_SRC_RDY_N;

   RX_DST_RDY_N <= not(MARK_VALID) or TX_DST_RDY_N
                                    when sel = SEL_BEFORE_INIT else
                   '1'              when sel = SEL_BEFORE_MARK else
                   '1'              when sel = SEL_BEFORE_END  else
                   TX_DST_RDY_N     when sel = SEL_AFTER_INIT else
                   '1'              when sel = SEL_AFTER_MARK else
                   '1'              when sel = SEL_AFTER_END  else
                   not(MARK_VALID) or TX_DST_RDY_N 
                                    when sel = SEL_PASS and mark_next_set = '1' else
                   TX_DST_RDY_N;


   TX_DATA <= mark_data    when sel = SEL_BEFORE_INIT else
              mark_data    when sel = SEL_BEFORE_MARK else
              reg_fl_data  when sel = SEL_BEFORE_END  else
              RX_DATA      when sel = SEL_AFTER_INIT else
              mark_data    when sel = SEL_AFTER_MARK else
              mark_data    when sel = SEL_AFTER_END  else
              RX_DATA;

   TX_REM <= (others => '1')  when sel = SEL_BEFORE_INIT else
             (others => '1')  when sel = SEL_BEFORE_MARK else
             reg_fl_rem       when sel = SEL_BEFORE_END  else
             RX_REM           when sel = SEL_AFTER_INIT else
             (others => '1')  when sel = SEL_AFTER_MARK else
             reg_fl_rem       when sel = SEL_AFTER_END  else
             RX_REM;

   TX_SOF_N <= RX_SOF_N    when sel = SEL_BEFORE_INIT else
               '1'         when sel = SEL_BEFORE_MARK else
               '1'         when sel = SEL_BEFORE_END  else
               RX_SOF_N    when sel = SEL_AFTER_INIT else
               '1'         when sel = SEL_AFTER_MARK else
               '1'         when sel = SEL_AFTER_END  else
               RX_SOF_N;

   TX_SOP_N <= RX_SOP_N    when sel = SEL_BEFORE_INIT else
               '1'         when sel = SEL_BEFORE_MARK else
               '1'         when sel = SEL_BEFORE_END  else
               RX_SOP_N    when sel = SEL_AFTER_INIT else
               '1'         when sel = SEL_AFTER_MARK else
               '1'         when sel = SEL_AFTER_END  else
               RX_SOP_N;

   out_eof_n <= '1'           when sel = SEL_BEFORE_INIT else
                '1'           when sel = SEL_BEFORE_MARK else
                reg_fl_eof_n  when sel = SEL_BEFORE_END  else
                '1'           when sel = SEL_AFTER_INIT else
                '1'           when sel = SEL_AFTER_MARK else
                reg_fl_eof_n  when sel = SEL_AFTER_END  else
                RX_EOF_N;

   out_eop_n <= '1'           when sel = SEL_BEFORE_INIT else
                '1'           when sel = SEL_BEFORE_MARK else
                reg_fl_eop_n  when sel = SEL_BEFORE_END else
                '1'           when sel = SEL_AFTER_INIT else
                '1'           when sel = SEL_AFTER_MARK else
                reg_fl_eop_n  when sel = SEL_AFTER_END  else
                RX_EOP_N;

   cnt_part_ce <= not(RX_EOP_N or RX_SRC_RDY_N or TX_DST_RDY_N) 
                              when sel = SEL_PASS and mark_next_set = '0' else
                  not(RX_EOP_N or RX_SRC_RDY_N or TX_DST_RDY_N) and MARK_VALID 
                              when sel = SEL_PASS else
                  not(out_eop_n or TX_DST_RDY_N) 
                              when sel = SEL_BEFORE_END else
                  MARK_VALID and not(TX_DST_RDY_N) 
                              when sel = SEL_AFTER_END else
                  '0';

   cnt_part_clr <= '0'     when sel = SEL_BEFORE_INIT else
                   '0'     when sel = SEL_BEFORE_MARK else
                   MARK_VALID and not(TX_DST_RDY_N or out_eof_n) 
                           when sel = SEL_BEFORE_END else
                   MARK_VALID and not(TX_DST_RDY_N or out_eof_n) 
                           when sel = SEL_AFTER_END else
                   not(out_eof_n or TX_DST_RDY_N or RX_SRC_RDY_N) 
                           when sel = SEL_PASS and mark_next_set = '0' else
                   not(out_eof_n or TX_DST_RDY_N or RX_SRC_RDY_N) and MARK_VALID 
                           when sel = SEL_PASS else
                   '0';

   cnt_word_ce <= '0'      when sel = SEL_BEFORE_INIT else
                  '0'      when sel = SEL_BEFORE_MARK else
                  not(TX_DST_RDY_N) and MARK_VALID 
                           when sel = SEL_BEFORE_END  else
                  not(RX_SRC_RDY_N or TX_DST_RDY_N) 
                           when sel = SEL_AFTER_INIT else
                  '0'      when sel = SEL_AFTER_MARK else
                  MARK_VALID and not(TX_DST_RDY_N) 
                           when sel = SEL_AFTER_END else
                  is_markpart and not(RX_SRC_RDY_N or TX_DST_RDY_N) 
                           when sel = SEL_PASS and mark_next_set = '0' else
                  is_markpart and not(RX_SRC_RDY_N or TX_DST_RDY_N) and MARK_VALID 
                           when sel = SEL_PASS else
                  '0';

   cnt_word_clr <= '0'     when sel = SEL_BEFORE_INIT else
                   '0'     when sel = SEL_BEFORE_MARK else
                   not(out_eop_n or TX_DST_RDY_N) and MARK_VALID 
                           when sel = SEL_BEFORE_END else
                   MARK_VALID and not(TX_DST_RDY_N) 
                           when sel = SEL_AFTER_END else
                   not(out_eop_n or TX_DST_RDY_N or RX_SRC_RDY_N) 
                           when sel = SEL_PASS and mark_next_set = '0' else
                   not(out_eop_n or TX_DST_RDY_N or RX_SRC_RDY_N) and MARK_VALID 
                           when sel = SEL_PASS else
                   '0';

   cnt_mark_ce <= MARK_VALID and not(TX_DST_RDY_N or RX_SRC_RDY_N) 
                           when sel = SEL_BEFORE_INIT else
                  MARK_VALID and not(TX_DST_RDY_N) 
                           when sel = SEL_BEFORE_MARK else
                  '1'      when sel = SEL_BEFORE_END else
                  MARK_VALID and not(TX_DST_RDY_N) 
                           when sel = SEL_AFTER_MARK else
                  '0';
  
   cnt_mark_clr <= '0'     when sel = SEL_BEFORE_INIT else
                   '0'     when sel = SEL_BEFORE_MARK else
                   not(out_eop_n or TX_DST_RDY_N) and MARK_VALID 
                           when sel = SEL_BEFORE_END else
                   MARK_VALID and not(TX_DST_RDY_N) 
                           when sel = SEL_AFTER_END else
                   not(out_eof_n or TX_DST_RDY_N or RX_SRC_RDY_N) 
                           when sel = SEL_PASS and mark_next_set = '0' else
                   not(out_eof_n or TX_DST_RDY_N or RX_SRC_RDY_N) and MARK_VALID 
                           when sel = SEL_PASS else
                   '0';


-- ----------------------------------------------------------------------------
--                 Simple comparators and connections
-- ----------------------------------------------------------------------------

   is_markpart <= '1' when cnt_part = MARK_PART else
                  '0';
   is_markword <= is_markpart when cnt_word = OFFSET_WORDS else
                  '0';
   is_before_markword <= is_markpart when cnt_word < OFFSET_WORDS else
                        '0';

   MARK_NEXT <= mark_next_set;
   TX_EOF_N <= out_eof_n;
   TX_EOP_N <= out_eop_n;


-- ----------------------------------------------------------------------------
--                 Generic multiplexor for MARK passing
-- ----------------------------------------------------------------------------

   gen_mux: if MARK_WORDS > 1 generate -- generates multiplexor
      mark_mux :  entity work.GEN_MUX
      generic map (
         DATA_WIDTH => DATA_WIDTH,
         MUX_WIDTH => MARK_WORDS
      )
      port map (
         DATA_IN => MARK,
         SEL => cnt_mark(log2(MARK_WORDS)-1 downto 0),
         DATA_OUT => mark_data
      );
   end generate;
   
   gen_wire: if MARK_WORDS = 1 generate -- generates only simple wire
      mark_data <= MARK;
   end generate;


-- ----------------------------------------------------------------------------
--          FL register implementation, stores EOF, EOP, DATA, REM
-- ----------------------------------------------------------------------------

   register_fl : process(CLK, reg_fl_ce, RX_EOF_N, RX_EOP_N, RX_DATA, RX_REM)
   begin
      if CLK'event and CLK = '1' then
         if reg_fl_ce = '1' then
            reg_fl_data <= RX_DATA;
            reg_fl_rem <= RX_REM;
            reg_fl_eof_n <= RX_EOF_N;
            reg_fl_eop_n <= RX_EOP_N;
         end if;
      end if;
   end process;


-- ----------------------------------------------------------------------------
--                               Counters
-- ----------------------------------------------------------------------------

   counter_part : process(CLK, RST, cnt_part_ce, cnt_part_clr, cnt_part)
   begin
      if CLK'event and CLK = '1' then
         if cnt_part_clr = '1' or RST = '1' then
            cnt_part <= (others => '0');

         elsif cnt_part_ce = '1' then
            cnt_part <= cnt_part + 1;

         end if;
      end if;
   end process;

   counter_word : process(CLK, RST, cnt_word_ce, cnt_word_clr, cnt_word)
   begin
      if CLK'event and CLK = '1' then
         if cnt_word_clr = '1' or RST = '1' then
            cnt_word <= (others => '0');

         elsif cnt_word_ce = '1' and cnt_word < OFFSET_WORDS + 1 then
            cnt_word <= cnt_word + 1;

         end if;
      end if;
   end process;

   counter_mark : process(CLK, RST, cnt_mark_ce, cnt_mark_clr, cnt_mark)
   begin
      if CLK'event and CLK = '1' then
         if cnt_mark_clr = '1' or RST = '1' then
            cnt_mark <= (others => '0');

         elsif cnt_mark_ce = '1' and cnt_mark < MARK_WORDS then
            cnt_mark <= cnt_mark + 1;

         end if;
      end if;
   end process;

end architecture; 
