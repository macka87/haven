-- fsm_main.vhd: FrameLink cutter: FSM Main
-- (extract and optionally remove data on defined offset in defined frame part)
-- Copyright (C) 2008 CESNET
-- Author(s): Bronislav Pribyl <xpriby12@stud.fit.vutbr.cz>
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
use work.math_pack.all;
use work.cutter_types.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fsm_main is

   -- ============================== TYPES =====================================

   type t_fsm_main     is (sm_idle, sm_inactive_part, sm_active_before,
                           sm_active_start, sm_active_progress, sm_active_end,
                           sm_active_after);


   -- ============================== SIGNALS ===================================
   
   -- FSM signals
   signal main_c_state             : t_fsm_main;
   signal main_n_state             : t_fsm_main;
   signal main_last_transmit_state : t_fsm_main;
   
   -- tx_sop signals
   signal generated_tx_sop_n_before       : std_logic;
   signal generated_tx_sop_n_end_start    : std_logic;
   signal generated_tx_sop_n_end_progress : std_logic;
   signal generated_tx_sop_n_after        : std_logic;
   
   -- tx_eop signals
   signal generated_tx_eop_n_idle_end   : std_logic;
   signal generated_tx_eop_n_idle_after : std_logic;
   signal generated_tx_eop_n_end        : std_logic;
   signal generated_tx_eop_n_after      : std_logic;
   
   -- tx_src_rdy signals
   signal generated_tx_src_rdy_n_before_inactive : std_logic;
   signal generated_tx_src_rdy_n_before_before   : std_logic;
   signal generated_tx_src_rdy_n_end             : std_logic;
   
   -- tx_rem signals
   signal generated_tx_rem_src      : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal rx_rem_modified_inc       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal rx_rem_modified_inc_start : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal rx_rem_modified_inc_end   : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal rx_rem_modified_inc_en    : std_logic;
   signal rx_rem_modified           : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg_rx_rem_modified       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   
   -- output counter
   signal cnt_output_en_end : std_logic;
   
   -- output register enable
   signal I_TX_DATA_en_end  : std_logic;
   
   -- auxiliary signals
   signal ready             : std_logic;
   signal ready_src         : std_logic;
   signal reg_ready         : std_logic;


begin

   -- current state register
   Main_fsm_current_state: process(CLK, RESET)
   begin
      if (RESET = '1') then
         main_c_state <= sm_idle;
      elsif (CLK'event and CLK = '1') then
         main_c_state <= main_n_state;
      end if;
   end process;
   
   -- last transmit state register
   Main_fsm_last_transmit_state: process(CLK, RESET)
   begin
      if (RESET = '1') then
         main_last_transmit_state <= sm_idle;
      elsif (CLK'event and CLK = '1') then
         if (main_n_state /= sm_idle) then
            main_last_transmit_state <= main_n_state;
         end if;
      end if;
   end process;


   -- next state logic
   Main_fsm_next_state:
   process(main_c_state, TRANSMIT_PROGRESS, PART_NUM, WORD_NUM, REG_RX_EOP)
   begin
      main_n_state <= sm_idle;

      case main_c_state is

         -- idle
         when sm_idle =>
            if (TRANSMIT_PROGRESS = '0') then
               main_n_state <= sm_idle;
            else
               if (PART_NUM /= PART) then
                  main_n_state <= sm_inactive_part;
               elsif (WORD_NUM  > END_WORD) then
                  main_n_state <= sm_active_after;
               elsif (WORD_NUM = END_WORD) then
                  main_n_state <= sm_active_end;
               elsif (WORD_NUM > START_WORD and WORD_NUM < END_WORD) then
                  main_n_state <= sm_active_progress;
               elsif (WORD_NUM = START_WORD) then
                  main_n_state <= sm_active_start;
               elsif (WORD_NUM < START_WORD) then
                  main_n_state <= sm_active_before;
               else
                  main_n_state <= sm_idle;
               end if;
            end if;

         -- inactive part
         when sm_inactive_part =>
            if (TRANSMIT_PROGRESS = '0') then
               main_n_state <= sm_idle;
            else
               if (PART_NUM = PART) then
                  if (WORD_NUM = END_WORD) then
                     main_n_state <= sm_active_end;
                  elsif (WORD_NUM = START_WORD) then
                     main_n_state <= sm_active_start;
                  elsif (WORD_NUM < START_WORD) then
                     main_n_state <= sm_active_before;
                  else
                     main_n_state <= sm_inactive_part;
                  end if;
               else
                  main_n_state <= sm_inactive_part;
               end if;
            end if;

         -- active before
         when sm_active_before =>
            if (TRANSMIT_PROGRESS = '0') then
               main_n_state <= sm_idle;
            else
               if (PART_NUM /= PART) then
                  main_n_state <= sm_inactive_part;
               elsif (WORD_NUM = END_WORD) then
                  main_n_state <= sm_active_end;
               elsif (WORD_NUM = START_WORD) then
                  main_n_state <= sm_active_start;
               else
                  main_n_state <= sm_active_before;
               end if;
            end if;

         -- active start
         when sm_active_start =>
            if (TRANSMIT_PROGRESS = '0') then
               main_n_state <= sm_idle;
            else
               if (PART_NUM /= PART) then
                  main_n_state <= sm_inactive_part;
               elsif (WORD_NUM = END_WORD) then
                  main_n_state <= sm_active_end;
               elsif (WORD_NUM > START_WORD) then
                  main_n_state <= sm_active_progress;
               else
                  main_n_state <= sm_active_start;
               end if;
            end if;

         -- active progress
         when sm_active_progress =>
            if (TRANSMIT_PROGRESS = '0') then
               main_n_state <= sm_idle;
            else
               if (PART_NUM /= PART) then
                  main_n_state <= sm_inactive_part;
               elsif (WORD_NUM = END_WORD or REG_RX_EOP = '1') then
                  main_n_state <= sm_active_end;
               else
                  main_n_state <= sm_active_progress;
               end if;
            end if;

         -- active end
         when sm_active_end =>
            if (TRANSMIT_PROGRESS = '0') then
               main_n_state <= sm_idle;
            else
               if (PART_NUM /= PART) then
                  main_n_state <= sm_inactive_part;
               elsif (WORD_NUM > END_WORD) then
                  main_n_state <= sm_active_after;
               else
                  main_n_state <= sm_active_end;
               end if;
            end if;

         -- active after
         when sm_active_after =>
            if (TRANSMIT_PROGRESS = '0') then
               main_n_state <= sm_idle;
            else
               if (PART_NUM /= PART) then
                  main_n_state <= sm_inactive_part;
               else
                  main_n_state <= sm_active_after;
               end if;
            end if;

         -- undefined
         when others =>

      end case;
   end process;


   -- === output logic auxiliary signals =======================================
   
   -- CNT_OUTPUT_EN -----------------------------------------------------------
   Cnt_output_en_end_1:
   if ((START_BYTE - END_BYTE) > 0) generate
      cnt_output_en_end <= '1';
   end generate;
   Cnt_output_en_end_0:
   if ((START_BYTE - END_BYTE) <= 0) generate
      cnt_output_en_end <= '0';
   end generate;
   
   -- tx_src_rdy_n -----------------------------------------------------------
   Tx_src_rdy_n_before_inactive_1:
   if (START_BYTE = 0 and END_BYTE = DATA_BYTES - 1) generate
      generated_tx_src_rdy_n_before_inactive <= REG_RX_EOP;
   end generate;
   Tx_src_rdy_n_before_inactive_2:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES - 1) and START_WORD = 0) generate
      generated_tx_src_rdy_n_before_inactive <= '0';
   end generate;
   Tx_src_rdy_n_before_inactive_3:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES - 1) and START_WORD /= 0 and START_BYTE = END_BYTE) generate
      generated_tx_src_rdy_n_before_inactive <= '0';
   end generate;
   Tx_src_rdy_n_before_inactive_4:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES - 1) and START_WORD /= 0 and START_BYTE /= END_BYTE) generate
      generated_tx_src_rdy_n_before_inactive <= '1';
   end generate;
   
   Tx_src_rdy_n_before_before_1:
   if (START_BYTE = 0 and END_BYTE = DATA_BYTES - 1) generate
      generated_tx_src_rdy_n_before_before <= REG_RX_EOP;
   end generate;
   Tx_src_rdy_n_before_before_2:
   if (START_BYTE /= 0 or END_BYTE /= DATA_BYTES - 1) generate
      generated_tx_src_rdy_n_before_before <= '1';--kvuli 11/2... drive I_RX_EOP or REG_RX_EOP;
   end generate;
   
   Tx_src_rdy_n_end_1a:
   if (START_BYTE = 0 and END_BYTE = DATA_BYTES - 1 and START_WORD = 0) generate
      generated_tx_src_rdy_n_end <= '0';--I_RX_EOP or REG_RX_EOP;--REG_RX_EOP;
   end generate;
   Tx_src_rdy_n_end_1b:
   if (START_BYTE = 0 and END_BYTE = DATA_BYTES - 1 and START_WORD /= 0) generate
      generated_tx_src_rdy_n_end <= '1';
   end generate;
   Tx_src_rdy_n_end_2a:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES- 1) and (START_BYTE - END_BYTE) > 0) generate
      generated_tx_src_rdy_n_end <= '1';
   end generate;
   Tx_src_rdy_n_end_2b:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES- 1) and (START_BYTE - END_BYTE) <= 0) generate
      generated_tx_src_rdy_n_end <= REG_RX_EOP;
   end generate;
   
   -- GENERATED_TX_SOP -------------------------------------------------------
   Generated_tx_sop_n_before_1:
   if (START_BYTE = 0 and END_BYTE = DATA_BYTES-1) generate
      generated_tx_sop_n_before <= '0';
   end generate;
   Generated_tx_sop_n_before_2:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1) and START_WORD = 0) generate
      generated_tx_sop_n_before <= REG_RX_SOP;
   end generate;
   Generated_tx_sop_n_before_3:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1) and START_WORD /= 0 and START_BYTE = END_BYTE) generate
      generated_tx_sop_n_before <= '0';
   end generate;
   Generated_tx_sop_n_before_4:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1) and START_WORD /= 0 and START_BYTE /= END_BYTE) generate
      generated_tx_sop_n_before <= '0';--kvuli 11/2, 11/3, 11/4... driv '1';
   end generate;
   
   Generated_tx_sop_n_end_start_1:
   if ((START_BYTE = 0 and END_BYTE = DATA_BYTES-1) and START_WORD /= 1) generate
      generated_tx_sop_n_end_start <= '0';
   end generate;
   Generated_tx_sop_n_end_start_2:
   if ((START_BYTE = 0 and END_BYTE = DATA_BYTES-1) and START_WORD = 1) generate
      generated_tx_sop_n_end_start <= '1';
   end generate;
   Generated_tx_sop_n_end_start_3:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1) and (START_BYTE - END_BYTE) > 0) generate
      generated_tx_sop_n_end_start <= REG2_RX_SOP_LV;
   end generate;
   Generated_tx_sop_n_end_start_4:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1) and (START_BYTE - END_BYTE) <= 0) generate
      generated_tx_sop_n_end_start <= REG_RX_EOP;
   end generate;
   
   Generated_tx_sop_n_end_progress_1:
   if ((START_BYTE = 0 and END_BYTE = DATA_BYTES-1) and START_WORD = 0) generate
      generated_tx_sop_n_end_progress <= '0';
   end generate;
   Generated_tx_sop_n_end_progress_2:
   if ((START_BYTE = 0 and END_BYTE = DATA_BYTES-1) and START_WORD /= 0) generate
      generated_tx_sop_n_end_progress <= '1';
   end generate;
   Generated_tx_sop_n_end_progress_3:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1) and START_WORD < 2) generate
      generated_tx_sop_n_end_progress <= '1';
   end generate;
   Generated_tx_sop_n_end_progress_4:
   if ((START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1) and START_WORD >= 2) generate
      generated_tx_sop_n_end_progress <= '0';
   end generate;


   Generated_tx_sop_n_after_0:
   if (START_WORD = 0 and START_BYTE <= END_BYTE) generate
      generated_tx_sop_n_after <= '1';
   end generate;
   Generated_tx_sop_n_after_1:
   if ((START_WORD /= 0 or START_BYTE > END_BYTE) and ((START_BYTE - END_BYTE) < 1 and (START_BYTE /= 0 or END_BYTE /= DATA_BYTES-1))) generate
      generated_tx_sop_n_after <= not I_RX_EOP and not REG_RX_EOP;--'1';
   end generate;
   Generated_tx_sop_n_after_2:
   if ((START_WORD /= 0 or START_BYTE > END_BYTE) and ((START_BYTE - END_BYTE >= 1) or (START_BYTE = 0 and END_BYTE = DATA_BYTES-1))) generate
      generated_tx_sop_n_after <= REG2_RX_SOP_LV;--'0';
   end generate;
   
   -- GENERATED_TX_EOP -------------------------------------------------------
   Generated_tx_eop_n_idle_end_1:
   if (not RX_WAIT_NEED) generate
      generated_tx_eop_n_idle_end <= '0';
   end generate;
   Generated_tx_eop_n_idle_end_2:
   if (RX_WAIT_NEED) generate
      generated_tx_eop_n_idle_end <= '1';
   end generate;
   
   Generated_tx_eop_n_idle_after_1:
   if (not RX_WAIT_NEED) generate
      generated_tx_eop_n_idle_after <= REG_RX_EOP;
   end generate;
   Generated_tx_eop_n_idle_after_2:
   if (RX_WAIT_NEED) generate
      generated_tx_eop_n_idle_after <= '1';
   end generate;
   
   Generated_tx_eop_n_end_1:
   if (not RX_WAIT_NEED) generate
      generated_tx_eop_n_end <= REG_RX_EOP;
   end generate;
   Generated_tx_eop_n_end_2:
   if (RX_WAIT_NEED) generate
      generated_tx_eop_n_end <= '0';
   end generate;
   
   Generated_tx_eop_n_after_1:
   if (not RX_WAIT_NEED) generate
      generated_tx_eop_n_after <= REG_RX_EOP;
   end generate;
   Generated_tx_eop_n_after_2:
   if (RX_WAIT_NEED) generate
      generated_tx_eop_n_after <= REG2_RX_EOP;
   end generate;
   
   -- I_TX_DATA_EN -----------------------------------------------------------
   I_tx_data_en_end_1:
   if ((START_BYTE - END_BYTE) > 0) generate
      I_TX_DATA_en_end <= '1';
   end generate;
   I_tx_data_en_end_other:
   if ((START_BYTE - END_BYTE) <= 0) generate
      I_TX_DATA_en_end <= REG_RX_EOP;
   end generate;
   
   -- ready_src ----------------------------------------------------------------
   Ready_src_1:
   if (not RX_WAIT_NEED) generate
      ready_src <= '1';
   end generate;
   Ready_src_0:
   if (RX_WAIT_NEED) generate
      ready_src <= '0';
   end generate;
   
   -- rx_rem_modified_inc ------------------------------------------------------
   rx_rem_modified_inc_start <= conv_std_logic_vector(START_BYTE,rx_rem_modified_inc'length);
   
   Rx_rem_modified_inc_end_one_word:
   if (START_WORD = END_WORD) generate
      rx_rem_modified_inc_end <= conv_std_logic_vector(DATA_BYTES - 1 - END_BYTE + START_BYTE, rx_rem_modified_inc_end'length);
   end generate;
   Rx_rem_modified_inc_end_more_words:
   if (START_WORD /= END_WORD) generate
      rx_rem_modified_inc_end <= REG_RX_REM;
   end generate;

   -- rx_rem_modified ----------------------------------------------------------
   process(rx_rem_modified_inc_en, reg_rx_rem_modified, rx_rem_modified_inc)
   begin
      if (rx_rem_modified_inc_en = '1') then
         rx_rem_modified <= reg_rx_rem_modified + rx_rem_modified_inc;
      else
         rx_rem_modified <= reg_rx_rem_modified;
      end if;
   end process;
   
   process(CLK, RESET)
   begin
      if (RESET = '1') then -- asynchronous reset
         reg_rx_rem_modified <= (others => '1');
      elsif (CLK'event and CLK = '1') then
         if (REG_RX_EOP = '1') then -- synchronous reset
            reg_rx_rem_modified <= (others => '1');
         else
            reg_rx_rem_modified <= rx_rem_modified;
         end if;
      end if;
   end process;
   
   -- generated_tx_rem_src -----------------------------------------------------
   Generated_tx_rem_src_no_wait_need:
   if (not RX_WAIT_NEED) generate
      generated_tx_rem_src <= REG_RX_REM;
   end generate;
   Generated_tx_rem_src_wait_need:
   if (RX_WAIT_NEED) generate
      generated_tx_rem_src <= rx_rem_modified;
   end generate;
   
   -- ==========================================================================


   -- output logic
   Main_fsm_output: process(
      main_c_state, main_n_state, main_last_transmit_state,
      REG_RX_SOF, REG_RX_SOP, REG_RX_EOP, REG_RX_EOF, REG_RX_SRC_RDY, REG_RX_REM,
      WORD_NUM, I_RX_EOP,
      ready_src, cnt_output_en_end, rx_rem_modified, I_TX_DATA_en_end,
      generated_tx_src_rdy_n_before_inactive, generated_tx_src_rdy_n_before_before, generated_tx_src_rdy_n_end,
      generated_tx_rem_src,
      generated_tx_sop_n_before, generated_tx_sop_n_end_start, generated_tx_sop_n_end_progress, generated_tx_sop_n_after,
      generated_tx_eop_n_idle_end, generated_tx_eop_n_idle_after, generated_tx_eop_n_end, generated_tx_eop_n_after
   )
   begin
      CUT_EXTRACTED       <= '0';
      SEL_REORDER_END        <= '0';
      SEL_REORDER            <= '0';
      CNT_AUX_EN             <= '0';
      SEL_AUX0_EN            <= en_no_reorder;
      SEL_AUX1_EN            <= en_no_reorder;
      CNT_OUTPUT_EN          <= '0';
      I_TX_DATA_EN           <= '1';
      ready                  <= '1';
      CUT_PROGRESS                <= '0';
      rx_rem_modified_inc    <= (others => '-');
      rx_rem_modified_inc_en <= '0';
      GENERATED_TX_SRC_RDY <= REG_RX_SRC_RDY;
      GENERATED_TX_SOF     <= REG_RX_SOF;
      GENERATED_TX_SOP     <= REG_RX_SOP;
      GENERATED_TX_EOP     <= REG_RX_EOP;
      GENERATED_TX_EOF     <= REG_RX_EOF;
      GENERATED_TX_REM       <= REG_RX_REM;

      case main_n_state is

         -- idle
         when sm_idle =>
            if (reg_ready = '0') then
               SEL_AUX0_EN <= en_after;
               SEL_AUX1_EN <= en_after;
            end if;
--             if (main_last_transmit_state = sm_active_end or main_last_transmit_state = sm_active_after) then--kvuli 11/2... driv if (main_last_transmit_state = sm_active_after) then
--                GENERATED_TX_EOP <= 'Z';--generated_tx_eop_n_idle;
--             end if;
            
            if (main_c_state = sm_active_end) then
               GENERATED_TX_EOP <= generated_tx_eop_n_idle_end;
            elsif (main_c_state = sm_active_after) then
               GENERATED_TX_EOP <= generated_tx_eop_n_idle_after;
            else
               GENERATED_TX_EOP <= '0';
            end if;
-- TODO            ... na hovno ... pokusit se to generovat na základě generiků (OFFSET a SIZE, START_BYTE, atd.)

         -- inactive part
         when sm_inactive_part =>
            if (main_c_state = sm_active_after) then
               GENERATED_TX_REM <= generated_tx_rem_src;
            end if;
            
         -- active before
         when sm_active_before =>
            -- in this beat there is last guaranteed valid word;
            -- therefore we must store it until EOP or next valid word
            if (WORD_NUM = START_WORD - 1) then--(I_RX_EOP = '1') then
               if (main_last_transmit_state = sm_inactive_part) then
                  GENERATED_TX_SRC_RDY <= generated_tx_src_rdy_n_before_inactive;
               elsif (main_last_transmit_state = sm_active_before) then
                  GENERATED_TX_SRC_RDY <= generated_tx_src_rdy_n_before_before;
               end if;
            end if;
            
            if (WORD_NUM = (START_WORD - 1)) then
               GENERATED_TX_SOP <= generated_tx_sop_n_before;
            end if;

         -- active start
         when sm_active_start =>
            -- EOP: CUT_VLD only if minimum 1 extracted byte is confirmed by REM
            -- no EOP: not CUT_VLD
            if (REG_RX_EOP = '1' and REG_RX_REM >= conv_std_logic_vector(START_BYTE, REG_RX_REM'length)) then
               CUT_EXTRACTED       <= '1';
            else
               CUT_EXTRACTED       <= '0';
            end if;
            CUT_PROGRESS                <= '1';
            SEL_AUX0_EN            <= en_start;
            SEL_AUX1_EN            <= en_start;
            rx_rem_modified_inc    <= rx_rem_modified_inc_start;
             rx_rem_modified_inc_en <= '1';
            GENERATED_TX_SRC_RDY <= REG_RX_EOP;
            GENERATED_TX_SOP     <= '0';
            GENERATED_TX_REM       <= conv_std_logic_vector(START_BYTE - 1, GENERATED_TX_REM'length);--TODO

         -- active progress
         when sm_active_progress =>
            -- if EOP, set CUT_VLD even though all data hasn't been extracted
            CUT_EXTRACTED       <= REG_RX_EOP;
            CUT_PROGRESS                <= '1';
            SEL_REORDER            <= '1';
            SEL_AUX0_EN            <= en_progress;
            SEL_AUX1_EN            <= en_progress;
            I_TX_DATA_EN           <= '0';
            GENERATED_TX_SRC_RDY <= REG_RX_EOP;
            GENERATED_TX_REM       <= conv_std_logic_vector(START_BYTE - 1, GENERATED_TX_REM'length);--TODO: sjednotit s active_start

         -- active end
         when sm_active_end =>
            -- EOP: CUT_VLD only if minimum 1 extracted byte is confirmed by REM
            -- no EOP: CUT_VLD
            if (REG_RX_EOP = '1' and REG_RX_REM < conv_std_logic_vector(START_BYTE, REG_RX_REM'length)) then
               CUT_EXTRACTED  <= '0';
            else
               CUT_EXTRACTED <= '1';
            end if;
            CUT_PROGRESS           <= '1';
            SEL_REORDER_END   <= '1';
            SEL_REORDER       <= '1';
            CNT_AUX_EN        <= '1';
            SEL_AUX0_EN       <= en_end;
            SEL_AUX1_EN       <= en_end;
            CNT_OUTPUT_EN     <= cnt_output_en_end;
            
            if (REG_RX_EOP = '1') then
               ready <= ready_src;
            end if;
            
            if (WORD_NUM = END_WORD) then
               I_TX_DATA_EN           <= I_TX_DATA_en_end;
               rx_rem_modified_inc_en <= '1';
            else
               I_TX_DATA_EN           <= '0';
               rx_rem_modified_inc_en <= '0';
            end if;
            rx_rem_modified_inc    <= rx_rem_modified_inc_end;

            if (main_last_transmit_state = sm_active_before) then
               GENERATED_TX_SRC_RDY <= '1';
            else
               GENERATED_TX_SRC_RDY <= generated_tx_src_rdy_n_end;
            end if;

            if (main_last_transmit_state = sm_inactive_part) then
               GENERATED_TX_SOP <= REG_RX_EOP;
            elsif (main_last_transmit_state = sm_active_before) then
               GENERATED_TX_SOP <= not I_RX_EOP and not REG_RX_EOP;--'0';
            elsif (main_last_transmit_state = sm_active_start)   then
               GENERATED_TX_SOP <= generated_tx_sop_n_end_start;
            elsif (main_last_transmit_state = sm_active_progress) then
               GENERATED_TX_SOP <= generated_tx_sop_n_end_progress;
            end if;
            
            GENERATED_TX_EOP <= generated_tx_eop_n_end;--kvuli 11/2
            
            GENERATED_TX_REM <= rx_rem_modified;--TODO

         -- active after
         when sm_active_after =>
            CUT_EXTRACTED          <= '1';
            SEL_REORDER            <= '1';
            CNT_AUX_EN             <= '1';
            SEL_AUX0_EN            <= en_after;
            SEL_AUX1_EN            <= en_after;
            CNT_OUTPUT_EN          <= '1';
            if (REG_RX_EOP = '1') then
               ready <= ready_src;
            end if;
-- nefunguje pri 0/1 ... zkusit dodelat az po tx_eop_n --erase
            rx_rem_modified_inc_en <= REG_RX_EOP;
            rx_rem_modified_inc    <= REG_RX_REM + '1';
            GENERATED_TX_REM       <= rx_rem_modified;--TODO
            if (main_last_transmit_state = sm_active_end) then
               GENERATED_TX_SOP <= generated_tx_sop_n_after;
            end if;
            GENERATED_TX_EOP <= generated_tx_eop_n_after;

         -- undefined
         when others =>

      end case;
   end process;
   
   
   -- registering ready signal
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         reg_ready <= ready;
      end if;
   end process;
   
   RX_READY <= ready;

end architecture full;
