-- fl_cutter.vhd: architecture of fl_cutter component
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03 at stud.fit.vutbr.cz>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of fl_cutter is
   -- -------------------------------------------------------------------------
   -- CONSTANTS DECLARATION
   -- -------------------------------------------------------------------------
   constant bperw          : integer := DATA_WIDTH/8; -- bytes per word
   constant first_ext_word : integer := EXT_OFFSET/bperw; -- index of first word for extraction
   constant num_of_words   : integer := (EXT_OFFSET+EXT_SIZE-1)/bperw - first_ext_word + 1; -- number of words, needed for extraction
   
   -- -------------------------------------------------------------------------
   -- SIGNALS DECLARATION
   -- -------------------------------------------------------------------------
   type t_state is (IDLE, EXTRACTION, EXTRACT_REMOVE, EXTRACT_AFTER_REMOVE,
                    VLD_EXT, ERROR_EXT, AFTER_EXT);
   signal present_state, next_state : t_state;
   
   signal ext_data         : std_logic_vector(num_of_words*DATA_WIDTH - 1 downto 0);
   signal ext_addr_index   : std_logic_vector(log2(num_of_words+1) - 1 downto 0); -- select whereto write current data into ext_data_reg
   signal ext_en	   : std_logic; -- enables counter ext_addr_cnt and write into extracted data register
   signal cut_en           : std_logic; -- set if current word is cutted => eop_n/eof_n signals have to be moved forward

   signal data             : std_logic_vector(DATA_WIDTH - 1 downto 0); -- current recieved word of data
   signal send_data        : std_logic_vector(DATA_WIDTH - 1 downto 0); -- current recieved word of data which will be send out
   signal data_rem         : std_logic_vector(log2(bperw) - 1 downto 0);
   signal send_data_rem    : std_logic_vector(log2(bperw) - 1 downto 0);
   signal rem_mux_out      : std_logic_vector(log2(bperw) - 1 downto 0);

   signal send_rx_data_vld : std_logic;
   signal pre_rx_data_vld  : std_logic;
   signal rx_data_vld      : std_logic;
   signal dst_rdy_n        : std_logic;
   signal src_rdy_n        : std_logic;
   
   signal part_num         : std_logic_vector(log2(PART+2) - 1 downto 0);   
   signal word_num         : std_logic_vector(log2(EXT_OFFSET/bperw+2) - 1 downto 0);
   signal cut_word_num     : std_logic_vector(log2(CUT_OFFSET+2) - 1 downto 0);

   signal sof_n            : std_logic;
   signal sop_n            : std_logic;      
   signal eop_n            : std_logic;
   signal eof_n            : std_logic;
   signal send_sop_n       : std_logic;
   signal send_sof_n       : std_logic;
   signal send_eop_n       : std_logic;
   signal send_eof_n       : std_logic;
   signal fsm_sof_n        : std_logic;
   signal fsm_eop_n        : std_logic;
   signal fsm_eof_n        : std_logic;

   signal pipe_cut_en      : std_logic;

   signal transmission     : std_logic;                -- indicates if transmission is possible (but may not be in progress)
   signal tx_trans         : std_logic;                -- indicates if transmission in tx direction is possible
   signal rx_trans         : std_logic;                -- indicates if transmission in rx direction is possible, enables counters

   signal pre_tx_eop_n     : std_logic;
   signal pre_tx_eof_n     : std_logic;

   attribute keep : string;
   attribute keep of pipe_cut_en: signal is "true";
begin

-- directly connected signals:
TX_DATA  <= send_data;
TX_REM   <= send_data_rem;
TX_SRC_RDY_N <= src_rdy_n;
TX_EOP_N <= pre_tx_eop_n;
TX_EOF_N <= pre_tx_eof_n;
TX_SOP_N <= send_sop_n;
TX_SOF_N <= send_sof_n;

src_rdy_n <= not (send_rx_data_vld and (rx_data_vld or not pre_tx_eof_n));

tx_trans <= TX_DST_RDY_N nor src_rdy_n;
rx_trans <= RX_SRC_RDY_N nor (dst_rdy_n or TX_DST_RDY_N);
transmission <= RX_SRC_RDY_N nor TX_DST_RDY_N;

RX_DST_RDY_N <= dst_rdy_n or TX_DST_RDY_N;

-- -------------------------------------------------------
-- register for extracted data
ext_data_reg : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (ext_en = '1') then
         ext_data((conv_integer(unsigned(ext_addr_index))+1)*DATA_WIDTH - 1
                   downto
                   conv_integer(unsigned(ext_addr_index))*DATA_WIDTH) <= data;
      end if;
   end if;
end process ext_data_reg;

-- -------------------------------------------------------
-- assignement of extracted data to EXTRACTED_DATA output
EXTRACTED_DATA <= ext_data( ((EXT_OFFSET mod bperw) + EXT_SIZE)*8 - 1 downto (EXT_OFFSET mod bperw)*8);

-- -------------------------------------------------------    
-- Registers that store data and signals to be send to output ifc
-- -------------------------------------------------------

-- -------------------------------------------------------    
-- data valid register
send_rx_data_valid : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         send_rx_data_vld <= '0';
      elsif (tx_trans = '1' and rx_data_vld = '0') then
         send_rx_data_vld <= '0';
      elsif (rx_data_vld = '1' and (send_rx_data_vld = '0' or tx_trans = '1')) then
         send_rx_data_vld <= '1';
      end if;
   end if;
end process send_rx_data_valid;

-- -------------------------------------------------------
-- register for received word of data that will be send out
send_rx_data_reg : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (rx_data_vld = '1' and (send_rx_data_vld = '0' or tx_trans = '1')) then
         send_data <= data;
      end if;
   end if;    
end process send_rx_data_reg;

-- -------------------------------------------------------    
-- register for send data reminder
send_data_rem_reg : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (rx_data_vld = '1' and (send_rx_data_vld = '0' or tx_trans = '1')) then
         send_data_rem <= data_rem;
      end if;
   end if;    
end process send_data_rem_reg;

-- -------------------------------------------------------    
-- register for start of frame signal - send
-- which type is generated depends on CUT_OFFSET constant
SOF_N_GENERATOR0_I : if (CUT_OFFSET = 0) generate
   send_sof_n_reg : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            send_sof_n <= '1';
         elsif ((pipe_cut_en = '1') and send_rx_data_vld = '0') then
            send_sof_n <= send_sof_n and sof_n;
         elsif ((rx_data_vld = '1') and (send_rx_data_vld = '0' or tx_trans = '1')) then
            send_sof_n <= sof_n;
         end if;
      end if;    
   end process send_sof_n_reg;
end generate SOF_N_GENERATOR0_I;

SOF_N_GENERATORN_I : if (CUT_OFFSET > 0) generate
   send_sof_n_reg : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            send_sof_n <= '1';
         elsif (rx_data_vld = '1' and (send_rx_data_vld = '0' or tx_trans = '1')) then
            send_sof_n <= sof_n;
         end if;
      end if;    
   end process send_sof_n_reg;
end generate SOF_N_GENERATORN_I;

-- -------------------------------------------------------    
-- register for start of part signal - send
-- which type is generated depends on CUT_OFFSET constant
SOP_N_GENERATOR0_I : if (CUT_OFFSET = 0) generate
   send_sop_n_reg : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            send_sop_n <= '1';
         elsif ((pipe_cut_en = '1') and send_rx_data_vld = '0') then
            send_sop_n <= send_sop_n and sop_n;
         elsif ((rx_data_vld = '1') and (send_rx_data_vld = '0' or tx_trans = '1')) then
            send_sop_n <= sop_n;
         end if;
      end if;
   end process send_sop_n_reg;
end generate SOP_N_GENERATOR0_I;

SOP_N_GENERATORN_I : if (CUT_OFFSET > 0) generate
   send_sop_n_reg : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
         if (RESET = '1') then
            send_sop_n <= '1';
         elsif (rx_data_vld = '1' and (send_rx_data_vld = '0' or tx_trans = '1')) then
            send_sop_n <= sop_n;
         end if;
      end if;
   end process send_sop_n_reg;
end generate SOP_N_GENERATORN_I;

-- -------------------------------------------------------
-- register for eof_n signal - send
send_eof_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         send_eof_n <= '1';
      elsif (rx_data_vld = '1' and (send_rx_data_vld = '0' or tx_trans = '1')) then
         send_eof_n <= eof_n;
      else
         send_eof_n <= pre_tx_eof_n;
      end if;
   end if;
end process send_eof_n_reg;

-- -------------------------------------------------------
-- register for eop_n signal - send
send_eop_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         send_eop_n <= '1';
      elsif (rx_data_vld = '1' and (send_rx_data_vld = '0' or tx_trans = '1')) then
         send_eop_n <= eop_n;
      else
         send_eop_n <= pre_tx_eop_n;
      end if;
   end if;
end process send_eop_n_reg;

-- -------------------------------------------------------
-- register for cut_en signal
cut_en_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         pipe_cut_en <= '0';
      elsif (rx_trans = '1') then
         pipe_cut_en <= cut_en;
      end if;
   end if;
end process cut_en_reg;


-- -------------------------------------------------------
-- Registers that stores data and signals from input ifc
-- -------------------------------------------------------

-- -------------------------------------------------------    
-- data valid register
rx_data_valid : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         pre_rx_data_vld <= '0';
      elsif ((tx_trans = '1' or (rx_data_vld = '1' and send_rx_data_vld = '0')) and rx_trans = '0') then
         pre_rx_data_vld <= '0';
      elsif (rx_trans = '1') then
         pre_rx_data_vld <= '1';
      end if;
   end if;
end process rx_data_valid;

rx_data_vld <= pre_rx_data_vld and not cut_en;

-- -------------------------------------------------------    
-- register for received word of data
rx_data_reg : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (rx_trans = '1') then
         data <= RX_DATA;
      end if;
   end if;    
end process rx_data_reg;

-- -------------------------------------------------------    
-- register for data reminder
data_rem_reg : process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (rx_trans = '1') then
         data_rem <= rem_mux_out;
      end if;
   end if;    
end process data_rem_reg;

-- -------------------------------------------------------    
-- register for start of frame signal
sof_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         sof_n <= '1';
      elsif (rx_trans = '1' and cut_en = '1') then
         sof_n <= sof_n and RX_SOF_N;
      elsif (rx_trans = '1') then
         sof_n <= RX_SOF_N;
      end if;
   end if;
end process sof_n_reg;

-- -------------------------------------------------------    
-- register for start of part signal
sop_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         sop_n <= '1';
      elsif (rx_trans = '1' and cut_en = '1') then
         sop_n <= sop_n and RX_SOP_N;
      elsif (rx_trans = '1') then
         sop_n <= RX_SOP_N;
      end if;
   end if;
end process sop_n_reg;

-- -------------------------------------------------------
-- register for eof_n signal
eof_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         eof_n <= '1';
      elsif (rx_trans = '1') then
         eof_n <= RX_EOF_N;
      end if;
   end if;
end process eof_n_reg;

-- -------------------------------------------------------
-- register for eop_n signal
eop_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         eop_n <= '1';
      elsif (rx_trans = '1') then
         eop_n <= RX_EOP_N;
      end if;
   end if;
end process eop_n_reg;


-- -------------------------------------------------------
-- Multiplexors in unit
-- -------------------------------------------------------

-- -------------------------------------------------------
-- mux for rem signal - rem on input is valid only with
-- RX_EOP_N signal set to low. 
rem_mux : process(RX_EOP_N, RX_REM)
begin
   if (RX_EOP_N = '0') then
      rem_mux_out <= RX_REM;
   else
      rem_mux_out <= (others => '1');
   end if;
end process rem_mux;

-- -------------------------------------------------------
-- mux for tx_eop_n signal
tx_eop_n_mux : process(cut_en, send_eop_n, eop_n)
begin
   if (cut_en = '1') then
      pre_tx_eop_n <= send_eop_n and eop_n;
   else
      pre_tx_eop_n <= send_eop_n;
   end if;
end process tx_eop_n_mux;

-- -------------------------------------------------------
-- mux for tx_eof_n signal
tx_eof_n_mux : process(cut_en, send_eof_n, eof_n)
begin
   if (cut_en = '1') then
      pre_tx_eof_n <= send_eof_n and eof_n;
   else
      pre_tx_eof_n <= send_eof_n;
   end if;
end process tx_eof_n_mux;

-- -------------------------------------------------------
-- Counters in unit
-- -------------------------------------------------------

-- -------------------------------------------------------
-- counter of address index for extracted data register
ext_addr_cnt : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1' or ext_en = '0') then
         ext_addr_index <= (others => '0');
      elsif (rx_trans = '1') then
         ext_addr_index <= ext_addr_index + 1;
      end if;
   end if;
end process ext_addr_cnt;

-- -------------------------------------------------------
-- parts counter from the frame start
part_cnt : process(RESET, CLK)
begin
   if (CLK'event and CLK='1') then
      if (RESET = '1') then
         part_num <= (others => '0');
      elsif (rx_trans = '1') then
         if (RX_EOF_N = '0') then
            part_num <= (others => '0');
         elsif (RX_EOP_N = '0') then
            part_num <= part_num + 1;
         end if;
      end if;
   end if;
end process part_cnt;

-- -------------------------------------------------------
-- words counter from the part start for extraction
word_cnt : process(RESET, CLK)
begin
   if (CLK'event and CLK='1') then
      if (RESET = '1') then
         word_num <= (others => '0');
      elsif (rx_trans = '1') then
         if (RX_EOP_N = '0') then
            word_num <= (others => '0');
         else
            word_num <= word_num + 1;
         end if;
      end if;
   end if;
end process word_cnt;

-- -------------------------------------------------------
-- cut_words counter from the part start
cut_word_cnt : process(RESET, CLK)
begin
   if (CLK'event and CLK='1') then
      if (RESET = '1') then
         cut_word_num <= (others => '0');
      elsif (rx_trans = '1') then
         if (RX_EOP_N = '0') then
            cut_word_num <= (others => '0');
         else
            cut_word_num <= cut_word_num + 1;
         end if;
      end if;
   end if;
end process cut_word_cnt;


-- -------------------------------------------------------
-- Registers for FSM transation decision
-- -------------------------------------------------------

-- -------------------------------------------------------    
-- register for start of part signal
fsm_sof_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         fsm_sof_n <= '1';
      elsif (rx_trans = '1') then
         fsm_sof_n <= RX_SOF_N;
      end if;
   end if;
end process fsm_sof_n_reg;

-- -------------------------------------------------------
-- register for eof_n signal
fsm_eof_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         fsm_eof_n <= '1';
      elsif (rx_trans = '1') then
         fsm_eof_n <= RX_EOF_N;
      end if;
   end if;
end process fsm_eof_n_reg;

-- -------------------------------------------------------
-- register for eop_n signal
fsm_eop_n_reg : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         fsm_eop_n <= '1';
      elsif (rx_trans = '1') then
         fsm_eop_n <= RX_EOP_N;
      end if;
   end if;
end process fsm_eop_n_reg;


-- -------------------------------------------------------
-- FSM
-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         present_state <= IDLE;
      else
         present_state <= next_state;
      end if;
   end if;
end process sync_logic;
-- -------------------------------------------------------
next_state_logic : process(present_state, part_num, word_num, cut_word_num, fsm_sof_n,
                           RX_EOP_N, RX_EOF_N, fsm_eof_n, fsm_eop_n, ext_addr_index, data_rem, transmission)
begin
   next_state <= present_state;

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - - - -
   when IDLE =>
      if (transmission = '1') then
      -- transfer in progress      
         if (conv_integer(unsigned(part_num)) = PART
             and 
            conv_integer(unsigned(word_num)) = first_ext_word) then
            -- data for extraction are being transferred right now
            if (conv_integer(unsigned(cut_word_num)) >= CUT_OFFSET
                and conv_integer(unsigned(cut_word_num)) < CUT_OFFSET + CUT_SIZE) then
                -- data meant to be removed is being transferred right now
               next_state <= EXTRACT_REMOVE;
            else
               next_state <= EXTRACTION;
            end if;
         elsif (conv_integer(unsigned(part_num)) = PART
                and RX_EOP_N = '0' and RX_EOF_N = '1') then
            -- data not extracted and now even can't be from this frame
            next_state <= AFTER_EXT;
         else
            next_state <= IDLE;
         end if;      
      else
         next_state <= IDLE;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when EXTRACTION =>
      if (transmission = '1') then
      -- transfer in progress      
         if (conv_integer(unsigned(ext_addr_index)) < num_of_words - 1) then
            if (fsm_eop_n = '0') then
               -- part ended earlier than all neded data is extracted
               next_state <= ERROR_EXT;
            elsif (conv_integer(unsigned(cut_word_num)) >= CUT_OFFSET
                   and conv_integer(unsigned(cut_word_num)) < CUT_OFFSET + CUT_SIZE) then
               next_state <= EXTRACT_REMOVE;
            else
               next_state <= EXTRACTION;
            end if;
         elsif (conv_integer(unsigned(data_rem)) < (EXT_OFFSET+EXT_SIZE-1) mod bperw) then
            -- if there is not enought bytes in last extracted word
            next_state <= ERROR_EXT;
         else
            next_state <= VLD_EXT;
         end if;
      else
         next_state <= EXTRACTION;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when EXTRACT_REMOVE =>
      if (transmission = '1') then
      -- transfer in progress
         if (conv_integer(unsigned(ext_addr_index)) < num_of_words - 1) then
            if (fsm_eop_n = '0') then
               -- part ended earlier than all neded data is extracted
               next_state <= ERROR_EXT;
            elsif (conv_integer(unsigned(cut_word_num)) >= CUT_OFFSET + 1
                   and conv_integer(unsigned(cut_word_num)) < CUT_OFFSET + CUT_SIZE) then
               next_state <= EXTRACT_REMOVE;
            else
               next_state <= EXTRACT_AFTER_REMOVE;
            end if;
         elsif (conv_integer(unsigned(data_rem)) < (EXT_OFFSET+EXT_SIZE-1) mod bperw) then
            -- if there is not enought bytes in last extracted word
            next_state <= ERROR_EXT;
         else
            next_state <= VLD_EXT;
         end if;
      else
         next_state <= EXTRACT_REMOVE;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when EXTRACT_AFTER_REMOVE =>
      if (transmission = '1') then
      -- transfer in progress
         if (conv_integer(unsigned(ext_addr_index)) < num_of_words - 1) then
            if (fsm_eop_n = '0') then
               -- part ended earlier than all neded data is extracted
               next_state <= ERROR_EXT;
            else
               next_state <= EXTRACT_AFTER_REMOVE;
            end if;
         elsif (conv_integer(unsigned(data_rem)) < (EXT_OFFSET+EXT_SIZE-1) mod bperw) then
            -- if there is not enought bytes in last extracted word
            next_state <= ERROR_EXT;
         else
            next_state <= VLD_EXT;
         end if;
      else
         next_state <= EXTRACT_AFTER_REMOVE;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when VLD_EXT =>
      if (transmission = '1') then
      -- transfer in progress
         if (fsm_eof_n = '0') then
         -- it's end of current frame
            if (PART = 0 and first_ext_word = 0) then
               -- data for extraction are being transferred right now
               if (conv_integer(unsigned(cut_word_num)) >= CUT_OFFSET
                   and conv_integer(unsigned(cut_word_num)) < CUT_OFFSET + CUT_SIZE) then
                   -- data meant to be removed is being transferred right now
                  next_state <= EXTRACT_REMOVE;
               else
                  next_state <= EXTRACTION;
               end if;
            elsif (conv_integer(unsigned(part_num)) = PART
                   and RX_EOP_N = '0' and RX_EOF_N = '1') then
               -- data not extracted and now even can't be from this frame
               next_state <= AFTER_EXT;
            else            
               next_state <= IDLE;
            end if;
         elsif (fsm_sof_n = '0') then
         -- frame ended with cutted word => now we are in new frame
            next_state <= IDLE;
         else
            next_state <= AFTER_EXT;
         end if;
      else
         next_state <= VLD_EXT;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when ERROR_EXT =>
      if (transmission = '1') then
      -- transfer in progress
         if (fsm_eof_n = '0') then
         -- it's end of current frame
            if (PART = 0 and first_ext_word = 0) then
               -- data for extraction are being transferred right now
               if (conv_integer(unsigned(cut_word_num)) >= CUT_OFFSET
                   and conv_integer(unsigned(cut_word_num)) < CUT_OFFSET + CUT_SIZE) then
                   -- data meant to be removed is being transferred right now
                  next_state <= EXTRACT_REMOVE;
               else
                  next_state <= EXTRACTION;
               end if;
            elsif (conv_integer(unsigned(part_num)) = PART
                   and RX_EOP_N = '0' and RX_EOF_N = '1') then
               -- data not extracted and now even can't be from this frame
               next_state <= AFTER_EXT;
            else            
               next_state <= IDLE;
            end if;
         elsif (fsm_sof_n = '0') then
         -- frame ended with cutted word => now we are in new frame
            next_state <= IDLE;
         else
            next_state <= AFTER_EXT;
         end if;
      else
         next_state <= ERROR_EXT;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when AFTER_EXT =>
      if (fsm_eof_n = '0' and transmission = '1') then
      -- it's end of current frame
         if (PART = 0 and first_ext_word = 0) then
            -- data for extraction are being transferred right now
            if (conv_integer(unsigned(cut_word_num)) >= CUT_OFFSET
                and conv_integer(unsigned(cut_word_num)) < CUT_OFFSET + CUT_SIZE) then
                -- data meant to be removed is being transferred right now
               next_state <= EXTRACT_REMOVE;
            else
               next_state <= EXTRACTION;
            end if;
         elsif (conv_integer(unsigned(part_num)) = PART
                and RX_EOP_N = '0' and RX_EOF_N = '1') then
            -- data not extracted and now even can't be from this frame
            next_state <= AFTER_EXT;
         else            
            next_state <= IDLE;
         end if;
      else
         next_state <= AFTER_EXT;
      end if;
   -- - - - - - - - - - - - - - - - - - - - - - -
   when others =>
      next_state <= IDLE;
   end case;
end process next_state_logic;

-- -------------------------------------------------------
output_logic : process(present_state, fsm_eof_n)
begin
   dst_rdy_n      <= '0';
   ext_en         <= '0';
   cut_en         <= '0';
   EXTRACTED_DONE <= '0';
   EXTRACTED_ERR  <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - - - -
   when IDLE =>
   -- - - - - - - - - - - - - - - - - - - - - - -
   when EXTRACTION =>
      if (fsm_eof_n <= '0' and PART = 0 and first_ext_word = 0) then
         -- it is end of frame and next extraction data are being send - need to send ext_vld signal
         dst_rdy_n <= '1';
      end if;
      ext_en <= '1';
   -- - - - - - - - - - - - - - - - - - - - - - -
   when EXTRACT_REMOVE =>
      if (fsm_eof_n <= '0' and PART = 0 and first_ext_word = 0) then
         -- it is end of frame and next extraction data are being send - need to send ext_vld signal
         dst_rdy_n <= '1';
      end if;
      ext_en <= '1';
      cut_en <= '1';
   -- - - - - - - - - - - - - - - - - - - - - - -
   when EXTRACT_AFTER_REMOVE =>
      if (fsm_eof_n <= '0' and PART = 0 and first_ext_word = 0) then
         -- it is end of frame and next extraction data are being send - need to send ext_vld signal
         dst_rdy_n <= '1';
      end if;
      ext_en <= '1';
   -- - - - - - - - - - - - - - - - - - - - - - -
   when VLD_EXT =>
      EXTRACTED_DONE <= '1';
   -- - - - - - - - - - - - - - - - - - - - - - -
   when ERROR_EXT =>
      EXTRACTED_DONE <= '1';
      EXTRACTED_ERR <= '1';
   -- - - - - - - - - - - - - - - - - - - - - - -
   when AFTER_EXT =>
   -- - - - - - - - - - - - - - - - - - - - - - -
   when others =>
   end case;
end process output_logic;

end architecture behavioral;
