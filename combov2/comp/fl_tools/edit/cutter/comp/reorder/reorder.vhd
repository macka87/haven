-- reorder.vhd: FrameLink cutter: Reorder logic
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
architecture full of reorder is

   -- ============================== SIGNALS ===================================
   
   -- reordered data
   signal reordered_data_end   : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal reordered_data_after : std_logic_vector(DATA_WIDTH - 1 downto 0);
   
   -- auxiliary registers signals
   signal aux0_data     : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal reg_aux0_data : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal aux1_data     : std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal reg_aux1_data : std_logic_vector(DATA_WIDTH - 1 downto 0);
   
   -- auxiliary reg. enable variants
   signal aux0_en       : std_logic_vector(DATA_BYTES - 1 downto 0);
   signal aux0_en_start : std_logic_vector(DATA_BYTES - 1 downto 0);
   signal aux0_en_end   : std_logic_vector(DATA_BYTES - 1 downto 0);
   signal aux0_en_after : std_logic_vector(DATA_BYTES - 1 downto 0);
   
   signal aux1_en       : std_logic_vector(DATA_BYTES - 1 downto 0);
   signal aux1_en_start : std_logic_vector(DATA_BYTES - 1 downto 0);
   signal aux1_en_end   : std_logic_vector(DATA_BYTES - 1 downto 0);
   signal aux1_en_after : std_logic_vector(DATA_BYTES - 1 downto 0);
   
   -- auxiliary counter
   signal cnt_aux    : std_logic;
   
   -- output counter
   signal cnt_output        : std_logic;
   signal reg_cnt_output    : std_logic;
   signal cnt_output_areset : std_logic;
   
   -- mux select signals
   signal sel_output      : std_logic;
   
   -- output register signals
   signal output_data     : std_logic_vector(DATA_WIDTH - 1 downto 0);
   
   -- other
   signal reg_I_TX_DATA_en   : std_logic;


begin

   Extract_one_beat: if (START_WORD = END_WORD) generate

      -- CONDITIONS:
      -- A:   if (i < START_BYTE or START_WORD /= END_WORD)
      --        reordered_data_end(i) <= RX_DATA(i);
      -- B:   elsif (i < ((START_BYTE + DATA_BYTES - END_BYTE - 1) mod DATA_BYTES))
      --        reordered_data_end(i) <= RX_DATA((i + SIZE) mod DATA_BYTES);
      --      else
      --        reordered_data_end(i) <= RX_DATA(i - ((DATA_BYTES - END_BYTE - 1) mod DATA_BYTES));
      
      Reorder_data_end: for i in 0 to DATA_BYTES - 1 generate
      
         Condition_A: if (i < START_BYTE or START_WORD /= END_WORD) generate
            reordered_data_end(8 * (i + 1) - 1 downto 8 * i)
               <= DATA_IN(
                  8 * (i + 1) - 1
                     downto
                  8 * i
               );
         end generate;
         
         Condition_not_A: if (i >= START_BYTE and START_WORD = END_WORD) generate
         
            Condition_B: if (i < ((START_BYTE + DATA_BYTES - END_BYTE - 1) mod DATA_BYTES)) generate
               reordered_data_end(8 * (i + 1) - 1 downto 8 * i)
                  <= DATA_IN(
                     8 * (((i + SIZE) mod DATA_BYTES) + 1) - 1
                        downto
                     8 * ((i + SIZE) mod DATA_BYTES)
                  );
            end generate;
         
            Condition_not_B: if (i >= ((START_BYTE + DATA_BYTES - END_BYTE - 1) mod DATA_BYTES)) generate
               reordered_data_end(8 * (i + 1) - 1 downto 8 * i)
                  <= DATA_IN(
                     8 * (((i -(DATA_BYTES - END_BYTE - 1)) mod DATA_BYTES) + 1) - 1
                        downto
                     8 * ((i - (DATA_BYTES - END_BYTE - 1))  mod DATA_BYTES)
                  );
            end generate;
         
         end generate;
      
      end generate;
      
      -- aux1_data mux
      process(SEL_REORDER_END, reordered_data_end, reordered_data_after)
      begin
        if (SEL_REORDER_END = '1') then
           aux1_data <= reordered_data_end;
        else
           aux1_data <= reordered_data_after;
        end if;
      end process;
      
      end generate;
      
      
      -- if no mux needed, connect reordered_data_after directly
      Extract_more_than_beat: if (START_WORD /= END_WORD) generate
      aux1_data <= reordered_data_after;
      end generate;
      
      
      Reorder_data_after: for i in 0 to DATA_BYTES - 1 generate
      reordered_data_after(8 * (i + 1) - 1 downto 8 * i)
        <= DATA_IN(
              8 * (((i + SIZE) mod DATA_BYTES) + 1) - 1
                 downto
              8 * ((i + SIZE) mod DATA_BYTES)
           );
      end generate;
      
      
      -- aux0_data mux
      process(SEL_REORDER, DATA_IN, aux1_data)
      begin
      if (SEL_REORDER = '1') then
        aux0_data <= aux1_data;
      else
        aux0_data <= DATA_IN;
      end if;
      end process;
      
      
      -- auxiliary counter
      process(CLK, RESET)
      begin
      if (RESET = '1') then -- asynchronous reset
        cnt_aux <= '0';
      elsif (CLK'event and CLK = '1') then
        if (RX_EOF = '1') then -- synchronous reset
           cnt_aux <= '0';
        elsif (CNT_AUX_EN = '1') then
           cnt_aux <= not cnt_aux;
        end if;
      end if;
      end process;
      
      
      -- auxiliary register 0
      Aux0: for i in 0 to DATA_BYTES - 1 generate
      
      -- aux0_en_start
      Aux0_en_start_1: if (i < START_BYTE) generate
        aux0_en_start(i) <= '1' and TRANSMIT_PROGRESS;
      end generate;
      Aux0_en_start_0: if (i >= START_BYTE) generate
        aux0_en_start(i) <= '0' and TRANSMIT_PROGRESS;
      end generate;
      
      -- aux0_en_end
      Aux0_en_end_small: if (START_WORD = END_WORD) generate
        Aux0_en_end_small_1: if (i < (DATA_BYTES - SIZE)) generate
           aux0_en_end(i) <= '1' and TRANSMIT_PROGRESS;
        end generate;
         Aux0_en_end_small_0: if (i >= (DATA_BYTES - SIZE)) generate
           aux0_en_end(i) <= '0' and TRANSMIT_PROGRESS;
        end generate;
      end generate;
      Aux0_en_end_big: if (START_WORD /= END_WORD) generate
        Aux0_en_end_big_1: if ((i >= START_BYTE) and (i < (START_BYTE + DATA_BYTES - END_BYTE - 1))) generate
           aux0_en_end(i) <= '1' and TRANSMIT_PROGRESS;
        end generate;
         Aux0_en_end_big_0: if ((i < START_BYTE) or (i >= (START_BYTE + DATA_BYTES - END_BYTE - 1))) generate
           aux0_en_end(i) <= '0' and TRANSMIT_PROGRESS;
        end generate;
      end generate;
      
      -- aux0_en_after
      Aux0_en_after_1: if (i >= (START_BYTE - END_BYTE - 1) and i < (START_BYTE - END_BYTE - 1 + DATA_BYTES)) generate
        aux0_en_after(i) <= not cnt_aux and TRANSMIT_PROGRESS;
      end generate;
      Aux0_en_after_0: if (i < (START_BYTE - END_BYTE - 1) or i >= (START_BYTE - END_BYTE - 1 + DATA_BYTES)) generate
        aux0_en_after(i) <= cnt_aux and TRANSMIT_PROGRESS;
      end generate;
      
      -- aux0_en (multiplexer)
      process(SEL_AUX0_EN, aux0_en_start, aux0_en_end, aux0_en_after, TRANSMIT_PAUSE, REG_RX_SRC_RDY, RX_READY)
      begin
         if    ( SEL_AUX0_EN = en_start ) then
            aux0_en <= aux0_en_start;
         elsif ( SEL_AUX0_EN = en_progress ) then
            aux0_en <= (others => '0'); -- block
         elsif ( SEL_AUX0_EN = en_end   ) then
            aux0_en <= aux0_en_end;
         elsif ( SEL_AUX0_EN = en_after ) then
            aux0_en <= aux0_en_after;
         else
            if ((TRANSMIT_PAUSE = '1' and REG_RX_SRC_RDY = '0') or RX_READY = '0') then
               aux0_en <= (others => '0');
            else
               aux0_en <= (others => '1'); -- default: enabled
            end if;
         end if;
      end process;
      
      Reg_aux0: process(CLK) -- no need for RESET
      begin
        if (CLK'event and CLK = '1') then
           if (aux0_en(i) = '1' and TX_DST_RDY = '1') then
              reg_aux0_data(8*(i+1)-1 downto 8*i) <= aux0_data(8*(i+1)-1 downto 8*i);
           end if;
        end if;
      end process;
      
      end generate;
      
      
      -- auxiliary register 1
      Aux1: for i in 0 to DATA_BYTES - 1 generate
      
      -- aux1_en_start
      aux1_en_start(i) <= '0';
      
      -- aux1_en_end
      Aux1_en_end_1: if ((START_BYTE - END_BYTE) > 1 and i < (START_BYTE - END_BYTE - 1)) generate
        aux1_en_end(i) <= '1';
      end generate;
      Aux1_en_end_0: if ((START_BYTE - END_BYTE) <= 1 or i >= (START_BYTE - END_BYTE - 1)) generate
        aux1_en_end(i) <= '0';
      end generate;
      
      -- aux1_en_after
      Aux1_en_after_1: if (i >= (START_BYTE - END_BYTE - 1) and i < (START_BYTE - END_BYTE - 1 + DATA_BYTES)) generate
        aux1_en_after(i) <= cnt_aux;
      end generate;
      Aux1_en_after_0: if (i < (START_BYTE - END_BYTE - 1) or i >= (START_BYTE - END_BYTE - 1 + DATA_BYTES)) generate
        aux1_en_after(i) <= not cnt_aux;
      end generate;
      
      -- aux1_en (multiplexer)
      process(SEL_AUX1_EN, aux1_en_start, aux1_en_end, aux1_en_after)
      begin
        if    ( SEL_AUX1_EN = en_start ) then
           aux1_en <= aux1_en_start;
        elsif ( SEL_AUX1_EN = en_progress ) then
       aux1_en <= (others => '0'); -- block
        elsif ( SEL_AUX1_EN = en_end   ) then
           aux1_en <= aux1_en_end;
        elsif ( SEL_AUX1_EN = en_after ) then
           aux1_en <= aux1_en_after;
        else
           aux1_en <= (others => '0'); -- default: disabled
        end if;
      end process;
      
      Reg_aux1: process(CLK) -- no need for RESET
      begin
        if (CLK'event and CLK = '1') then
           if (aux1_en(i) = '1' and TRANSMIT_PROGRESS = '1' and TX_DST_RDY = '1') then
              reg_aux1_data(8*(i+1)-1 downto 8*i) <= aux1_data(8*(i+1)-1 downto 8*i);
           end if;
        end if;
      end process;
      
      end generate;
      
      
      -- output counter
      Cnt_output_areset_wait: if (RX_WAIT_NEED) generate
         cnt_output_areset <= REG2_RX_EOP;
      end generate;
      Cnt_output_areset_no_wait: if (not RX_WAIT_NEED) generate
         cnt_output_areset <= REG_RX_EOP;
      end generate;
      
      process(CLK, RESET)
      begin
      if (RESET = '1') then -- asynchronous reset
        cnt_output <= '0';
      elsif (CLK'event and CLK = '1') then
        if (cnt_output_areset = '1') then -- synchronous reset
           cnt_output <= '0';
        elsif (CNT_OUTPUT_EN = '1') then
           cnt_output <= not cnt_output;
        end if;
      end if;
      end process;
      
      process(CLK) -- no need for RESET
      begin
      if (CLK'event and CLK = '1') then
        reg_cnt_output <= cnt_output;
      end if;
      end process;
      
      sel_output <= reg_cnt_output;
      
      -- output multiplexer
      process(sel_output, reg_aux0_data, reg_aux1_data)
      begin
      if (sel_output = '1') then
        output_data <= reg_aux1_data;
      else
        output_data <= reg_aux0_data;
      end if;
      end process;
      
      
      -- output register
      process(CLK) -- no need for RESET
      begin
      if (CLK'event and CLK = '1') then
        reg_I_TX_DATA_en <= I_TX_DATA_EN;
      end if;
      end process;
      
      Output_reg: for i in 0 to DATA_BYTES - 1 generate
      
      process(CLK) -- no need for RESET
      begin
        if (CLK'event and CLK = '1') then
           if (	reg_I_TX_DATA_en = '1' and TX_DST_RDY = '1') then
              DATA_OUT <= output_data;
      end if;
        end if;
      end process;
      
      end generate;

end architecture full;
