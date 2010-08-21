-- cutter.vhd: FrameLink cutter
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
architecture full of fl_cutter is

   -- ============================ CONSTANTS ===================================

   -- maximum number of frame parts - you can freely change this
   constant MAX_PARTS     : integer := 4;
   -- maximal size of one frame part (in bytes) - you can freely change this
   constant MAX_PART_SIZE : integer := 128 * (DATA_WIDTH / 8);

   -- width of data bus in bytes
   constant DATA_BYTES : integer := DATA_WIDTH / 8;
   -- serial number of word containing first byte of data to cut
   constant START_WORD : integer := OFFSET / DATA_BYTES;
   -- serial number of word containing last byte of data to cut
   constant END_WORD   : integer := (OFFSET + SIZE - 1) / DATA_BYTES;
   -- serial number of first byte of data to cut in START_WORD
   constant START_BYTE : integer := OFFSET mod DATA_BYTES;
   -- serial number of last byte of data to cut in END_WORD
   constant END_BYTE   : integer := (OFFSET + SIZE - 1) mod DATA_BYTES;
   -- flag whether extra empty beat is needed to transmit all remaining reordered data
   constant RX_WAIT_NEED : boolean := (((START_BYTE - END_BYTE + DATA_BYTES) mod DATA_BYTES) /= 1 and MODIFY);


   -- ============================== SIGNALS ===================================

   -- pseudo-interface signals to invert frame link negative logic to positive
   -- write interface
   signal I_RX_DATA      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal I_RX_REM       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal I_RX_SRC_RDY_N : std_logic;
   signal I_RX_DST_RDY_N : std_logic;
   signal I_RX_SOP_N     : std_logic;
   signal I_RX_EOP_N     : std_logic;
   signal I_RX_SOF_N     : std_logic;
   signal I_RX_EOF_N     : std_logic;
   -- read interface
   signal I_TX_DATA      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal I_TX_REM       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal I_TX_SRC_RDY_N : std_logic;
   signal I_TX_DST_RDY_N : std_logic;
   signal I_TX_SOP_N     : std_logic;
   signal I_TX_EOP_N     : std_logic;
   signal I_TX_SOF_N     : std_logic;
   signal I_TX_EOF_N     : std_logic;
   
   signal I_TX_DATA_en       : std_logic;
   
   -- registered input signals
   signal reg_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg_rx_src_rdy_n : std_logic;
   signal reg_rx_sop_n     : std_logic;
   signal reg_rx_eop_n     : std_logic;
   signal reg_rx_sof_n     : std_logic;
   signal reg_rx_eof_n     : std_logic;
   
   signal reg_rx_sop_n_lv  : std_logic;-- "lv" stands for "last valid"
   signal reg_rx_eop_n_lv  : std_logic;
   signal reg_rx_sof_n_lv  : std_logic;
   signal reg_rx_eof_n_lv  : std_logic;
   
   signal reg_rx_sop_n_bc  : std_logic;-- "bc" stands for "before cut"
   signal reg_rx_eop_n_bc  : std_logic;
   signal reg_rx_sof_n_bc  : std_logic;
   signal reg_rx_eof_n_bc  : std_logic;
   
   signal reg2_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg2_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg2_rx_src_rdy_n : std_logic;
   signal reg2_rx_sop_n     : std_logic;
   signal reg2_rx_eop_n     : std_logic;
   signal reg2_rx_sof_n     : std_logic;
   signal reg2_rx_eof_n     : std_logic;
   
   signal reg2_rx_sop_n_lv  : std_logic;
   signal reg2_rx_eop_n_lv  : std_logic;
   signal reg2_rx_sof_n_lv  : std_logic;
   signal reg2_rx_eof_n_lv  : std_logic;
   
   signal reg3_rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg3_rx_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg3_rx_src_rdy_n : std_logic;
   signal reg3_rx_sop_n     : std_logic;
   signal reg3_rx_eop_n     : std_logic;
   signal reg3_rx_sof_n     : std_logic;
   signal reg3_rx_eof_n     : std_logic;
   
   -- rem signals
   signal generated_tx_rem       : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal reg_generated_tx_rem   : std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   
   -- tx_src_rdy signals
   signal generated_tx_src_rdy_n                 : std_logic;
   signal reg_generated_tx_src_rdy_n             : std_logic;
   
   -- tx_sof signals
   signal generated_tx_sof_n     : std_logic;
   signal reg_generated_tx_sof_n : std_logic;
   
   -- tx_sop signals
   signal generated_tx_sop_n              : std_logic;
   signal reg_generated_tx_sop_n          : std_logic;
   
   -- tx_eop signals
   signal generated_tx_eop_n            : std_logic;
   signal reg_generated_tx_eop_n        : std_logic;
   
   -- tx_eof signals
   signal generated_tx_eof_n     : std_logic;
   signal reg_generated_tx_eof_n : std_logic;

   -- auxiliary signals
   signal transmit_progress : std_logic; -- (generated by FSM transmit) indicating transmit in progress
   signal transmit_pause    : std_logic; -- (generated by FSM transmit) indicating transmit paused (is going to continue)
   signal cut_extracted     : std_logic; -- (generated by FSM main) indicating cut data are complete or part has ended
   signal ready             : std_logic;
   signal cut_progress      : std_logic;

   -- parts and words counter
   signal cnt_part    : std_logic_vector(log2(MAX_PARTS)-1 downto 0);
   signal cnt_word    : std_logic_vector(log2(MAX_PART_SIZE / DATA_BYTES)-1 downto 0);
   
   -- auxiliary counter
   signal cnt_aux_en : std_logic;

   -- auxiliary reg. enable variants
   signal sel_aux0_en   : t_aux_en;
   signal sel_aux1_en   : t_aux_en;

   -- output counter
   signal cnt_output_en     : std_logic;

   -- mux select signals
   signal sel_reorder_end : std_logic;
   signal sel_reorder     : std_logic;


begin

   -- assert generic conditions to eliminate counter overflow
   assert (PART < MAX_PARTS)
      report "FL_CUTTER: Generic PART must be lesser than constant MAX_PARTS."
      severity error;
   assert ((OFFSET + SIZE) <= (MAX_PART_SIZE))
      report "FL_CUTTER: You are trying to extract data from part bigger than constant MAX_PART_SIZE."
      severity error;


   -- mapping interface signals to pseudo-interface signals to invert logic
   -- write interface
   I_RX_DATA      <= RX_DATA;
   I_RX_REM       <= RX_REM;
   I_RX_SRC_RDY_N <= not RX_SRC_RDY_N;
   RX_DST_RDY_N   <= not I_RX_DST_RDY_N;
   I_RX_SOP_N     <= not RX_SOP_N;
   I_RX_EOP_N     <= not RX_EOP_N;
   I_RX_SOF_N     <= not RX_SOF_N;
   I_RX_EOF_N     <= not RX_EOF_N;
   -- read interface
   TX_DATA        <= I_TX_DATA;
   TX_REM         <= I_TX_REM;
   TX_SRC_RDY_N   <= not I_TX_SRC_RDY_N;
   I_TX_DST_RDY_N <= not TX_DST_RDY_N;
   TX_SOP_N       <= not (I_TX_SOP_N and I_TX_DST_RDY_N);
   TX_EOP_N       <= not (I_TX_EOP_N and I_TX_DST_RDY_N);
   TX_SOF_N       <= not (I_TX_SOF_N and I_TX_DST_RDY_N);
   TX_EOF_N       <= not (I_TX_EOF_N and I_TX_DST_RDY_N);
   
   -- registering input signals
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         if (I_TX_DST_RDY_N = '1') then
            reg_rx_rem       <= I_RX_REM;
            reg_rx_src_rdy_n <= I_RX_SRC_RDY_N;
            reg_rx_sop_n     <= I_RX_SOP_N;
            reg_rx_eop_n     <= I_RX_EOP_N;
            reg_rx_sof_n     <= I_RX_SOF_N;
            reg_rx_eof_n     <= I_RX_EOF_N;
         end if;
      end if;
   end process;
   
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         if (ready = '1' and I_TX_DST_RDY_N = '1') then
            reg_rx_data      <= I_RX_DATA;
         end if;
      end if;
   end process;
   
   -- registering last valid input signals
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         if (transmit_progress = '1' and I_TX_DST_RDY_N = '1') then
            reg_rx_sop_n_lv  <= I_RX_SOP_N;
            reg_rx_eop_n_lv  <= I_RX_EOP_N;
            reg_rx_sof_n_lv  <= I_RX_SOF_N;
            reg_rx_eof_n_lv  <= I_RX_EOF_N;
         end if;
      end if;
   end process;
   
   -- registering input signals before cut_progress
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         if (cut_progress = '0') then
            reg_rx_sop_n_bc  <= I_RX_SOP_N;
            reg_rx_eop_n_bc  <= I_RX_EOP_N;
            reg_rx_sof_n_bc  <= I_RX_SOF_N;
            reg_rx_eof_n_bc  <= I_RX_EOF_N;
         end if;
      end if;
   end process;
   
   -- registering input signals (2)
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         if (I_TX_DST_RDY_N = '1') then
            reg2_rx_rem       <= reg_rx_rem;
            reg2_rx_src_rdy_n <= reg_rx_src_rdy_n;
            reg2_rx_sop_n     <= reg_rx_sop_n;
            reg2_rx_eop_n     <= reg_rx_eop_n;
            reg2_rx_sof_n     <= reg_rx_sof_n;
            reg2_rx_eof_n     <= reg_rx_eof_n;
         end if;
      end if;
   end process;
   
   -- registering last valid input signals (2)
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         if (transmit_progress = '1' and I_TX_DST_RDY_N = '1') then
            reg2_rx_data      <= reg_rx_data;
            reg2_rx_sop_n_lv  <= reg_rx_sop_n_lv;
            reg2_rx_eop_n_lv  <= reg_rx_eop_n_lv;
            reg2_rx_sof_n_lv  <= reg_rx_sof_n_lv;
            reg2_rx_eof_n_lv  <= reg_rx_eof_n_lv;
         end if;
      end if;
   end process;
   
   -- registering input signals (3)
   process(CLK) -- no need for RESET
   begin
      if (CLK'event and CLK = '1') then
         if (I_TX_DST_RDY_N = '1') then
            reg3_rx_rem       <= reg2_rx_rem;
            reg3_rx_src_rdy_n <= reg2_rx_src_rdy_n;
            reg3_rx_sop_n     <= reg2_rx_sop_n;
            reg3_rx_eop_n     <= reg2_rx_eop_n;
            reg3_rx_sof_n     <= reg2_rx_sof_n;
            reg3_rx_eof_n     <= reg2_rx_eof_n;
         end if;
      end if;
   end process;
   
   -- registering last valid REM
--    process(CLK) -- no need for RESET
--    begin
--       if (CLK'event and CLK = '1') then
--          if (reg2_rx_eop_n = '1') then
--             last_rx_rem <= reg2_rx_rem;
--          end if;
--       end if;
--    end process;


-- -----------------------------------------------------------------------------
--                               TRANSMIT FSM
-- -----------------------------------------------------------------------------
   Fsm_transmit_i: entity work.fsm_transmit
   port map(
      RESET             => RESET, -- Asynchronous reset
      CLK               => CLK,
 
      -- inputs
      SOF               => I_RX_SOF_N, -- Start Of Frame
      EOF               => I_RX_EOF_N, -- End Of Frame
      SRC_RDY           => I_RX_SRC_RDY_N, -- SouRCe ReaDY
      DST_RDY           => I_RX_DST_RDY_N, -- DeSTination ReaDY

      -- outputs
      TRANSMIT_PROGRESS => transmit_progress, -- Transmit in progress
      TRANSMIT_PAUSE    => transmit_pause -- Transmit paused (is going to continue)
   );
   


-- -----------------------------------------------------------------------------
--                            PARTS AND WORDS COUNTER
-- -----------------------------------------------------------------------------

   Parts_counter: process(CLK, RESET)
   begin
      if (RESET = '1') then
         cnt_part <= (others => '0');
      elsif (CLK'event and CLK = '1') then
         if (reg_rx_eof_n = '1') then
            cnt_part <= (others => '0');
         elsif (reg_rx_eop_n = '1') then
            cnt_part <= cnt_part + '1';
         end if;
      end if;
   end process;

   Words_counter: process(CLK, RESET)
   begin
      if (RESET = '1') then
         cnt_word <= (others => '0');
      elsif (CLK'event and CLK = '1') then
         if (reg_rx_eop_n = '1') then
            cnt_word <= (others => '0');
         elsif (transmit_progress = '1') then
            cnt_word <= cnt_word + '1';
         end if;
      end if;
   end process;


-- -----------------------------------------------------------------------------
--                                 MAIN FSM
-- -----------------------------------------------------------------------------
   Fsm_main_i: entity work.fsm_main
   generic map(
      DATA_WIDTH    => DATA_WIDTH, -- FrameLink width
      DATA_BYTES    => DATA_BYTES, -- Width of data bus in bytes
      PART          => PART, -- Number of processed part, 0 = first part
      MAX_PARTS     => MAX_PARTS, -- Maximum number of frame parts
      MAX_PART_SIZE => MAX_PART_SIZE, -- Maximal size of one frame part (in bytes)

      START_WORD    => START_WORD, -- Serial number of word containing first byte of data to cut
      END_WORD      => END_WORD, -- Serial number of word containing last byte of data to cut
      START_BYTE    => START_BYTE, -- Serial number of first byte of data to cut in START_WORD
      END_BYTE      => END_BYTE, -- Serial number of last byte of data to cut in END_WORD
      RX_WAIT_NEED  => RX_WAIT_NEED -- Flag whether extra empty beat is needed to transmit all remaining reordered data
   )
   port map(
      RESET                => RESET, -- Asynchronous reset
      CLK                  => CLK,

      -- inputs
      TRANSMIT_PROGRESS    => transmit_progress, -- Indicating transmit on RX port in progress
      PART_NUM             => cnt_part, -- Number of currently processed part
      WORD_NUM             => cnt_word, -- Number of currently processed word in the part
      
      I_RX_EOP             => I_RX_EOP_N, -- RX_EOP with positive logic
      
      REG_RX_SOF           => reg_rx_sof_n, -- Registered RX_SOF
      REG_RX_SOP           => reg_rx_sop_n, -- Registered RX_SOP
      REG_RX_EOP           => reg_rx_eop_n, -- Registered RX_EOP
      REG_RX_EOF           => reg_rx_eof_n, -- Registered RX_EOF
      REG_RX_SRC_RDY       => reg_rx_src_rdy_n, -- Registered RX_SRC_RDY
      REG_RX_REM           => reg_rx_rem, -- Registered RX_REM
      REG2_RX_SOP_LV       => reg2_rx_sop_n_lv, -- 2x registered RX_SOP "last valid" (sampled when transmission was in progress)
      REG2_RX_EOP          => reg2_rx_eop_n, -- 2x registered RX_EOP
      
      -- outputs
      RX_READY             => ready, -- Cutter is ready to receive new data; otherwise RX wait cycle is required
      CUT_PROGRESS         => cut_progress, -- Extraction of predefined bytes in progress
      CUT_EXTRACTED        => cut_extracted, -- Extraction of predefined bytes done
      SEL_REORDER          => sel_reorder, -- Determines whether to choose original or reordered data
      SEL_REORDER_END      => sel_reorder_end, -- Determines which version of reordered data to choose
      CNT_AUX_EN           => cnt_aux_en, -- Enables cnt_aux (auxiliary counter in reorder logic module)
      SEL_AUX0_EN          => sel_aux0_en, -- Determines which vector of enable signals to use for Auxiliary register 0
      SEL_AUX1_EN          => sel_aux1_en, -- Determines which vector of enable signals to use for Auxiliary register 1
      CNT_OUTPUT_EN        => cnt_output_en, -- Enables cnt_output (output counter in reorder logic module)
      I_TX_DATA_EN         => I_TX_DATA_en, -- Enables output register
      
      GENERATED_TX_SOF     => generated_tx_sof_n, -- Generated TX_SOF
      GENERATED_TX_SOP     => generated_tx_sop_n, -- Generated TX_SOP
      GENERATED_TX_EOP     => generated_tx_eop_n, -- Generated TX_EOP
      GENERATED_TX_EOF     => generated_tx_eof_n, -- Generated TX_EOF
      GENERATED_TX_SRC_RDY => generated_tx_src_rdy_n, -- Generated TX_SRC_RDY
      GENERATED_TX_REM     => generated_tx_rem -- Generated TX_REM
   );


-- -----------------------------------------------------------------------------
--                                  FSM VALID
-- -----------------------------------------------------------------------------
   Fsm_valid_i: entity work.fsm_valid
   port map(
      RESET         => RESET, -- Asynchronous reset
      CLK           => CLK,

      -- inputs
      SYN_RESET     => reg_rx_eof_n, -- Synchronous reset
      CUT_EXTRACTED => cut_extracted, -- Extraction of predefined bytes done

      -- outputs
      CUT_VLD       => CUT_VLD -- Cut data is valid (one cycle)
   );


-- -----------------------------------------------------------------------------
--                               CUT DATA LOGIC
-- -----------------------------------------------------------------------------
   Cut_data_i: entity work.cut_data
   generic map(
      DATA_WIDTH    => DATA_WIDTH, -- FrameLink width
      DATA_BYTES    => DATA_BYTES, -- Width of data bus in bytes
      PART          => PART, -- Number of processed part, 0 = first part
      MAX_PARTS     => MAX_PARTS, -- Maximum number of frame parts
      MAX_PART_SIZE => MAX_PART_SIZE, -- Maximal size of one frame part (in bytes)
      OFFSET        => OFFSET, -- Position from SOP, 0 = first byte
      SIZE          => SIZE  -- Extracted block size, greater than 0
   )
   port map(
      CLK          => CLK,

      -- inputs
      DATA         => reg_rx_data, -- Input FrameLink data
      PART_NUM     => cnt_part, -- Number of currently processed part
      WORD_NUM     => cnt_word, -- Number of currently processed word in the part
      TRANSMIT_PROGRESS => transmit_progress, -- Currently transmit in progress?

      -- outputs
      CUT_DATA  => CUT_DATA
   );



   Modify_logic: if (MODIFY = true) generate
-- -----------------------------------------------------------------------------
--                                REORDER LOGIC
-- -----------------------------------------------------------------------------
   Reorder_i: entity work.reorder
   generic map(
      DATA_WIDTH    => DATA_WIDTH, -- FrameLink width
      DATA_BYTES    => DATA_BYTES, -- Width of data bus in bytes
      SIZE          => SIZE, -- Extracted block size, greater than 0

      START_WORD    => START_WORD, -- Serial number of word containing first byte of data to cut
      END_WORD      => END_WORD, -- Serial number of word containing last byte of data to cut
      START_BYTE    => START_BYTE, -- Serial number of first byte of data to cut in START_WORD
      END_BYTE      => END_BYTE, -- Serial number of last byte of data to cut in END_WORD
      RX_WAIT_NEED  => RX_WAIT_NEED -- Flag whether extra empty beat is needed to transmit all remaining reordered data
   )
   port map(
      RESET             => RESET, -- Asynchronous reset
      CLK               => CLK,

      -- inputs
      DATA_IN           => reg_rx_data, -- Input data
      
      RX_READY          => ready, -- Cutter is ready to receive new data; otherwise RX wait cycle is required
      TRANSMIT_PROGRESS => transmit_progress, -- Transmit in progress
      TRANSMIT_PAUSE    => transmit_pause, -- Transmit paused (is going to continue)
      SEL_REORDER       => sel_reorder, -- Determines whether to choose original or reordered data
      SEL_REORDER_END   => sel_reorder_end, -- Determines which version of reordered data to choose
      SEL_AUX0_EN       => sel_aux0_en, -- Determines which vector of enable signals to use for Auxiliary register 0
      SEL_AUX1_EN       => sel_aux1_en, -- Determines which vector of enable signals to use for Auxiliary register 1
      RX_EOF            => reg_rx_eof_n, -- Resets all counters
      REG_RX_EOP        => reg_rx_eop_n, -- Registered RX_EOP
      REG2_RX_EOP       => reg2_rx_eop_n, -- 2x registered RX_EOP
      REG_RX_SRC_RDY    => reg_rx_src_rdy_n, -- Registered RX_SRC_RDY
      TX_DST_RDY        => I_TX_DST_RDY_N, -- TX_DST_RDY
      CNT_AUX_EN        => cnt_aux_en, -- Enables cnt_aux
      CNT_OUTPUT_EN     => cnt_output_en, -- Enalbes cnt_output
      I_TX_DATA_EN      => I_TX_DATA_en, -- Enables output register
 
      -- outputs
      DATA_OUT          => I_TX_DATA -- Output data

   );
      

   -- --------------------------------------------------------------------------
   --                     "MODIFY" OUTPUT SIGNALS MAPPING
   -- --------------------------------------------------------------------------

      -- TX_REM registers
      process(CLK) -- no need for RESET
      begin
         if (CLK'event and CLK = '1') then
            reg_generated_tx_rem <= generated_tx_rem;
         end if;
      end process;
      
      process(CLK) -- no need for RESET
      begin
         if (CLK'event and CLK = '1') then
            I_TX_REM <= reg_generated_tx_rem;
         end if;
      end process;
      
      -- TX_SRC_RDY_N registers
      process(CLK,RESET)
      begin
         if (RESET = '1') then
            reg_generated_tx_src_rdy_n <= '0';
         elsif (CLK'event and CLK = '1') then
            reg_generated_tx_src_rdy_n <= generated_tx_src_rdy_n;
         end if;
      end process;

      process(CLK,RESET)
      begin
         if (RESET = '1') then
            I_TX_SRC_RDY_N <= '0';
         elsif (CLK'event and CLK = '1') then
            I_TX_SRC_RDY_N <= reg_generated_tx_src_rdy_n;
         end if;
      end process;
      
      
      -- other TX signals
      process(CLK,RESET)
      begin
         if (RESET = '1') then
            reg_generated_tx_sof_n <= '0';
            reg_generated_tx_sop_n <= '0';
            reg_generated_tx_eop_n <= '0';
            reg_generated_tx_eof_n <= '0';
         elsif (CLK'event and CLK = '1') then
            reg_generated_tx_sof_n <= generated_tx_sof_n;
            reg_generated_tx_sop_n <= generated_tx_sop_n;
            reg_generated_tx_eop_n <= generated_tx_eop_n;
            reg_generated_tx_eof_n <= generated_tx_eof_n;
         end if;
      end process;

      process(CLK,RESET)
      begin
         if (RESET = '1') then
            I_TX_SOF_N <= '0';
            I_TX_SOP_N <= '0';
            I_TX_EOP_N <= '0';
            I_TX_EOF_N <= '0';
         elsif (CLK'event and CLK = '1') then
            I_TX_SOF_N <= reg_generated_tx_sof_n;
            I_TX_SOP_N <= reg_generated_tx_sop_n;
            I_TX_EOP_N <= reg_generated_tx_eop_n;
            I_TX_EOF_N <= reg_generated_tx_eof_n;
         end if;
      end process;


   end generate;-- Modify_logic


-- -----------------------------------------------------------------------------
--                    "DON'T MODIFY" OUTPUT SIGNALS MAPPING
-- -----------------------------------------------------------------------------
   Dont_modify_logic: if (MODIFY = false) generate

      I_TX_DATA      <= I_RX_DATA;
      I_TX_REM       <= I_RX_REM;
      I_TX_SRC_RDY_N <= I_RX_SRC_RDY_N;
   -- I_RX_DST_RDY_N is assigned in OUTPUT SIGNAL MAPPING
      I_TX_SOP_N     <= I_RX_SOP_N;
      I_TX_EOP_N     <= I_RX_EOP_N;
      I_TX_SOF_N     <= I_RX_SOF_N;
      I_TX_EOF_N     <= I_RX_EOF_N;

   end generate;-- Dont_modify_logic


-- -----------------------------------------------------------------------------
--                         COMMON OUTPUT SIGNALS MAPPING
-- -----------------------------------------------------------------------------
   I_RX_DST_RDY_N <= ready and I_TX_DST_RDY_N;

end architecture full;

-- TODO-list
-- nefunguje zastaveni cele komponenty, pokud je TX_DST_RDY_N aktivni bezprostredne po ukonceni framu (a zacina se hned vysilat dalsi frame)
-- dodelat generovani REM
-- napred udelat SOP a EOP, REM generovat az podle toho
-- udelat SOF a EOF podle SOPu a EOPu
-- EOP: buguje pri 2/1 vs 11/2 v sm_idle
