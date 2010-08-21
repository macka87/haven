-- header_rearranger.vhd: FrameLink unit that cuts off the first
--                        half-word of a frame header and rearranges the
--                        rest of the header, so that it conforms to the
--                        FrameLink protocol
-- Copyright (C) 2008 CESNET
-- Author(s): Ondrej Lengal <xlenga00@stud.fit.vutbr.cz>
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

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity HEADER_REARRANGER is
   generic
   (
      -- the data width of the FrameLink protocol
      DATA_WIDTH     : integer := 64
   );
   port
   (
      -- common signals
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      -- "frame contains header" signal
      -- This signal is used to indicate that this frame contains a
      -- header, the structure of which is to be rearranged. This signal is
      -- valid when the SOF_N input FrameLink signal is valid
      FRAME_HAS_HEADER  : in  std_logic;

      -- input FrameLink
      RX_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM            : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N          : in  std_logic;
      RX_EOF_N          : in  std_logic;
      RX_SOP_N          : in  std_logic;
      RX_EOP_N          : in  std_logic;
      RX_SRC_RDY_N      : in  std_logic;
      RX_DST_RDY_N      : out std_logic;
      
      -- output FrameLink
      TX_DATA           : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM            : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N          : out std_logic;
      TX_EOF_N          : out std_logic;
      TX_SOP_N          : out std_logic;
      TX_EOP_N          : out std_logic;
      TX_SRC_RDY_N      : out std_logic;
      TX_DST_RDY_N      : in  std_logic
   );
end entity HEADER_REARRANGER;

-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture ARCH of HEADER_REARRANGER is

-- ==========================================================================
--                                   TYPES
-- ==========================================================================

   -- type for FSM states
   type states is (STATE_IDLE, STATE_NOT_REARRANGING, STATE_REARRANGING);

-- ==========================================================================
--                                 CONSTANTS
-- ==========================================================================

   -- width of the FrameLink REM signal
   constant FL_REM_WIDTH      : integer := log2(DATA_WIDTH/8);

   -- width of the input FrameLink register (DATA, REM, EOF_N, SOP_N,
   -- EOP_N, FRAME_HAS_HEADER)
   constant REG_INPUT_WIDTH   : integer := DATA_WIDTH + FL_REM_WIDTH + 4;

   -- width of the previous data register (DATA,REM,SOF_N,EOF_N,SOP_N,EOP_N)
   constant REG_PREV_WIDTH    : integer := DATA_WIDTH + FL_REM_WIDTH + 4;

-- ==========================================================================
--                                  SIGNALS
-- ==========================================================================

   -- input FrameLink
   signal fl_in_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_in_rem        : std_logic_vector(FL_REM_WIDTH-1 downto 0);
   signal fl_in_sof_n      : std_logic;
   signal fl_in_eof_n      : std_logic;
   signal fl_in_sop_n      : std_logic;
   signal fl_in_eop_n      : std_logic;
   signal fl_in_src_rdy_n  : std_logic;
   signal fl_in_dst_rdy_n  : std_logic;
   -- input "Frame has header" signal
   signal in_frm_has_hdr   : std_logic;

   -- output FrameLink
   signal fl_out_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal fl_out_rem       : std_logic_vector(FL_REM_WIDTH-1 downto 0);
   signal fl_out_sof_n     : std_logic;
   signal fl_out_eof_n     : std_logic;
   signal fl_out_sop_n     : std_logic;
   signal fl_out_eop_n     : std_logic;
   signal fl_out_src_rdy_n : std_logic;
   signal fl_out_dst_rdy_n : std_logic;

   -- the signal that the header rearranger can accept input data
   signal can_accept_data     : std_logic;

   -- the signal that the header rearranger can transmit data
   signal can_transmit_data   : std_logic;

   -- register for storage of input data
   signal reg_input     : std_logic_vector(REG_INPUT_WIDTH-1 downto 0)
                        := (others => '0');
   signal reg_input_in  : std_logic_vector(REG_INPUT_WIDTH-1 downto 0);
   signal reg_input_we  : std_logic;

   -- register for storage of input FrameLink's SOF_N (this register needs a
   -- RESET)
   signal reg_input_sof_n     : std_logic;
   signal reg_input_sof_n_in  : std_logic;
   signal reg_input_sof_n_we  : std_logic;

   -- register that determines whether the input register is full
   signal reg_input_full      : std_logic;
   signal reg_input_full_in   : std_logic;
   signal reg_input_full_we   : std_logic;

   -- pipeline input FrameLink
   signal ppl_in_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal ppl_in_rem          : std_logic_vector(FL_REM_WIDTH-1 downto 0);
   signal ppl_in_sof_n        : std_logic;
   signal ppl_in_eof_n        : std_logic;
   signal ppl_in_sop_n        : std_logic;
   signal ppl_in_eop_n        : std_logic;
   -- pipeline input "Frame has header" signal
   signal ppl_in_frm_has_hdr  : std_logic;

   -- inverter of the MSB of the REM
   signal hdr_last_rem_msb_not_in   : std_logic;
   signal hdr_last_rem_msb_not_out  : std_logic;

   -- REM for the last word of the header
   signal hdr_last_rem        : std_logic_vector(FL_REM_WIDTH-1 downto 0);

   -- multiplexer for choosing correct REM MSB to be stored to the previous
   -- data register
   signal mux_prev_rem_msb          : std_logic;
   signal mux_prev_rem_msb_pld_hdr  : std_logic;
   signal mux_prev_rem_msb_hdr_last : std_logic;
   signal mux_prev_rem_msb_sel      : std_logic;

   -- possibly modified REM signal to be stored to the previous word register
   signal reg_prev_in_rem     : std_logic_vector(FL_REM_WIDTH-1 downto 0);

   -- previous word register
   signal reg_prev      : std_logic_vector(REG_PREV_WIDTH-1 downto 0)
                        := (others => '0');
   signal reg_prev_in   : std_logic_vector(REG_PREV_WIDTH-1 downto 0);
   signal reg_prev_we   : std_logic;

   -- register that determines whether the previous word register is full
   signal reg_prev_full       : std_logic;
   signal reg_prev_full_in    : std_logic;
   signal reg_prev_full_we    : std_logic;

   -- pipeline output FrameLink
   signal ppl_out_data  : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal ppl_out_rem   : std_logic_vector(FL_REM_WIDTH-1 downto 0);
   signal ppl_out_sof_n : std_logic;
   signal ppl_out_eof_n : std_logic;
   signal ppl_out_sop_n : std_logic;
   signal ppl_out_eop_n : std_logic;

   -- output data multiplexer control register
   signal reg_next_data_sel      : std_logic := '0';
   signal reg_next_data_sel_in   : std_logic;
   signal reg_next_data_sel_we   : std_logic;

   -- output data multiplexer
   signal mux_out_data           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mux_out_data_in_pld    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mux_out_data_in_hdr    : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal mux_out_data_sel       : std_logic;

   -- output REM multiplexer
   signal mux_out_rem               : std_logic_vector(FL_REM_WIDTH-1 downto 0);
   signal mux_out_rem_in_pld_hdr    : std_logic_vector(FL_REM_WIDTH-1 downto 0);
   signal mux_out_rem_in_hdr_last   : std_logic_vector(FL_REM_WIDTH-1 downto 0);
   signal mux_out_rem_sel           : std_logic;

   -- output EOP_N multiplexer
   signal mux_out_eop_n             : std_logic;
   signal mux_out_eop_n_in_mat      : std_logic;
   signal mux_out_eop_n_in_premat   : std_logic;
   signal mux_out_eop_n_sel         : std_logic;

   -- the register that holds the value whether the output is to be suspended
   signal reg_output_suspensor      : std_logic := '0';
   signal reg_output_suspensor_in   : std_logic;
   signal reg_output_suspensor_we   : std_logic;

   -- FSM input signals
   signal fsm_in_sof_n        : std_logic;
   signal fsm_in_eof_n        : std_logic;
   signal fsm_in_eop_n        : std_logic;
   signal fsm_in_rem_msb      : std_logic;
   signal fsm_in_frm_has_hdr  : std_logic;
   signal fsm_in_enable       : std_logic;

   -- FSM output signals
   signal fsm_out_reg_next_data_sel_in    : std_logic;
   signal fsm_out_mux_prev_rem_sel        : std_logic;
   signal fsm_out_mux_out_rem_sel         : std_logic;
   signal fsm_out_mux_out_eop_n_sel       : std_logic;
   signal fsm_out_reg_output_suspensor_in : std_logic;
   signal fsm_out_is_rearranging          : std_logic;

   -- FSM states
   signal fsm_state        : states;
   signal fsm_next_state   : states;

   -- pipeline enable signal
   signal pipe_enable      : std_logic;

   -- the FSM is rearranging state signal
   signal is_rearranging   : std_logic;

begin

   -- mapping of input signals
   fl_in_data        <= RX_DATA;
   fl_in_rem         <= RX_REM;
   fl_in_sof_n       <= RX_SOF_N;
   fl_in_eof_n       <= RX_EOF_N;
   fl_in_sop_n       <= RX_SOP_N;
   fl_in_eop_n       <= RX_EOP_N;
   fl_in_src_rdy_n   <= RX_SRC_RDY_N;
   RX_DST_RDY_N      <= fl_in_dst_rdy_n;

   -- the "frame has header" signal
   in_frm_has_hdr    <= FRAME_HAS_HEADER;

   -- mapping of output signals
   TX_DATA           <= fl_out_data;
   TX_REM            <= fl_out_rem;
   TX_SOF_N          <= fl_out_sof_n;
   TX_EOF_N          <= fl_out_eof_n;
   TX_SOP_N          <= fl_out_sop_n;
   TX_EOP_N          <= fl_out_eop_n;
   TX_SRC_RDY_N      <= fl_out_src_rdy_n;
   fl_out_dst_rdy_n  <= TX_DST_RDY_N;

   -- the header rearranger is ready signal
   fl_in_dst_rdy_n   <= reg_input_full AND fl_out_dst_rdy_n AND
                        (NOT pipe_enable);

   -- the signal that the header rearranger can accept input data
   can_accept_data   <= NOT (fl_in_dst_rdy_n OR fl_in_src_rdy_n);

   -- the signal that the header rearranger can transmit data
   can_transmit_data <= NOT (fl_out_src_rdy_n OR fl_out_dst_rdy_n);


   reg_input_in   <= in_frm_has_hdr & fl_in_eof_n & fl_in_sop_n &
                     fl_in_eop_n & fl_in_rem & fl_in_data; 
   reg_input_we   <= can_accept_data;

   -- register for storage of input FrameLink and FRAME_HAS_HEADER signal
   reg_inputp : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_input_we = '1') then
            reg_input <= reg_input_in;
         end if;
      end if;
   end process;

   reg_input_sof_n_in <= fl_in_sof_n;
   reg_input_sof_n_we <= can_accept_data;

   -- register for storage of input FrameLink's SOF_N
   reg_input_sof_np : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            -- reset sets the content to 1s, because of inverted FrameLink
            -- control signals
            reg_input_sof_n <= '1';
         elsif (reg_input_sof_n_we = '1') then
            reg_input_sof_n <= reg_input_sof_n_in;
         end if;
      end if;
   end process;


   reg_input_full_in    <= can_accept_data OR (reg_input_full AND
                                               (NOT pipe_enable));
   reg_input_full_we    <= '1';

   -- register that determines whether the input register is full
   reg_input_fullp : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_input_full <= '0';
         elsif (reg_input_full_we = '1') then
            reg_input_full <= reg_input_full_in;
         end if;
      end if;
   end process;


   -- mapping of pipeline input signals
   ppl_in_data          <= reg_input(DATA_WIDTH-1 downto 0);
   ppl_in_rem           <= reg_input(DATA_WIDTH+FL_REM_WIDTH-1 downto DATA_WIDTH);
   ppl_in_eop_n         <= reg_input(DATA_WIDTH+FL_REM_WIDTH);
   ppl_in_sop_n         <= reg_input(DATA_WIDTH+FL_REM_WIDTH+1);
   ppl_in_eof_n         <= reg_input(DATA_WIDTH+FL_REM_WIDTH+2);
   ppl_in_sof_n         <= reg_input_sof_n;
   ppl_in_frm_has_hdr   <= reg_input(DATA_WIDTH+FL_REM_WIDTH+3);

   -- pipeline enable signal
   pipe_enable    <= reg_input_full AND ((NOT reg_prev_full) OR
                                         (NOT fl_out_dst_rdy_n));
                     
   -- inverter of the MSB REM signal
   hdr_last_rem_msb_not_in    <= ppl_in_rem(FL_REM_WIDTH-1);
   hdr_last_rem_msb_not_out   <= NOT hdr_last_rem_msb_not_in;

   hdr_last_rem               <= hdr_last_rem_msb_not_out &
                                 ppl_in_rem(FL_REM_WIDTH-2 downto 0);

   mux_prev_rem_msb_pld_hdr   <= ppl_in_rem(FL_REM_WIDTH-1);
   mux_prev_rem_msb_hdr_last  <= hdr_last_rem_msb_not_out;
   mux_prev_rem_msb_sel       <= fsm_out_mux_prev_rem_sel;

   -- multiplexer that chooses whether the original REM MSB or the modified
   -- one should be used
   mux_prev_rem_msbp : process (mux_prev_rem_msb_sel, mux_prev_rem_msb_pld_hdr,
                                mux_prev_rem_msb_hdr_last)
   begin
      case mux_prev_rem_msb_sel is
         -- send the original REM MSB (normal payload or header word)
         when '0' => mux_prev_rem_msb <= mux_prev_rem_msb_pld_hdr;
         -- send modified REM MSB (last header word)
         when '1' => mux_prev_rem_msb <= mux_prev_rem_msb_hdr_last;
         -- else
         when others => null;
      end case;
   end process;

   reg_prev_in_rem <= mux_prev_rem_msb & ppl_in_rem(FL_REM_WIDTH-2 downto 0);

   reg_prev_in <= ppl_in_sof_n & ppl_in_eof_n & ppl_in_sop_n &
                  ppl_in_eop_n & reg_prev_in_rem & ppl_in_data;
   reg_prev_we <= pipe_enable;

   -- register for storage of previous word
   reg_prev_p : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_prev_we = '1') then
            reg_prev <= reg_prev_in;
         end if;
      end if;
   end process;

   reg_prev_full_in    <= pipe_enable OR (reg_prev_full AND
                                          (NOT can_transmit_data));
   reg_prev_full_we    <= '1';

   -- register that determines whether the register for previous word is full
   reg_prev_fullp : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            reg_prev_full <= '0';
         elsif (reg_prev_full_we = '1') then
            reg_prev_full <= reg_prev_full_in;
         end if;
      end if;
   end process;

   -- mapping of pipeline output signals
   ppl_out_data      <= reg_prev(DATA_WIDTH-1 downto 0);
   ppl_out_rem       <= reg_prev(DATA_WIDTH+FL_REM_WIDTH-1 downto DATA_WIDTH);
   ppl_out_eop_n     <= reg_prev(DATA_WIDTH+FL_REM_WIDTH);
   ppl_out_sop_n     <= reg_prev(DATA_WIDTH+FL_REM_WIDTH+1);
   ppl_out_eof_n     <= reg_prev(DATA_WIDTH+FL_REM_WIDTH+2);
   ppl_out_sof_n     <= reg_prev(DATA_WIDTH+FL_REM_WIDTH+3);


   reg_next_data_sel_in <= fsm_out_reg_next_data_sel_in;
   reg_next_data_sel_we <= pipe_enable;

   -- the register that controls the output data multiplexer
   reg_next_data_selp : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_next_data_sel_we = '1') then
            reg_next_data_sel <= reg_next_data_sel_in;
         end if;
      end if;
   end process;


   mux_out_data_sel     <= reg_next_data_sel;
   mux_out_data_in_pld  <= ppl_out_data;
   mux_out_data_in_hdr  <= ppl_in_data(DATA_WIDTH/2-1 downto 0) &
                           ppl_out_data(DATA_WIDTH-1 downto DATA_WIDTH/2);

   -- multiplexer for data output
   mux_out_datap : process (mux_out_data_sel, mux_out_data_in_pld,
                            mux_out_data_in_hdr)
   begin
      case mux_out_data_sel is
         -- send original input to the output
         when '0' => mux_out_data <= mux_out_data_in_pld;
         -- send rearranged input to the output
         when '1' => mux_out_data <= mux_out_data_in_hdr;
         -- else
         when others => null;
      end case;
   end process;



   mux_out_rem_in_pld_hdr     <= ppl_out_rem;
   mux_out_rem_in_hdr_last    <= hdr_last_rem;
   mux_out_rem_sel            <= fsm_out_mux_out_rem_sel;

   -- multiplexer for REM output
   mux_out_remp : process (mux_out_rem_sel, mux_out_rem_in_pld_hdr,
                           mux_out_rem_in_hdr_last)
   begin
      case mux_out_rem_sel is
         -- send previous word's REM (either modified or not) to the output
         when '0' => mux_out_rem <= mux_out_rem_in_pld_hdr;
         -- send this word's modified REM header to the output
         when '1' => mux_out_rem <= mux_out_rem_in_hdr_last;
         -- else
         when others => null;
      end case;
   end process;

   
   mux_out_eop_n_in_mat    <= ppl_out_eop_n;
   mux_out_eop_n_in_premat <= '0';
   mux_out_eop_n_sel       <= fsm_out_mux_out_eop_n_sel;

   -- multiplexer for output FrameLink EOP_N signal
   mux_out_fl_sigp : process (mux_out_eop_n_sel, mux_out_eop_n_in_mat,
                              mux_out_eop_n_in_premat)
   begin
      case mux_out_eop_n_sel is
         -- send mature end of part
         when '0' => mux_out_eop_n <= mux_out_eop_n_in_mat;
         -- send premature end of part
         when '1' => mux_out_eop_n <= mux_out_eop_n_in_premat;
         -- else
         when others => null;
      end case;
   end process;


   reg_output_suspensor_in <= fsm_out_reg_output_suspensor_in;
   reg_output_suspensor_we <= pipe_enable;

   -- the register that holds the value whether the output should be suspended
   reg_output_suspensorp : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (reg_output_suspensor_we = '1') then
            reg_output_suspensor <= reg_output_suspensor_in;
         end if;
      end if;
   end process;

   -- mapping of output FrameLink
   fl_out_data       <= mux_out_data;
   fl_out_rem        <= mux_out_rem;
   fl_out_sof_n      <= ppl_out_sof_n;
   fl_out_eof_n      <= ppl_out_eof_n;
   fl_out_sop_n      <= ppl_out_sop_n;
   fl_out_eop_n      <= mux_out_eop_n;

   -- is the header rearranger ready to transmit data?
   fl_out_src_rdy_n  <= (NOT (reg_prev_full AND (NOT reg_output_suspensor)))
                        OR (is_rearranging AND (NOT reg_input_full));

   is_rearranging       <= fsm_out_is_rearranging;

   -- mapping of FSM input signals
   fsm_in_sof_n         <= ppl_in_sof_n;
   fsm_in_eof_n         <= ppl_in_eof_n;
   fsm_in_eop_n         <= ppl_in_eop_n;
   fsm_in_rem_msb       <= ppl_in_rem(FL_REM_WIDTH-1);
   fsm_in_frm_has_hdr   <= ppl_in_frm_has_hdr;
   fsm_in_enable        <= pipe_enable;

   -- FSM state register
   fsm_statep : process (CLK)
   begin
      if (rising_edge(CLK)) then
         if (RESET = '1') then
            fsm_state <= STATE_IDLE;
         else
            fsm_state <= fsm_next_state;
         end if;
      end if;
   end process;

   -- FSM next state logic
   fsm_next_statep : process (fsm_state, fsm_in_enable, fsm_in_sof_n, fsm_in_eof_n,
                              fsm_in_eop_n, fsm_in_rem_msb, fsm_in_frm_has_hdr)
   begin
      fsm_next_state                   <= STATE_IDLE;

      case fsm_state is

         ---------------------- IDLE start --------------------
         when STATE_IDLE =>
         -- FSM is idle, waiting for next FrameLink frame
            if (fsm_in_enable = '1') then
            -- if the header rearranger can accept data
               if (fsm_in_sof_n = '0') then
               -- if a new frame arrives
                  if (fsm_in_frm_has_hdr = '1') then
                  -- if the frame has a header that needs to be rearranged

                     if (fsm_in_eop_n = '0') then
                     -- if the frame part immediately ends

                        -- next parts of the frame do not need to be
                        -- rearranged
                        fsm_next_state <= STATE_NOT_REARRANGING;
                     else
                     -- if the frame part is longer

                        -- next parts of the frame do not need to be
                        -- rearranged
                        fsm_next_state <= STATE_REARRANGING;
                     end if;
                  else
                  -- if the frame does not contain a header

                     if (fsm_in_eof_n = '0') then
                     -- if the frame immediately ends

                        -- the frame ends
                        fsm_next_state <= STATE_IDLE;
                     else
                     -- if the frame is longer

                        -- do not rearrange
                        fsm_next_state <= STATE_NOT_REARRANGING;
                     end if;
                  end if;
               else
               -- if nothing arrives
                  fsm_next_state <= STATE_IDLE;
               end if;
            else
            -- if the header rearranger cannot accept data
               fsm_next_state <= fsm_state;
            end if;
         ---------------------- IDLE end ----------------------

         ----------------- REARRANGING start ------------------
         when STATE_REARRANGING =>
         -- FSM is rearranging the data
            if (fsm_in_enable = '1') then
            -- if the header rearranger can accept data
               if (fsm_in_eop_n = '0') then
               -- if the frame part ends
                  -- other parts follow, so do not arrange them
                  fsm_next_state <= STATE_NOT_REARRANGING;
               else
               -- if the frame part is longer
                  -- continue rearranging
                  fsm_next_state <= STATE_REARRANGING;
               end if;
            else
            -- if the header rearranger cannot accept data
               fsm_next_state <= fsm_state;
            end if;
         ------------------ REARRANGING end -------------------

         --------------- NOT_REARRANGING start ----------------
         when STATE_NOT_REARRANGING =>
         -- FSM is not rearranging the data -> the input is pipelined to the
         -- output
            if (fsm_in_enable = '1') then
            -- if the header rearranger can accept data
               if (fsm_in_eof_n = '0') then
               -- if the frame ends
                  -- frame ends
                  fsm_next_state <= STATE_IDLE;
               else
               -- if the frame doesn't end
                  -- continue not rearranging
                  fsm_next_state <= STATE_NOT_REARRANGING;
               end if;
            else
            -- if the header rearranger cannot accept data
               fsm_next_state <= fsm_state;
            end if;
         ---------------- NOT_REARRANGING end -----------------

         when others => null;
         -- else

      end case;
   end process;


   -- FSM output logic
   fsm_output_logicp : process (fsm_state, fsm_in_sof_n, fsm_in_eof_n,
                                fsm_in_eop_n, fsm_in_rem_msb, fsm_in_frm_has_hdr)
   begin
      fsm_out_reg_next_data_sel_in     <= '0';
      fsm_out_mux_prev_rem_sel         <= '0';
      fsm_out_mux_out_rem_sel          <= '0';
      fsm_out_mux_out_eop_n_sel        <= '0';
      fsm_out_reg_output_suspensor_in  <= '0';
      fsm_out_is_rearranging           <= '0';


      case fsm_state is
         when STATE_IDLE =>
         -- FSM is idle, waiting for next FrameLink frame

            if (fsm_in_sof_n = '0') then
            -- if a new frame arrives
               if (fsm_in_frm_has_hdr = '1') then
               -- if the frame has a header that needs to be rearranged

                  -- start rearranging
                  fsm_out_reg_next_data_sel_in  <= '1';
                  -- FSM is rearranging
                  fsm_out_is_rearranging        <= '1';

                  if (fsm_in_eop_n = '0') then
                  -- if the frame part immediately ends

                     -- store original REM with the data
                     fsm_out_mux_prev_rem_sel   <= '1';
                  else
                  -- if the frame part is longer

                     -- store original REM with the data
                     fsm_out_mux_prev_rem_sel   <= '0';
                  end if;
               else
               -- if the frame does not contain a header

                  -- do not rearrange
                  fsm_out_reg_next_data_sel_in  <= '0';
                  -- store original REM with the data
                  fsm_out_mux_prev_rem_sel      <= '0';
                  -- FSM is not rearranging
                  fsm_out_is_rearranging        <= '0';
               end if;
            end if;

         when STATE_REARRANGING =>
         -- FSM is rearranging the data

            -- continue rearranging
            fsm_out_reg_next_data_sel_in  <= '1';
            -- store modified REM with the data
            fsm_out_mux_prev_rem_sel      <= '1';
            -- FSM is rearranging
            fsm_out_is_rearranging        <= '1';

            if (fsm_in_eop_n = '0') then
            -- if the frame part ends
               if (fsm_in_rem_msb = '1') then
               -- if the valid part of the word is more than a half-word

                  -- no need to suspend the header rearranger output
                  fsm_out_reg_output_suspensor_in  <= '0';
                  -- take original "end of part" signal
                  fsm_out_mux_out_eop_n_sel        <= '0';
                  -- take the previous modified REM signal
                  fsm_out_mux_out_rem_sel          <= '0';
               else
               -- if the valid part of the word is a half-word or less

                  -- suspend the header rearranger output
                  fsm_out_reg_output_suspensor_in  <= '1';
                  -- signal "end of part" to the destination
                  fsm_out_mux_out_eop_n_sel        <= '1';
                  -- take the modified input REM signal
                  fsm_out_mux_out_rem_sel          <= '1';
               end if;
            else
            -- if the frame part is longer

               -- store original REM with the data
               fsm_out_mux_prev_rem_sel <= '0';
            end if;

         when STATE_NOT_REARRANGING =>
         -- FSM is not rearranging the data -> the input is pipelined to the
         -- output

            -- do not rearrange
            fsm_out_reg_next_data_sel_in  <= '0';
            -- store original REM with the data
            fsm_out_mux_prev_rem_sel      <= '0';
            -- FSM is not rearranging
            fsm_out_is_rearranging        <= '0';

         when others => null;
         -- else

      end case;
   end process;

end architecture ARCH;
