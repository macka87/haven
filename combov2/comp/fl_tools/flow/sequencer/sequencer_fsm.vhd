-- sequencer_fsm.vhd: FrameLink Sequencer finite state machine
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_SEQUENCER_FSM is
   generic(
      -- Number of input interfaces
      INPUT_COUNT       : integer;
      -- Size of the ticket
      TICKET_WIDTH      : integer
   );
   port(
      -- Common signals
      -- clock sigal
      CLK               : in std_logic;
      -- asynchronous reset, active in '1'
      RESET             : in std_logic;

      -- FSM input signals
      -- vector with information what input is ready
      TICKET_RDY        : in std_logic_vector(INPUT_COUNT-1 downto 0);
      -- transferring FL_EOF_N signal
      FL_EOF_N          : in std_logic;
      -- information whether the output is ready for the transmission
      OUTPUT_RDY_N      : in std_logic;
      -- information whether the selected input FIFO is ready
      SRC_RDY_IN_N      : in std_logic;

      -- FSM output signals
      -- signal to control multiplexors
      MX_SEL            : out std_logic_vector(log2(INPUT_COUNT)-1 downto 0);
      -- number of the actual ticket
      TICKET_NUMBER     : out std_logic_vector(TICKET_WIDTH-1 downto 0);
      -- this signal is set to 1 after new ticket number is set
      TICKET_EXCHANGE   : out std_logic;
      -- vector to control input activeness
      INPUT_ACTIVE      : out std_logic_vector(INPUT_COUNT-1 downto 0);
      -- output FIFO src rdy control
      SRC_RDY_OUT_N     : out std_logic
   ); 
end entity FL_SEQUENCER_FSM;

-- ----------------------------------------------------------------------------
--                         Architecture declaration
-- ----------------------------------------------------------------------------
architecture FL_SEQUENCER_FSM_ARCH of FL_SEQUENCER_FSM is
   -- Signal declaration
   -- Control FSM declaration
   type t_states is (st_idle, st_start, st_transmission);
   signal present_state, next_state: t_states;

   -- Select register signals
   signal reg_sel : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal reg_sel_we : std_logic;
   -- If at least one signal is ready, this signal is set to 1
   signal input_rdy     : std_logic;
   -- Ticket counter
   signal cnt_ticket : std_logic_vector(TICKET_WIDTH-1 downto 0);
   signal cnt_ticket_en : std_logic;

begin

   INPUT_ACTIVE <= reg_sel;

   -- process to control input_rdy signal -------------------------------------
   gen_orp : process(TICKET_RDY)
      variable or_int : std_logic;
   begin
      or_int := '0';

      for k in 0 to TICKET_RDY'length -1 loop
         or_int := or_int or TICKET_RDY(k);
      end loop;

      input_rdy <= or_int;
   end process;

   -- register to control select signal for Sequencer's multiplexors
   reg_selp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_sel <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (reg_sel_we = '1') then
            reg_sel <= TICKET_RDY;
         end if;
      end if;
   end process;

   -- mx_sel signal encoder
   gen_enc: entity work.GEN_ENC
      generic map (
         ITEMS       => INPUT_COUNT
      )
      port map (
         DI          => reg_sel,
         ADDR        => MX_SEL
      );

   -- cnt_ticket counter
   cnt_ticketp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_ticket <= (others => '0');
      elsif (CLK'event AND CLK = '1') then
         if (cnt_ticket_en = '1') then
            cnt_ticket <= cnt_ticket + 1;
         end if;
      end if;
   end process;

   TICKET_NUMBER <= cnt_ticket;


   -----------------------------------------------------------------------------
   -- FSM
   -- TICKET_EXCHANGE control
   TICKET_EXCHANGE <= cnt_ticket_en;

   -- FSM control process
   fsm_ctrlp: process(CLK, RESET)
   begin
      if reset = '1' then
         present_state <= st_idle;
      elsif CLK='1' and CLK'event then
         present_state <= next_state;
      end if;
   end process;

   -- Next state logic
   state_transp: process (present_state, input_rdy, FL_EOF_N, OUTPUT_RDY_N,
                          SRC_RDY_IN_N)
   begin
      case present_state is

         -- ST_IDLE
         when st_idle =>
            if input_rdy = '1' then
               next_state <= st_start;
            else
               next_state <= st_idle;
            end if;

         -- ST_START
         when st_start =>
            if FL_EOF_N = '0' and OUTPUT_RDY_N = '0' and SRC_RDY_IN_N = '0' then
               next_state <= st_idle;
            else
               next_state <= st_transmission;
            end if;

         -- ST_TRANSMISSION
         when st_transmission =>
            if FL_EOF_N = '0' and OUTPUT_RDY_N = '0' and SRC_RDY_IN_N = '0' then
               if input_rdy = '1' then
                  next_state <= st_start;
               else
                  next_state <= st_idle;
               end if;
            else
               next_state <= st_transmission;
            end if;

      end case;
   end process;

   -- Output logic
   output_logicp: process(present_state, TICKET_RDY, FL_EOF_N, OUTPUT_RDY_N,
                          SRC_RDY_IN_N)
   begin
      case present_state is

         -- ST_IDLE
         when st_idle =>
            reg_sel_we <= '1';
            src_rdy_out_n <= '1';
            cnt_ticket_en <= '0';

         -- ST_START
         when st_start =>
            reg_sel_we <= '0';
            src_rdy_out_n <= '0';
            cnt_ticket_en <= '1';

         -- ST_TRANSMISSION
         when st_transmission =>
            reg_sel_we <= not (FL_EOF_N or OUTPUT_RDY_N or SRC_RDY_IN_N);
            src_rdy_out_n <= '0';
            cnt_ticket_en <= '0';

      end case;
   end process;
end architecture FL_SEQUENCER_FSM_ARCH;
