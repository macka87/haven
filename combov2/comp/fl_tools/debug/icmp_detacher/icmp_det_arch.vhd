-- icmp_det_arch.vhd: Architecture of Frame link icmp detacher unit
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz>
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

-- library containing log2 and min functions
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of FL_ICMP_DETACHER is

-- Every ICMPv4 packet has it's prtocol ID at 23'rd byte of ethernet packet equal to 1.
-- Protocol ID size is 8 bits.

signal cnt_en	        : std_logic;
signal word_num	        : std_logic_vector(1 downto 0);
signal discard	        : std_logic;
signal decided	        : std_logic;
signal pre_rx_src_rdy_n : std_logic;
signal pre_tx_src_rdy_n : std_logic;
signal pre_rx_dst_rdy_n : std_logic;
signal pre_tx_dst_rdy_n : std_logic;
signal pre_tx_eof_n     : std_logic;
signal rx_transmission  : std_logic;
signal tx_transmission  : std_logic;
signal fsm_tx_dst_rdy_n : std_logic;
signal fsm_tx_src_rdy_n : std_logic;

type rx_t_state is (IDLE, WAITING_WORD, PROC_PACKET, DISCARD_PACK);
type tx_t_state is (IDLE, PROCESSING, DISCARDING);

signal rx_present_state, rx_next_state : rx_t_state;
signal tx_present_state, tx_next_state : tx_t_state;

begin

   -- -------------------------------------------------------
   -- 64b width FL_FIFO
   fifo_inst : entity work.FL_FIFO
   generic map(
      DATA_WIDTH   => 64,
      -- True => use BlockBAMs
      -- False => use SelectRAMs
      USE_BRAMS    => true,
      -- number of items in the FIFO
      ITEMS        => 8,
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE   => 1,
      -- Width of STATUS signal available
      STATUS_WIDTH => 2,
      -- Number of parts in each frame
      PARTS        => 2
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      -- write interface
      RX_DATA        => RX_DATA,
      RX_REM         => RX_REM,
      RX_SRC_RDY_N   => pre_rx_src_rdy_n,
      RX_DST_RDY_N   => pre_rx_dst_rdy_n,
      RX_SOP_N       => RX_SOP_N,
      RX_EOP_N       => RX_EOP_N,
      RX_SOF_N       => RX_SOF_N,
      RX_EOF_N       => RX_EOF_N,
    
      -- read interface
      TX_DATA        => TX_DATA,
      TX_REM         => TX_REM,
      TX_SRC_RDY_N   => pre_tx_src_rdy_n,
      TX_DST_RDY_N   => pre_tx_dst_rdy_n,
      TX_SOP_N       => TX_SOP_N,
      TX_EOP_N       => TX_EOP_N,
      TX_SOF_N       => TX_SOF_N,
      TX_EOF_N       => pre_tx_eof_n,

      -- FIFO state signals
      LSTBLK         => open,
      FULL           => open,
      EMPTY          => open,
      STATUS         => open,
      FRAME_RDY      => open
   );

   RX_DST_RDY_N <= pre_rx_dst_rdy_n or TX_DST_RDY_N;
   rx_transmission <= not (RX_SRC_RDY_N or pre_rx_dst_rdy_n or TX_DST_RDY_N);
   pre_rx_src_rdy_n <= RX_SRC_RDY_N or TX_DST_RDY_N;

   TX_SRC_RDY_N <= pre_tx_src_rdy_n or fsm_tx_src_rdy_n;
   pre_tx_dst_rdy_n <= TX_DST_RDY_N or fsm_tx_dst_rdy_n;
   tx_transmission <= not (pre_tx_src_rdy_n or TX_DST_RDY_N);
   TX_EOF_N <= pre_tx_eof_n;

   -- -------------------------------------------------------
   -- counter of incomed words
   word_cnt : process(CLK)
   begin
      if (CLK'event and CLK = '1') then
	 if (cnt_en = '1' and rx_transmission = '1') then
	    if (RX_SOP_N = '0') then
	       word_num <= "01";
	    else
	       word_num <= word_num + 1;
	    end if;
	 end if;
      end if;
   end process word_cnt;

   -- -------------------------------------------------------
   -- RX FSM
   -- -------------------------------------------------------
   rx_sync_logic : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
	 if (RESET = '1') then
	    rx_present_state <= IDLE;
	 elsif (rx_transmission = '1') then
	    rx_present_state <= rx_next_state;
	 end if;
      end if;
   end process rx_sync_logic;

   -- -------------------------------------------------------
   rx_next_state_logic : process(rx_present_state, RX_EOP_N, RX_EOF_N, RX_DATA, word_num)
   begin
      -- ---------------------------------------------
      -- Default next state
      rx_next_state <= rx_present_state;

      case (rx_present_state) is
      -- - - - - - - - - - - - - - - - - - - - - - -
      when IDLE =>
         if (RX_EOP_N = '0') then
	    rx_next_state <= WAITING_WORD;
         end if;
      -- - - - - - - - - - - - - - - - - - - - - - -
      when WAITING_WORD =>
         if (word_num = 2) then
	    if (RX_DATA(63 downto 56) = X"01") then
	       rx_next_state <= PROC_PACKET;
	    else
	       rx_next_state <= DISCARD_PACK;
	    end if;
         elsif (RX_EOP_N = '0' or RX_EOF_N = '0') then
	    rx_next_state <= DISCARD_PACK;
         end if;
      -- - - - - - - - - - - - - - - - - - - - - - -
      when PROC_PACKET =>
         if (RX_EOF_N = '0') then
	    rx_next_state <= IDLE;
         end if;
      -- - - - - - - - - - - - - - - - - - - - - - -
      when DISCARD_PACK =>
         if (RX_EOF_N = '0') then
	    rx_next_state <= IDLE;
         end if;
      -- - - - - - - - - - - - - - - - - - - - - - -
      when others =>
         rx_next_state <= IDLE;
      end case;
   end process rx_next_state_logic;

   -- -------------------------------------------------------
   rx_output_logic : process(rx_present_state)
   begin
      -- ---------------------------------------------
      -- Initial values
      decided <= '0';
      discard <= '0';
      cnt_en <= '0';

      case (rx_present_state) is
      -- - - - - - - - - - - - - - - - - - - - - - -
      when IDLE =>
      -- - - - - - - - - - - - - - - - - - - - - - -
      when WAITING_WORD =>
         cnt_en <= '1';
      -- - - - - - - - - - - - - - - - - - - - - - -
      when PROC_PACKET =>
	 decided <= '1';
      -- - - - - - - - - - - - - - - - - - - - - - -
      when DISCARD_PACK =>
	 decided <= '1';
         discard <= '1';
      -- - - - - - - - - - - - - - - - - - - - - - -
      when others =>
      end case;
   end process rx_output_logic;

   -- -------------------------------------------------------
   -- TX FSM
   -- -------------------------------------------------------
   tx_sync_logic : process(RESET, CLK)
   begin
      if (CLK'event and CLK = '1') then
	 if (RESET = '1') then
	    tx_present_state <= IDLE;
	 elsif (tx_transmission = '1') then
	    tx_present_state <= tx_next_state;
	 end if;
      end if;
   end process tx_sync_logic;

   -- -------------------------------------------------------
   tx_next_state_logic : process(tx_present_state, pre_tx_eof_n, decided, discard)
   begin
      -- ---------------------------------------------
      -- Default next state
      tx_next_state <= tx_present_state;

      case (tx_present_state) is
      -- - - - - - - - - - - - - - - - - - - - - - -
      when IDLE =>
         if (decided = '1') then
            if (discard = '0') then
               tx_next_state <= PROCESSING;
            else
               tx_next_state <= DISCARDING;
            end if;
         end if;
      -- - - - - - - - - - - - - - - - - - - - - - -
      when PROCESSING =>
         if (pre_tx_eof_n = '0') then
            if (decided = '1') then
               if (discard = '1') then
                  tx_next_state <= DISCARDING;
               end if;
	    else
               tx_next_state <= IDLE;
            end if;
         end if;
      -- - - - - - - - - - - - - - - - - - - - - - -
      when DISCARDING =>
         if (pre_tx_eof_n = '0') then
            if (decided = '1') then
               if (discard = '0') then
                  tx_next_state <= PROCESSING;
               end if;
            else
               tx_next_state <= IDLE;
            end if;
         end if;
      -- - - - - - - - - - - - - - - - - - - - - - -
      when others =>
         tx_next_state <= IDLE;
      end case;
   end process tx_next_state_logic;

   -- -------------------------------------------------------
   tx_output_logic : process(tx_present_state)
   begin
      -- ---------------------------------------------
      -- Initial values
      fsm_tx_dst_rdy_n <= '1';
      fsm_tx_src_rdy_n <= '1';

      case (tx_present_state) is
      -- - - - - - - - - - - - - - - - - - - - - - -
      when IDLE =>
      -- - - - - - - - - - - - - - - - - - - - - - -
      when PROCESSING =>
         fsm_tx_dst_rdy_n <= '0';
         fsm_tx_src_rdy_n <= '0';
      -- - - - - - - - - - - - - - - - - - - - - - -
      when DISCARDING =>
         fsm_tx_dst_rdy_n <= '0';
      -- - - - - - - - - - - - - - - - - - - - - - -
      when others =>
      end case;
   end process tx_output_logic;

end architecture full;
