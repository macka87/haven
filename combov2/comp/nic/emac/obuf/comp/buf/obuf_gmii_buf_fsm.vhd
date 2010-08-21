--
-- obuf_gmii_buf_fsm.vhd: fsm for obuf_emac buffer part
--
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
--            Libor Polcak <polcak_l@liberouter.org>
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
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity obuf_emac_buf_fsm is
   generic (
      DATA_PATHS : integer
   );
   port (
      CLK          :  in std_logic;
      RESET        :  in std_logic;

      LAST_WORD    :  in std_logic;
      DATA_DV      :  in std_logic;
      EOP          :  in std_logic;
      STATUS_EMPTY :  in std_logic;
      TX_NEXT      :  in std_logic;
      COLLISION    :  in std_logic;
      RETRANSMIT   :  in std_logic;
      RX_DVLD      :  in std_logic;

      DATA_RD      : out std_logic;
      STATUS_RD    : out std_logic;
      STORE        : out std_logic;
      SHIFT        : out std_logic;
      UNDERRUN     : out std_logic;
      TX_DVLD      : out std_logic
   );

end entity obuf_emac_buf_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_emac_buf_fsm is

   type t_state is (S_WAIT, S_DATA_RQ, S_DATA, S_LAST_BIT, S_RELEASE);
   signal present_state, next_state : t_state;

begin -------------------------------------------------------------------------

   sync_fsm: process(RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= S_WAIT;
      elsif (CLK'event and CLK = '1') then
         present_state <= next_state;
      end if;
   end process;

   next_state_logic:
   process(present_state, LAST_WORD, DATA_DV, EOP, STATUS_EMPTY, TX_NEXT,
                                                                  COLLISION)
   begin
      case (present_state) is
      -- ------------------------------
      when S_WAIT =>
         next_state <= S_WAIT;
         if (STATUS_EMPTY='0' and TX_NEXT='1') then
            if (DATA_PATHS>1) then
	    	      next_state <= S_DATA_RQ;
            else
	    	      next_state <= S_DATA;
	         end if;
         end if;
      -- ------------------------------
      when S_DATA_RQ =>
	      if (COLLISION='1') then
	         next_state <= S_RELEASE;
         elsif (DATA_DV='0') then
            --next_state <= S_RELEASE; -- underrun
            next_state <= S_DATA_RQ;
         else
            next_state <= S_DATA;
	      end if;
      -- ------------------------------
      when S_DATA =>
         next_state <= S_DATA;
         if (DATA_PATHS>1) then
            if (COLLISION = '1') then
               next_state <= S_RELEASE;
	         elsif (EOP='1' and LAST_WORD='1' and TX_NEXT='1') then
		         next_state <= S_LAST_BIT;
	         elsif (LAST_WORD='1' and TX_NEXT='1') then
		         next_state <= S_DATA_RQ;
	         end if;
	      else
            if (COLLISION='1') then
               next_state <= S_RELEASE;
	         elsif (EOP='1' and TX_NEXT='1') then
	            next_state <= S_WAIT;
	         end if;
         end if;
      -- ------------------------------
      when S_LAST_BIT =>
         next_state <= S_WAIT;
      -- ------------------------------
      when S_RELEASE =>
         if (EOP='1') then
            next_state <= S_WAIT;
         else
            next_state <= S_RELEASE;
         end if;
      -- ------------------------------
      when others =>
         next_state <= S_WAIT;
      -- -------------------------- ----
      end case;
   end process;

   output_logic:
   process(present_state, LAST_WORD, DATA_DV, EOP, STATUS_EMPTY, TX_NEXT,
                                                          RX_DVLD, COLLISION)
   begin
      DATA_RD   <= '0';
      STATUS_RD <= '0';
      STORE     <= '0';
      UNDERRUN  <= '0';
      TX_DVLD   <= '0';
      SHIFT     <= '0';

      case (present_state) is
         -- ------------------------------
         when S_WAIT =>
            if (STATUS_EMPTY='0' and TX_NEXT='1') then
	            DATA_RD <= '1';
            end if;
	      -- ------------------------------
         when S_DATA_RQ =>
            if (COLLISION='1') then
               TX_DVLD <= '1';
            elsif (DATA_DV='0') then
               --UNDERRUN <= '1';
               TX_DVLD <= '0';
               DATA_RD <= '1';
            else
               STORE <= '1';
               TX_DVLD <= RX_DVLD;
            end if;
	      -- ------------------------------
         when S_DATA =>
            TX_DVLD <= RX_DVLD;
            if (DATA_PATHS > 1) then
               if (COLLISION='1') then
                  TX_DVLD <= '1';
               elsif (EOP='1' and LAST_WORD='1' and TX_NEXT='1') then
                  SHIFT <= '1';
               elsif (LAST_WORD='1' and TX_NEXT='1') then
                  DATA_RD <= '1';
                  SHIFT <= '1';
               else
                  SHIFT <= TX_NEXT;
               end if;
            else
               if (COLLISION='1') then
                  TX_DVLD <= '1';
               elsif (EOP='1' and TX_NEXT='1') then
	               STATUS_RD <= '1';
               else
	               STORE <= '1';
	               DATA_RD <='1';
               end if;
            end if;
	      -- ------------------------------
         when S_LAST_BIT =>
            TX_DVLD <= RX_DVLD;
            STATUS_RD <= '1';
            SHIFT <= '1';
	      -- ------------------------------
         when S_RELEASE =>
            if (EOP = '1') then
               STATUS_RD <= '1';
            else
               DATA_RD <= '1';
            end if;
	      -- ------------------------------
         when others =>
            null;
         -- ------------------------------
      end case;
   end process;

end architecture full;
