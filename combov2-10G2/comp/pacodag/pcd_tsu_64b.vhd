-- pcd_tsu.vhd: PAcket COntrol DAta Generator for NIC project
-- Copyright (C) 2007 CESNET, Liberouter project
-- Author(s): Martin Kosek <kosek@liberouter.org>
--            Jan Pazdera <pazdera@liberouter.org>
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
-- TODO: - 

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

use work.math_pack.ALL;
use work.ibuf_general_pkg.ALL;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of pacodag_tsu_64b is

   signal reg_tsu                : std_logic_vector(63 downto 0);
   signal reg_segment_len        : std_logic_vector(15 downto 0);
   signal reg_segment_len_we     : std_logic;

   -- data for first word
   signal first_word_data        : std_logic_vector(63 downto 0);

   type t_state is (S_WORD1, S_WORD2, S_IDLE, S_WAIT_FOR_VALID);
   signal present_state, next_state : t_state;

begin
   reg_segment_len_we   <= STAT_DV;

   -- STORE all wanted STATs --------------------------------------------------
   process(CTRL_CLK)
   begin
      if (CTRL_CLK'event AND CTRL_CLK = '1') then
         if (RESET = '1') then
            reg_segment_len <= (others => '0');
         elsif (reg_segment_len_we = '1') then
            reg_segment_len <= STAT_PAYLOAD_LEN 
                            + conv_std_logic_vector(16, reg_segment_len'length);
         end if;
      end if;
   end process;

   process(CTRL_CLK)
   begin
      if (CTRL_CLK'event AND CTRL_CLK = '1') then
         if (RESET = '1') then
            reg_tsu <= (others => '0');
         elsif (SOP = '1') then
            reg_tsu <= TS;
         end if;
      end if;
   end process;
  
   -- reserved
   first_word_data(63 downto 48) <= X"0000";
   -- IFC_ID + reserved
   first_word_data(47 downto 32) <= X"000" & IFC_ID;
   -- header length
   first_word_data(31 downto 16) <= conv_std_logic_vector(12, 16);
   -- payload length
   first_word_data(15 downto  0) <= reg_segment_len;
   
   -- FSM present state register ----------------------------------------------
   sync_logic : process(RESET, CTRL_CLK)
   begin
      if (RESET = '1') then
         present_state <= S_IDLE;
      elsif (CTRL_CLK'event AND CTRL_CLK = '1') then
         present_state <= next_state;
      end if;
   end process sync_logic;
   
   -- FSM next state logic ----------------------------------------------------
   next_state_logic : process(present_state, SOP, CTRL_DST_RDY_N, STAT_DV)
   begin
      case present_state is
   
         -- -----------------------------------------
         when S_IDLE => 
            if (SOP = '1') then
               next_state <= S_WAIT_FOR_VALID;
            else
               next_state <= S_IDLE;
            end if;

          -- -----------------------------------------
         when S_WAIT_FOR_VALID => 
            if (STAT_DV = '1') then
               next_state <= S_WORD1;
            else
               next_state <= S_WAIT_FOR_VALID;
            end if;

         -- -----------------------------------------
         when S_WORD1 => 
            if (CTRL_DST_RDY_N = '0') then
               next_state <= S_WORD2;
            else
               next_state <= S_WORD1;
            end if;

         -- -----------------------------------------
         when S_WORD2 => 
            if (CTRL_DST_RDY_N = '0') then
               next_state <= S_IDLE;
            else
               next_state <= S_WORD2;
            end if;

         -- -----------------------------------------
         when others =>
            next_state <= S_IDLE;
      end case;
   end process next_state_logic;
   
   -- FSM output logic---------------------------------------------------------
   output_logic : process(present_state, STAT_DV, first_word_data, reg_tsu)
   begin
   
      CTRL_DATA       <= (others => '0');
      CTRL_REM        <= (others => '0');
      CTRL_SRC_RDY_N  <= '1';
      CTRL_SOP_N      <= '1';
      CTRL_EOP_N      <= '1';
      CTRL_RDY        <= '0';
   
      case present_state is
   
         when S_IDLE => 
            CTRL_RDY <= '1';

         when S_WAIT_FOR_VALID =>
            CTRL_RDY <= '1';

         -- -----------------------------------------
         when S_WORD1 => 
            CTRL_DATA         <= first_word_data;
            CTRL_SRC_RDY_N    <= '0';
            CTRL_SOP_N        <= '0';
   
         -- -----------------------------------------
         when S_WORD2 =>   -- TS
            CTRL_DATA         <= reg_tsu;
            CTRL_REM          <= conv_std_logic_vector(6, CTRL_REM'length);
            CTRL_EOP_N        <= '0';
            CTRL_SRC_RDY_N    <= '0';

         -- -----------------------------------------
         when others => null;
      end case;
   end process output_logic;

end behavioral;
