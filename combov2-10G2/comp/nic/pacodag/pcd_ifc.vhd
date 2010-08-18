-- pcd_ifc.vhd: PAcket COntrol DAta Generator for NIC project 
-- Copyright (C) 2007 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
architecture ifc of pacodag is

   -- registers
   signal reg_payload_len        : std_logic_vector(15 downto 0);
   signal reg_payload_len_we     : std_logic;

   -- FSM signals
   type t_state is (S_WORD1, S_WORD2 , S_IDLE, S_WAIT_FOR_VALID);
   signal present_state, next_state : t_state;
begin
   reg_payload_len_we   <= STAT_DV;

   -- STORE all wanted STATs --------------------------------------------------
   process(RESET, CTRL_CLK)
   begin
      if (RESET = '1') then
         reg_payload_len <= (others => '0');
      elsif (CTRL_CLK'event AND CTRL_CLK = '1') then
         if (reg_payload_len_we = '1') then
            reg_payload_len <= STAT.PAYLOAD_LEN;
         end if;
      end if;
   end process;

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
               -- NOTE: We don't generate any data when another SOP arrives
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
   output_logic : process(present_state, STAT_DV, reg_payload_len)
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
            CTRL_DATA(3 downto 0)   <= IFC_ID;                       -- IFC_ID
            CTRL_DATA(7 downto 4)   <= (others => '0');              -- RESERVED
            CTRL_DATA(15 downto 8)  <= reg_payload_len(7 downto 0);  -- PAYLOAD_LEN - 1/2
            CTRL_REM        <= (others=>'0');
            CTRL_SRC_RDY_N  <= '0';
            CTRL_SOP_N      <= '0';
   
         -- -----------------------------------------
         when S_WORD2 => 
            CTRL_DATA(7 downto 0)   <= reg_payload_len(15 downto 8); -- PAYLOAD_LEN - 2/2
            CTRL_DATA(15 downto 8)  <= (others => '0');              -- RESERVED
            CTRL_REM        <= (others=>'0');
            CTRL_SRC_RDY_N  <= '0';
            CTRL_EOP_N      <= '0';
   
         -- -----------------------------------------
         when others =>
      end case;
   end process output_logic;

   -- Header/footer part-------------------------------------------------------
   assert (HEADER_EN /= FOOTER_EN)
      report "PCD_IFC: Exactly one of the generics CTRL_HDR_EN and CTRL_FTR_EN has to be true"
      severity error;

end ifc;

