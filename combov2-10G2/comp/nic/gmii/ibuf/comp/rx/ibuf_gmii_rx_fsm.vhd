--
-- ibuff_gmii_rx_fsm.vhd: fsm for ibuf_gmii receive part
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
entity ibuf_gmii_rx_fsm is
   generic (
      INBANDFCS   : boolean
   );
   port (
      CLK         :  in std_logic;
      RESET       :  in std_logic;
      EN          :  in std_logic;

      RXDV        :  in std_logic;
      RXER        :  in std_logic;
      PREAM       :  in std_logic;
      PREAM_OVF   :  in std_logic;
      SFD         :  in std_logic;
      PLD_END     :  in std_logic;
      CRC_END     :  in std_logic;
   
      PREAM_CE    : out std_logic;
      DO_DV       : out std_logic;
      CRC_DV      : out std_logic;
      CRC_EOP     : out std_logic; -- crc last data
      ERR_FLAG    : out std_logic;
      INIT        : out std_logic;
      SOP         : out std_logic;
      EOP         : out std_logic;
      REG_CRC_WE  : out std_logic;
      STATE       : out std_logic_vector(2 downto 0)
   );

end entity ibuf_gmii_rx_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_gmii_rx_fsm is

   type t_state is (S_INIT, S_IDLE, S_PREAM, S_DATA_START, S_DATA, S_CRC);
   signal present_state, next_state : t_state;
   
   signal reg_crc_eop_i : std_logic;

begin

   reg_crc_eop_i_gen: if INBANDFCS = true generate
      -- register reg_crc_eop_i
      reg_crc_eop_ip: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (EN = '1') then
               reg_crc_eop_i <= CRC_END;
            end if;
         end if;
      end process;
   end generate reg_crc_eop_i_gen;

   -------------------------------------------------------------------------
   sync_fsm: process(RESET, CLK)
   begin
      if (RESET='1') then
         present_state <= S_INIT;
      elsif (CLK'event and CLK='1') then
         if (EN = '1') then
            present_state <= next_state;
         end if;
      end if;
   end process;

   next_state_logic:
   process(present_state, CLK, RESET, RXDV, RXER, PREAM, PREAM_OVF, SFD,
           PLD_END, reg_crc_eop_i)
   begin
      case (present_state) is
      -- ------------------------------
      when S_INIT =>
         next_state <= S_INIT;
         if (RXDV='0') then
            next_state <= S_IDLE;
         end if;
      -- ------------------------------
      when S_IDLE =>
         next_state <= S_INIT;
         if (RXDV='0') then
            next_state <= S_IDLE;
         elsif (RXER='0' and RXDV='1') then
            if (PREAM='1') then
               next_state <= S_PREAM;
            elsif (SFD='1') then
               next_state <= S_DATA_START;
            end if;
         end if;
      -- ------------------------------
      when S_PREAM =>
         next_state <= S_INIT;
         if (PREAM_OVF='0' and RXER='0') then
            if (PREAM='1') then
               next_state <= S_PREAM;
            elsif (SFD='1') then
               next_state <= S_DATA_START;
            else
               next_state <= S_INIT;
            end if;
         end if;
      -- ------------------------------
      when S_DATA_START =>
         next_state <= S_DATA;
         if (RXER='1' or RXDV = '0') then
	         next_state <= S_INIT;
         end if;
      -- ------------------------------
      when S_DATA =>
         next_state <= S_DATA;
         if (RXER = '1') then
            next_state <= S_INIT;
         elsif (PLD_END='1') then
            if (INBANDFCS=false) then
               next_state <= S_INIT;
            else
	            next_state <= S_CRC;
            end if;
         end if;
      -- ------------------------------
      when S_CRC =>
         next_state <= S_CRC;
         if (reg_crc_eop_i='1') then
            next_state <= S_IDLE;
         end if;
      -- ------------------------------
      when others =>
         next_state <= S_INIT;
      -- -------------------------- ----
      end case;
   end process;

   output_logic:
   process(present_state, CLK, RESET, RXDV, RXER, PREAM, PREAM_OVF, SFD,
           PLD_END, reg_crc_eop_i, EN)
   begin
      PREAM_CE <= '0';
      DO_DV    <= '0';
      CRC_DV   <= '0';
      CRC_EOP  <= '0';
      ERR_FLAG <= '0';
      INIT     <= '0';
      SOP      <= '0';
      EOP      <= '0';
      REG_CRC_WE <= '0';

      case (present_state) is
         -- ------------------------------
         when S_INIT =>
            STATE <= "000";
            if (RXDV='1') then
               INIT <= '1';
            end if;
         -- ------------------------------
         when S_IDLE =>
            STATE <= "001";
            if (RXDV='1' and RXER='0' and PREAM='1') then
               PREAM_CE <= '1';
               INIT     <= '1';
            end if;
         -- ------------------------------
         when S_PREAM =>
            STATE <= "010";
            if (PREAM='1') then
               PREAM_CE <= '1';
            end if;
         -- ------------------------------
         when S_DATA_START =>
            STATE <= "011";
            CRC_DV <= '1';
            SOP <= '1';
            REG_CRC_WE <= '1';
            if (RXER='1' or RXDV='0') then
               CRC_DV <= '0';
               SOP <= '0';
               ERR_FLAG <= '1';
            end if;
         -- ------------------------------
         when S_DATA =>
            STATE <= "101";
            DO_DV <= '1';
            CRC_DV <= '1';
            REG_CRC_WE <= '1';
            if (RXER='1') then
               CRC_EOP <= '1';
               ERR_FLAG <= '1';
               EOP <= '1';
            elsif (PLD_END='1') then
               CRC_EOP <= '1';
               REG_CRC_WE <= '0';
               if (INBANDFCS=false) then
                  EOP <= '1';
               end if;
            end if;
         -- ------------------------------
         when S_CRC =>
            STATE <= "110";
            if (INBANDFCS = true) then
               DO_DV <= '1';
               EOP <= reg_crc_eop_i;
            end if;
         -- ------------------------------
         when others =>
            STATE <= "111";
            null;
         -- ------------------------------
      end case;
   end process;

end architecture full;
