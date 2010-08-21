--
-- i2c_master_fsm.vhd: fsm for i2c master
--
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Mikusek <martin.mikusek@liberouter.org>
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
--
--

library IEEE;
use IEEE.std_logic_1164.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity i2c_master_fsm is
   port (
      CLK       :  in std_logic; -- 100 kHz clock
      RESET     :  in std_logic;

      -- inputs ---------------------------------------------------------------
      EN        :  in std_logic;
      DONE      :  in std_logic;
      ACK       :  in std_logic;
      RW        :  in std_logic; -- R/W operation register
      LOP       :  in std_logic; -- low i2c clock pulse

      -- outputs --------------------------------------------------------------
      OP_OK     : out std_logic;
      OP_DONE   : out std_logic;
      BUSY      : out std_logic;
      
      START_CMD : out std_logic;
      STOP_CMD  : out std_logic;
      DEV_RW    : out std_logic; -- device operation (LSB bit of dev_address)

      CNT_CLR   : out std_logic; -- shift register counter clear

      DEV       : out std_logic; -- device addressing
      ADDR      : out std_logic; -- word adressing
      WR_DATA   : out std_logic; -- data sending
      RD_DATA   : out std_logic;  -- data receiving

      STATE     : out std_logic_vector(1 downto 0);
      STORE_STATE : out std_logic
   );

end entity i2c_master_fsm;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of i2c_master_fsm is

   type t_state is (S_IDLE, S_START, S_RW_DEV, S_RW_ADDR, S_RD_START,
                    S_RD_DEV, S_RD_DATA, S_WR_DATA, S_STOP_OK, S_STOP_KO);
   signal present_state, next_state : t_state;

begin -------------------------------------------------------------------------

   sync_fsm: process(RESET, CLK)
   begin
      if (RESET = '1') then
         present_state <= S_IDLE;
      elsif (CLK'event and CLK = '1') then
         present_state <= next_state;
      end if;
   end process;

   next_state_logic:
   process(present_state, CLK, RESET, EN, DONE, ACK, RW, LOP)
   begin
      case (present_state) is
      -- ------------------------------
      when S_IDLE =>
         next_state <= S_IDLE;
         if (EN='1') then
            next_state <= S_START;
         end if;
      -- ------------------------------
      when S_START =>
         next_state <= S_START;
         if (LOP='1') then
            next_state <= S_RW_DEV;
         end if;
      -- ------------------------------
      when S_RW_DEV =>
	 next_state <= S_RW_DEV;
         if (DONE='1' and LOP='1') then
            if (ACK='1') then
               next_state <= S_RW_ADDR;
            else
               next_state <= S_STOP_KO;
	    end if;
         end if;
      -- ------------------------------
      when S_RW_ADDR =>
         next_state <= S_RW_ADDR;
         if (DONE='1'and LOP='1') then
            if (ACK='0') then
               next_state <= S_STOP_KO;
            else
               if (RW='0') then
                  next_state <= S_WR_DATA;
               else
                  next_state <= S_RD_START;
               end if;
            end if;
         end if;
      -- ------------------------------
      when S_RD_START =>
         next_state <= S_RD_START;
         if (LOP='1') then
            next_state <= S_RD_DEV;
         end if;
      -- ------------------------------
      when S_RD_DEV =>
         next_state <= S_RD_DEV;
         if (DONE='1' and LOP='1') then
            if (ACK='1') then
               next_state <= S_RD_DATA;
            else
               next_state <= S_STOP_KO;
	    end if;
         end if;
      -- ------------------------------
      when S_RD_DATA =>
         next_state <= S_RD_DATA;
         if (DONE='1' and LOP='1') then
            next_state <= S_STOP_OK;
         end if;
      -- ------------------------------
      when S_WR_DATA =>
         next_state <= S_WR_DATA;
         if (DONE='1' and LOP='1') then
            if (ACK='1') then
               next_state <= S_STOP_OK;
            else
               next_state <= S_STOP_KO;
            end if;
         end if;
      -- ------------------------------
      when S_STOP_OK =>
         next_state <= S_STOP_OK;
         if (LOP='1') then
            next_state <= S_IDLE;
         end if;
      -- ------------------------------
      when S_STOP_KO =>
         next_state <= S_STOP_KO;
         if (LOP='1') then
            next_state <= S_IDLE;
         end if;
      -- ------------------------------
      when others =>
         next_state <= S_IDLE;
      -- -------------------------- ----
      end case;
   end process;

   output_logic:
   process(present_state, CLK, RESET, EN, DONE, ACK, RW, LOP)
   begin
      OP_OK           <= '0';
      OP_DONE         <= '0';
      BUSY            <= '1';
      START_CMD       <= '0';
      STOP_CMD        <= '0';
      DEV_RW          <= '0';
      CNT_CLR         <= '0';
      DEV             <= '0';
      ADDR            <= '0';
      WR_DATA         <= '0';
      RD_DATA         <= '0';
      STATE           <= "00";
      STORE_STATE     <= '0';
      
      case (present_state) is
         -- ------------------------------
         when S_IDLE =>
           BUSY       <= '0';
         -- ------------------------------
         when S_START =>
           START_CMD  <= '1';
           CNT_CLR    <= LOP;
	 -- ------------------------------
         when S_RW_DEV =>
            DEV_RW    <= '0';
	    DEV       <= '1';
            CNT_CLR   <= DONE and ACK and LOP;
            STATE     <= "00";
            STORE_STATE <= DONE and (not ACK) and LOP;
	 -- ------------------------------
         when S_RW_ADDR =>
            ADDR      <= '1';
            CNT_CLR   <= DONE and ACK and LOP;
            STATE     <= "01";
            STORE_STATE <= DONE and (not ACK) and LOP;
         -- ------------------------------
         when S_RD_START =>
           START_CMD  <= '1';
           CNT_CLR    <= LOP;
         -- ------------------------------
         when S_RD_DEV =>
            DEV_RW    <= '1';
            DEV       <= '1';
            CNT_CLR   <= DONE and ACK and LOP;
            STATE     <= "10";
            STORE_STATE <= DONE and (not ACK) and LOP;
         -- ------------------------------
         when S_RD_DATA =>
            RD_DATA   <= '1';
         -- ------------------------------
         when S_WR_DATA =>
            WR_DATA   <= '1';
            STATE     <= "11";
            STORE_STATE <= DONE and (not ACK) and LOP;
         -- ------------------------------
         when S_STOP_OK =>
            STOP_CMD  <= '1';
            OP_DONE   <= LOP;
            OP_OK     <= '1';
         -- ------------------------------
         when S_STOP_KO =>
            STOP_CMD  <= '1';
            OP_DONE   <= LOP;
            OP_OK     <= '0';
         -- ------------------------------
         when others =>
            null;
         -- ------------------------------
      end case;
   end process;

end architecture full;
