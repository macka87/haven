
-- tsuadd_fsm.vhd: TSUADD_FSM component
-- Copyright (C) 2005 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
--       Entity :
-- -------------------------------------------------------------

entity tsuadd_fsm is
   port (
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- Input
      CNT_TS_MAX     : in std_logic;
      TSADD_INIT     : in std_logic;
      TSADD_SHORT    : in std_logic;
      TSPTM_DV       : in std_logic;

      -- Output
      TSADD_DV       : out std_logic;
      TS_WE_I        : out std_logic;
      CNT_PPFTS_RST  : out std_logic;
      TS_STORE       : out std_logic
   );
end tsuadd_fsm;

-- -------------------------------------------------------------
--       Architecture :
-- -------------------------------------------------------------
architecture behavioral of tsuadd_fsm is

type t_state is (WAIT_FOR_REQ, WAIT_FOR_DV, STORE_TS, ADD_PPFTS,
                 WAIT_FOR_DV_SHORT, STORE_TS_SHORT, SEND_DV1, SEND_DV2);

signal present_state, next_state : t_state;

begin

-- -------------------------------------------------------------
sync_logic: process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= WAIT_FOR_REQ;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------------
next_state_logic: process(present_state,TSADD_INIT,TSADD_SHORT,TSPTM_DV,
                           CNT_TS_MAX)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   -- Wait for request from add-on
   when WAIT_FOR_REQ =>
      next_state <= WAIT_FOR_REQ;
      if TSADD_INIT = '1' then
         next_state <= WAIT_FOR_DV;
      elsif TSADD_SHORT = '1' then
         next_state <= WAIT_FOR_DV_SHORT;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   -- Wait for DataValid from PTM
   when WAIT_FOR_DV =>
      next_state <= WAIT_FOR_DV;
      if TSPTM_DV = '1' then
         next_state <= STORE_TS;
      end if;

   when WAIT_FOR_DV_SHORT =>
      next_state <= WAIT_FOR_DV_SHORT;
      if TSPTM_DV = '1' then
         next_state <= STORE_TS_SHORT;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   -- Store TS incoming from PTM
   when STORE_TS =>
      next_state <= STORE_TS;
      if  CNT_TS_MAX = '1' then
         next_state <= ADD_PPFTS;
      end if;

   when STORE_TS_SHORT =>
      next_state <= SEND_DV1;
   -- - - - - - - - - - - - - - - - - - - - -
   -- Add cnt_ppfts content into ts_reg
   when ADD_PPFTS =>
      next_state <= SEND_DV1;
   -- - - - - - - - - - - - - - - - - - - - -
   -- Send DataValid to Add-on card interface
   --    DV must be set 2 cycles -> connected to AD2SD component
   when SEND_DV1 =>
      next_state <= SEND_DV2;
   when SEND_DV2 =>
      next_state <= WAIT_FOR_REQ;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

-- -------------------------------------------------------------
output_logic: process(present_state)
begin
   TS_WE_I        <= '1';
   TS_STORE       <= '0';
   CNT_PPFTS_RST  <= '0';
   TSADD_DV       <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when STORE_TS =>
      TS_STORE <= '1';
      TS_WE_I  <= '0';
   -- - - - - - - - - - - - - - - - - - - - -
   when ADD_PPFTS =>
      CNT_PPFTS_RST <= '1';
   -- - - - - - - - - - - - - - - - - - - - -
   when SEND_DV1 =>
      TSADD_DV <= '1';
   -- - - - - - - - - - - - - - - - - - - - -
   when SEND_DV2 =>
      TSADD_DV <= '1';
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;

end behavioral;

