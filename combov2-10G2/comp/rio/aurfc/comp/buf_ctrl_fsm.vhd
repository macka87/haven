
-- buf_ctrl_fsm.vhd: Buffer Controller FSM 
-- Copyright (C) 2006 CESNET, Liberouter project
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on

-- -------------------------------------------------------------
--       Entity :   
-- -------------------------------------------------------------

entity buf_ctrl_fsm is
   generic (
      XON_LIMIT         : std_logic_vector(2 downto 0) := "011";
      XOFF_LIMIT        : std_logic_vector(2 downto 0) := "110"
   );
   port (
         -- Common Input
         CLK      : in std_logic;
         RESET    : in std_logic;
         
         -- Input
         STATUS   : in std_logic_vector(2 downto 0);
         NFC_ACK_N   : in std_logic;

         -- Output
         NFC_REQ_N   : out std_logic;
         NFC_NB      : out std_logic_vector(0 to 3);

         -- Debug
         D_STATE     : out std_logic_vector(1 downto 0);
         D_CNT_XON   : out std_logic_vector(31 downto 0);
         D_CNT_XOFF  : out std_logic_vector(31 downto 0)
   );
end buf_ctrl_fsm;

-- -------------------------------------------------------------
--       Architecture :     
-- -------------------------------------------------------------
architecture behavioral of buf_ctrl_fsm is

type t_state is (XON_s, REQ_XOFF, XOFF_s, REQ_XON);
signal present_state, next_state: t_state; 

constant XON_c    : std_logic_vector(3 downto 0) := "0000";
constant XOFF_c   : std_logic_vector(3 downto 0) := "1111";

   signal cnt_xon : std_logic_vector(31 downto 0);
   signal cnt_xon_ce : std_logic;
   signal cnt_xoff : std_logic_vector(31 downto 0);
   signal cnt_xoff_ce : std_logic;

begin
-- debug logic

-- cnt_xon counter : 
process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         cnt_xon <= (others => '0');
      elsif (cnt_xon_ce='1') then
         cnt_xon <= cnt_xon + 1;
      end if;
   end if;
end process;
D_CNT_XON <= cnt_xon;

-- cnt_xoff counter : 
process(CLK)
begin
   if (CLK'event and CLK = '1') then
      if (RESET = '1') then
         cnt_xoff <= (others => '0');
      elsif (cnt_xoff_ce='1') then
         cnt_xoff <= cnt_xoff + 1;
      end if;
   end if;
end process;
D_CNT_XOFF <= cnt_xoff;

-- -------------------------------------------------------
sync_logic : process(RESET, CLK)
begin
   if (RESET = '1') then
      present_state <= XON_s;
   elsif (CLK'event AND CLK = '1') then
      present_state <= next_state;
   end if;
end process sync_logic;

-- -------------------------------------------------------
next_state_logic : process(present_state, STATUS, NFC_ACK_N)
begin
   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when XON_s =>
      next_state <= XON_s;
      if (STATUS > XON_LIMIT) then
         next_state <= REQ_XOFF;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when REQ_XOFF =>
      next_state <= REQ_XOFF;
      if (NFC_ACK_N = '0') then
         next_state <= XOFF_s;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when XOFF_s =>
      next_state <= XOFF_s;
      if (STATUS < XON_LIMIT) then
         next_state <= REQ_XON;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when REQ_XON =>
      next_state <= REQ_XON;
      if (NFC_ACK_N = '0') then
         next_state <= XON_s;
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      next_state <= XON_s;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;
      
-- -------------------------------------------------------
output_logic: process(present_state, STATUS)
begin
   NFC_REQ_N   <= '1';
   NFC_NB      <= XON_c;
   cnt_xoff_ce <= '0';
   cnt_xon_ce  <= '0';

   case (present_state) is
   -- - - - - - - - - - - - - - - - - - - - -
   when XON_s =>
      D_STATE <= "00";
      if (STATUS > XON_LIMIT) then
         cnt_xoff_ce <= '1';
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when REQ_XOFF =>
      NFC_NB <= XOFF_c;
      NFC_REQ_N <= '0';
      D_STATE <= "01";
   -- - - - - - - - - - - - - - - - - - - - -
   when XOFF_s =>
      D_STATE <= "10";
      if (STATUS < XON_LIMIT) then
         cnt_xon_ce <= '1';
      end if;
   -- - - - - - - - - - - - - - - - - - - - -
   when REQ_XON =>
      NFC_NB <= XON_c;
      NFC_REQ_N <= '0';
      D_STATE <= "11";
   -- - - - - - - - - - - - - - - - - - - - -
   when others =>
      null;
   -- - - - - - - - - - - - - - - - - - - - -
   end case;
end process;
      
end behavioral;

