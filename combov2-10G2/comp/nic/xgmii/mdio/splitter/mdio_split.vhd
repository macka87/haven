-- mdio_split.vhd: Split and re-address MDIO interface into 2 outputs
-- Copyright (C) 2010 CESNET
-- Author(s):  Stepan Friedl <friedl@liberouter.org>
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
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.STD_LOGIC_ARITH.ALL;
use IEEE.STD_LOGIC_UNSIGNED.ALL;
use IEEE.NUMERIC_STD.ALL;

entity mdio_split is
   generic (
      PORT0_SRC_ADDR : std_logic_vector(4 downto 0) := "00000";
      PORT1_SRC_ADDR : std_logic_vector(4 downto 0) := "00001";
      DST_ADDR       : std_logic_vector(4 downto 0) := "00000";
      VOID_DST_ADDR  : std_logic_vector(4 downto 0) := "01111" -- Fake device address
   );
   port (
      CLK      : in  std_logic;
      RESET    : in  std_logic;
      STATE    : out std_logic_vector(3 downto 0);
      --
      MDIO_IN  : in  std_logic;
      MDIO_OUT : out std_logic;
      MDIO_OE  : out std_logic; -- output enable, active high
      MDC      : in  std_logic; -- Serial clock input
      -- Output interface 0
      MDIO0_IN  : in  std_logic;
      MDIO0_OUT : out std_logic;
      MDIO0_OE  : out std_logic;  -- output enable, active high
      MDC0      : out  std_logic; -- Serial clock otput
      -- Output interface 1
      MDIO1_IN  : in  std_logic;
      MDIO1_OUT : out std_logic;
      MDIO1_OE  : out std_logic; -- output enable, active high
      MDC1      : out std_logic  -- Serial clock otput
   );
end mdio_split;

architecture behavioral of mdio_split is

type state_mdio_t is (WAIT_FOR_START, START, DIR0, DIR1, DIR1_HOLD, PHY_ADDRESS,
                      PHY_READDRESS, PHY_ADDR_HOLD, REG_ADDRESS, TURN_AROUND,
                      DATA);
signal state_mdio : state_mdio_t;

signal reg_mdc     : std_logic_vector(2 downto 0);
signal reg_mdio    : std_logic_vector(2 downto 0);
signal mdc_sum     : integer range 0 to 3;
signal mdc_filt    : std_logic;
signal mdio_filt   : std_logic;
signal mdio_dir    : std_logic := '0';
signal reg_mdc_filt: std_logic;
signal mdc_rising  : std_logic;
signal mdc_falling : std_logic;
signal mdio0_o     : std_logic;
signal mdio1_o     : std_logic;
signal mdc0_o      : std_logic;
signal mdc1_o      : std_logic;
signal port0_match : std_logic;
signal port1_match : std_logic;
signal mdio_cnt    : integer range 0 to 31 := 0;

begin

MDIO0_OUT <= mdio0_o;
MDC0      <= mdc0_o;

MDIO1_OUT <= mdio1_o;
MDC1      <= mdc1_o;

MDC_EDGE_DETECT: process(CLK)
begin
   if CLK'event and CLK = '1' then
      reg_mdc  <= reg_mdc(1 downto 0) & MDC;
      reg_mdio <= reg_mdio(1 downto 0) & MDIO_IN;

      reg_mdc_filt <= mdc_filt;
   end if;
end process;

-- MDC fliter for glitch elimination
mdc_sum     <= conv_integer(reg_mdc(0))+conv_integer(reg_mdc(1))+conv_integer(reg_mdc(2)); -- +conv_integer(reg_mdc(3));
mdc_filt    <= '1' when mdc_sum > 1 else '0';
mdio_filt   <= reg_mdio(1);
mdc_rising  <= mdc_filt and (not reg_mdc_filt);
mdc_falling <= (not mdc_filt) and (reg_mdc_filt);

    PROCESS(CLK, reset)
    BEGIN
        If CLK'event and CLK = '1' then
           if reset = '1' then
              state_mdio <= WAIT_FOR_START;
           else
               mdc0_o   <= mdc_filt;
               mdc1_o   <= mdc_filt;
               MDIO_OE  <= '0';
               MDIO0_OE <= '1';
               MDIO1_OE <= '1';
               MDIO_OUT <= MDIO0_IN;
               case state_mdio is

                   when WAIT_FOR_START =>
                      STATE <= X"0";
                      port0_match <= '1';
                      port1_match <= '1';
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if (mdio_filt = '0') and (mdc_rising = '1') then
                         STATE_MDIO <= START;
                      end if;

                   when START =>
                      STATE <= X"1";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if (mdc_rising = '1') then
                         state_mdio <= DIR0;
                      end if;

                   when DIR0 =>
                      STATE <= X"2";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if mdc_rising = '1' then
                         state_mdio <= DIR1;
                         mdio_dir   <= mdio_filt; -- '1' = Read, '0' = write
                      end if;

                   When DIR1 =>
                      STATE <= X"3";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if mdc_rising = '1' then
                         state_mdio  <= DIR1_HOLD; 
                      end if;
                      mdio_cnt <= 4;
                      
                   When DIR1_HOLD =>
                      STATE <= X"A";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if mdc_falling = '1' then
                         state_mdio  <= PHY_ADDRESS;
                      end if;
                      mdio_cnt <= 4;

                   when PHY_ADDRESS =>
                      STATE   <= X"4";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if (mdio_cnt > 0) and (mdc_rising = '1') then
                         mdio_cnt <= mdio_cnt - 1;
                      elsif (mdc_rising = '1') then
                         state_mdio <= REG_ADDRESS;
                         mdio_cnt   <= 0;
                      end if;
                      -- PORT0 re-addressing
                      if (mdio_filt = PORT0_SRC_ADDR(mdio_cnt)) and (port0_match = '1') then
                         port0_match <= '1';
                      elsif (mdc_falling = '1') then
                         port0_match <= '0';
                         state_mdio <= PHY_READDRESS;
                      end if;
                      -- PORT1 re-addressing
                      if (mdio_filt = PORT1_SRC_ADDR(mdio_cnt)) and (port1_match = '1') then
                         port1_match <= '1';
                      elsif (mdc_falling = '1') then
                         port1_match <= '0';
                         state_mdio <= PHY_READDRESS;
                      end if;

                   when PHY_READDRESS =>
                      STATE <= X"5";
                      if (mdc_rising = '1') then
                         state_mdio <= PHY_ADDR_HOLD;
                      end if;
                      if (port0_match = '1') then
                         mdio0_o <= DST_ADDR(mdio_cnt);
                      else
                         mdio0_o <= VOID_DST_ADDR(mdio_cnt);
                      end if;
                      if (port1_match = '1') then
                         mdio1_o <= DST_ADDR(mdio_cnt);
                      else
                         mdio1_o <= VOID_DST_ADDR(mdio_cnt);
                      end if;

                   when PHY_ADDR_HOLD =>
                      STATE <= X"6";
                      if (mdio_cnt > 0) and (mdc_falling = '1') then
                          state_mdio <= PHY_READDRESS;
                          mdio_cnt <= mdio_cnt - 1;
                      elsif (mdc_falling = '1') then
                          state_mdio <= REG_ADDRESS;
                          mdio_cnt   <= 0;
                          mdio0_o    <= mdio_filt;
                          mdio1_o    <= mdio_filt;
                      end if;
                      if (port0_match = '1') then
                         mdio0_o <= DST_ADDR(mdio_cnt);
                      else
                         mdio0_o <= VOID_DST_ADDR(mdio_cnt);
                      end if;
                      if (port1_match = '1') then
                         mdio1_o <= DST_ADDR(mdio_cnt);
                      else
                         mdio1_o <= VOID_DST_ADDR(mdio_cnt);
                      end if;

                   when REG_ADDRESS =>
                      STATE <= X"7";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if (mdio_cnt < 4) and (mdc_rising = '1') then
                          mdio_cnt <= mdio_cnt + 1;
                          state_mdio <= REG_ADDRESS;
                      elsif (mdc_rising = '1') then
                          mdio_cnt <= 0;
                          state_mdio <= TURN_AROUND;
                      end if;

                   When TURN_AROUND =>
                      STATE <= X"8";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if (mdio_cnt < 1) and (mdc_rising = '1') then
                         mdio_cnt <= mdio_cnt + 1;
                         state_mdio <= TURN_AROUND;
                      elsif (mdc_rising = '1') then
                         mdio_cnt <= 0;
                         state_mdio <= DATA;
                      end if;
                      if mdio_dir = '1' then -- Read from PHY
                         MDIO_OE  <= '1';
                         MDIO0_OE <= '0';
                         MDIO1_OE <= '0';
                      end if;

                   When DATA =>
                      STATE <= X"9";
                      mdio0_o <= mdio_filt;
                      mdio1_o <= mdio_filt;
                      if port0_match = '1' then
                         MDIO_OUT <= MDIO0_IN;
                      end if;
                      if port1_match = '1' then
                         MDIO_OUT <= MDIO1_IN;
                      end if;
                      if (mdio_cnt < 15) and (mdc_rising = '1') then
                          mdio_cnt <= mdio_cnt + 1;
                          state_mdio <= DATA;
                      elsif (mdc_rising = '1') then
                          mdio_cnt <= 0;
                          state_mdio <= WAIT_FOR_START;
                      end if;
                      if mdio_dir = '1' then -- Read from PHY
                         MDIO_OE  <= '1';
                         MDIO0_OE <= '0';
                         MDIO1_OE <= '0';
                      end if;

                   when others =>
                      state_mdio <= WAIT_FOR_START;
               end case;
           end if; -- not reset
        end if; -- CLK'event
    end process;

end behavioral;
