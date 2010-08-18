-- tx.vhd: EMAC OBUF - TX part
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
-- TODO:
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;

use work.ibuf_general_pkg.all;
use work.emac_pkg.all;

entity obuf_emac_tx is

   generic(
      -- EMAC#_USECLKEN generic
      USECLKEN       : boolean
   );

   port(
      -- Asynchronous reset
      RESET          : in std_logic;
      CLK            : in std_logic;
      CE             : in std_logic;

      -- EMAC TX record
      TX_EMAC_D            : out std_logic_vector(7 downto 0);
      TX_EMAC_DVLD         : out std_logic;
      TX_EMAC_ACK          : in  std_logic;
      TX_EMAC_FIRSTBYTE    : out std_logic;
      TX_EMAC_UNDERRUN     : out std_logic;
      TX_EMAC_COLLISION    : in  std_logic;
      TX_EMAC_RETRANSMIT   : in  std_logic;
      TX_EMAC_IFGDELAY     : out std_logic_vector(7 downto 0);
      TX_EMAC_STATS        : in  std_logic;
      TX_EMAC_STATSVLD     : in  std_logic;
      TX_EMAC_STATSBYTEVLD : in  std_logic;
      TX_EMAC_SPEEDIS10100 : in  std_logic;

      -- Signals from/to buffer
      RX_D           : in std_logic_vector(7 downto 0);
      RX_DVLD        : in std_logic;
      RX_UNDERRUN    : in std_logic;
      RX_NEXT        : out std_logic;
      RX_COLLISION   : out std_logic;
      RX_RETRANSMIT  : out std_logic;
      RX_STATS       : out std_logic_vector(31 downto 0);
      RX_STATS_VLD   : out std_logic
   );

end entity obuf_emac_tx;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_emac_tx is

   constant IFG_DELAY      : std_logic_vector(7 downto 0) := X"08"; -- 8

   signal fsm_dvld         : std_logic;
   signal fsm_next         : std_logic;
   signal fsm_ack          : std_logic;
   signal reg_ack          : std_logic;
   signal mx_ack           : std_logic;
   signal mx_ack_sel       : std_logic;
   signal underrun         : std_logic;
   signal reg_underrun     : std_logic;

   signal reg_stats        : std_logic_vector(31 downto 0);
   signal reg_stats_vld    : std_logic;
   signal cnt_stats_bit    : std_logic_vector(4 downto 0);
   signal cnt_stats_bit_ce : std_logic;
   signal cnt_stats_bit_ld : std_logic;

begin

   TX_EMAC_D            <= RX_D;
   TX_EMAC_DVLD         <= fsm_dvld;
   TX_EMAC_FIRSTBYTE    <= '0';
   TX_EMAC_UNDERRUN     <= underrun;
   RX_COLLISION         <= TX_EMAC_COLLISION and CE;
   RX_RETRANSMIT        <= TX_EMAC_RETRANSMIT and CE;
   TX_EMAC_IFGDELAY     <= IFG_DELAY;
   mx_ack_sel           <= TX_EMAC_SPEEDIS10100;
   RX_NEXT              <= fsm_next and CE;
   RX_STATS             <= reg_stats;
   RX_STATS_VLD         <= reg_stats_vld;

   -- Generated only when CE is enabled
   useclken_gen: if USECLKEN = true generate

      -- register reg_ack
      reg_ackp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_ack <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (CE = '1') then
               reg_ack <= TX_EMAC_ACK;
            end if;
         end if;
      end process;

      fsm_ack <= mx_ack;

      -- multiplexor mx_ack
      mx_ackp: process(mx_ack_sel, reg_ack, TX_EMAC_ACK)
      begin
         case mx_ack_sel is
            when '0' => mx_ack <= TX_EMAC_ACK;
            when '1' => mx_ack <= reg_ack;
            when others => mx_ack <= 'X';
         end case;
      end process;


      -- register reg_underrun
      reg_underrunp: process(RESET, CLK)
      begin
         if (RESET = '1') then
            reg_underrun <= '0';
         elsif (CLK'event AND CLK = '1') then
            if (RX_UNDERRUN = '1') then
               reg_underrun <= '1';
            elsif (CE = '1' and reg_underrun = '1') then
               reg_underrun <= '0';
            end if;
         end if;
      end process;
      underrun <= reg_underrun;

   end generate useclken_gen;

   -- Genrated only when CE is disabled
   not_useclken_gen: if USECLKEN = false generate
      fsm_ack <= TX_EMAC_ACK;
      underrun <= RX_UNDERRUN;
   end generate not_useclken_gen;


   -- FSM -----------------------------------------------------------------
   fsmi: entity work.obuf_emac_tx_fsm
      port map(
         RESET       => RESET,
         CLK         => CLK,
         CE          => CE,

         RX_DVLD     => RX_DVLD,
         EMAC_ACK    => fsm_ack,

         RX_NEXT     => fsm_next,
         TX_DVLD     => fsm_dvld
      );

   -- Statistic handling --------------------------------------------------
   -- register reg_stats
   reg_statsp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (CE = '1' AND TX_EMAC_STATSVLD = '1') then
            reg_stats(conv_integer(cnt_stats_bit)) <= TX_EMAC_STATS;
         end if;
      end if;
   end process;

   -- cnt_stats_bit counter
   cnt_stats_bitp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         cnt_stats_bit <= (others => '0');
      elsif (CLK'event AND CLK = '1' AND CE = '1') then
         if (CE = '1' AND TX_EMAC_STATSVLD = '1') then
            cnt_stats_bit <= cnt_stats_bit + 1;
         end if;
      end if;
   end process;

   -- register reg_stats_vld
   reg_stats_vldp: process(RESET, CLK)
   begin
      if (RESET = '1') then
         reg_stats_vld <= '0';
      elsif (CLK'event AND CLK = '1') then
         if (CE = '1' AND cnt_stats_bit = "11111") then
            reg_stats_vld <= '1';
         else
            reg_stats_vld <= '0';
         end if;
      end if;
   end process;

end architecture full;
