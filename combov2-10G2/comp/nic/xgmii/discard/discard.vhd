-- discard.vhd: XGMII discard unit (on packet border)
-- Copyright (C) 2010 CESNET
-- Author(s):  Jan Viktorin <xvikto03@liberouter.org>
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

use work.math_pack.ALL;
use work.xgmii_pkg.ALL; -- C_XGMII_IDLE_WORD64

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture arch of xgmii_discard is

   --+ ctrl idle signal of XGMII
   constant XGMII_IDLE_CTRL : std_logic_vector(7 downto 0) 
                                          := (others => '1');

      --+ counters of entries in fifo
--   signal cnt_pkt          : std_logic_vector();
--   signal cnt_pkt_up       : std_logic;
--   signal cnt_pkt_down     : std_logic;

   --+ comparators
   signal cmp_pkt_nonzero     : std_logic;

   --+ fifo signals
   signal fifo_discard_rd  : std_logic;
   signal fifo_discard_out : std_logic;
   signal fifo_discard_empty : std_logic;

   signal fifo_pkt_rd          : std_logic;
   signal fifo_pkt_in      : std_logic_vector(1 downto 0);
   signal fifo_pkt_out     : std_logic_vector(1 downto 0);
   signal fifo_pkt_wr      : std_logic;

   signal fifo_data_in     : std_logic_vector(64 + 8 - 1 downto 0);
   signal fifo_data_out    : std_logic_vector(64 + 8 - 1 downto 0);
   signal fifo_data_empty  : std_logic;

   signal fifo_sop_out     : std_logic;
   signal fifo_eop_out     : std_logic;
   signal fifo_txd_out     : std_logic_vector(63 downto 0);
   signal fifo_txc_out     : std_logic_vector(7 downto 0);

   signal fifo_discard_full : std_logic;
   signal fifo_pkt_full     : std_logic;
   signal fifo_data_full    : std_logic;

   signal sel_discard       : std_logic;

   signal cnt_fifo_data     : std_logic_vector(15 downto 0);
   signal cnt_fifo_data_up  : std_logic;
   signal cnt_fifo_data_dw  : std_logic;

   signal cnt_fifo_dis     : std_logic_vector(15 downto 0);
   signal cnt_fifo_dis_up  : std_logic;
   signal cnt_fifo_dis_dw  : std_logic;

begin

   assert fifo_data_full = '0'
      report "DATA FIFO is FULL"  severity error;
   assert fifo_pkt_full = '0'
      report "PKT FIFO is FULL"  severity error;
   assert fifo_discard_full = '0'
      report "DISCARD FIFO is FULL"  severity error;


-- ----------------------------------------------------------------------------
--                             Component logic
-- ----------------------------------------------------------------------------

   ---
   -- Input FSM
   ---
   input_fsm : entity work.discard_input_fsm
   port map (
      CLK   => CLK,
      RESET => RESET,

      RX_SOP   => RX_SOP,
      RX_EOP   => RX_EOP,

      FIFO_PKT_WR => fifo_pkt_wr
   );


   ---
   -- FIFO for input buffering
   ---

   -- used to store discard flag related to packets in the same order
   discard_fifo : entity work.sh_fifo
   generic map (
      FIFO_DEPTH  => max(FIFO_DEPTH, 1),
      FIFO_WIDTH  => 1
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      DIN(0)      => DISCARD,
      WE          => DISCARD_VLD,
      RE          => fifo_discard_rd,
      DOUT(0)     => fifo_discard_out,
      FULL        => fifo_discard_full,
      EMPTY       => fifo_discard_empty
   );

   -- SOP/EOP flags fifo
   pkt_fifo : entity work.sh_fifo
   generic map (
      FIFO_DEPTH  => max(FIFO_DEPTH, 1),
      FIFO_WIDTH  => 2
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      DIN         => fifo_pkt_in,
      WE          => fifo_pkt_wr,
      RE          => fifo_pkt_rd,
      DOUT        => fifo_pkt_out,
      FULL        => fifo_pkt_full,
      EMPTY       => open
   );

   -- packet data fifo
   data_fifo : entity work.sh_fifo
   generic map (
      FIFO_DEPTH  => max(FIFO_DEPTH, 1),
      FIFO_WIDTH  => 64 + 8
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      DIN         => fifo_data_in,
      WE          => fifo_pkt_wr,
      RE          => fifo_pkt_rd,
      DOUT        => fifo_data_out,
      FULL        => fifo_data_full,
      EMPTY       => fifo_data_empty
   );


   ---
   -- FIFO connections
   ---

   fifo_data_in   <= XGMII_RXD & XGMII_RXC;
   fifo_pkt_in    <= RX_EOP & RX_SOP;

   fifo_txd_out <= fifo_data_out(71 downto 8);
   fifo_txc_out <= fifo_data_out( 7 downto 0);

   fifo_sop_out   <= fifo_pkt_out(0);
   fifo_eop_out   <= fifo_pkt_out(1);


   ---
   -- Output FSM
   ---
   output_fsm : entity work.discard_output_fsm
   port map (
      CLK   => CLK,
      RESET => RESET,

      FIFO_SOP_OUT         => fifo_sop_out,
      FIFO_EOP_OUT         => fifo_eop_out,
      FIFO_DISCARD_OUT     => fifo_discard_out,
      FIFO_DISCARD_EMPTY   => fifo_discard_empty,
      FIFO_DATA_EMPTY      => fifo_data_empty,

      FIFO_RD              => fifo_pkt_rd,
      FIFO_DISCARD_RD      => fifo_discard_rd,
      SEL_DISCARD          => sel_discard
   );
   

   ---
   -- Output MUX
   ---

   XGMII_TXC <= fifo_txc_out   when sel_discard = '0'
                        else XGMII_IDLE_CTRL; 
   XGMII_TXD <= fifo_txd_out   when sel_discard = '0'
                        else C_XGMII_IDLE_WORD64;

   TX_SOP   <= fifo_sop_out   when sel_discard = '0'
               else '0';
   TX_EOP   <= fifo_eop_out   when sel_discard = '0'
               else '0';


-- ----------------------------------------------------------------------------
--                            Debugging section
-- ----------------------------------------------------------------------------


   FIFO_FULL   <= fifo_discard_full or fifo_pkt_full or
                  fifo_data_full;

   DEBUG <= cnt_fifo_data
          & cnt_fifo_dis
          & sel_discard
          & DISCARD
          & DISCARD_VLD
          & fifo_discard_out
          & fifo_sop_out
          & fifo_eop_out
          & fifo_pkt_out
          & fifo_pkt_wr
          & fifo_pkt_rd
          & fifo_discard_rd
          & fifo_discard_full 
          & fifo_pkt_full 
          & fifo_data_full;

   gen_debug_counters:
   if DEBUG_COUNTERS = true generate

      ---
      -- Counter of items in data/pkt fifo
      ---
      counter_data : process(CLK, RESET, cnt_fifo_data_up, cnt_fifo_data_dw)
         variable cnt_ce : std_logic_vector(1 downto 0);
      begin
         cnt_ce := cnt_fifo_data_up & cnt_fifo_data_dw;

         if CLK'event and CLK = '1' then
            if RESET = '1' then
               cnt_fifo_data  <= (others => '0');
            elsif cnt_ce = "10" then
               cnt_fifo_data  <= cnt_fifo_data + 1;
            elsif cnt_ce = "01" then
               cnt_fifo_data  <= cnt_fifo_data - 1;
            end if;
         end if;
      end process;

      cnt_fifo_data_up  <= fifo_pkt_wr;
      cnt_fifo_data_dw  <= fifo_pkt_rd;


      ---
      -- Counter of items in discard fifo
      ---
      counter_dis  : process(CLK, RESET, cnt_fifo_dis_up, cnt_fifo_dis_dw)
         variable cnt_ce : std_logic_vector(1 downto 0);
      begin
         cnt_ce := cnt_fifo_dis_up & cnt_fifo_dis_dw;

         if CLK'event and CLK = '1' then
            if RESET = '1' then
               cnt_fifo_dis  <= (others => '0');
            elsif cnt_ce = "10" then
               cnt_fifo_dis  <= cnt_fifo_dis + 1;
            elsif cnt_ce = "01" then
               cnt_fifo_dis  <= cnt_fifo_dis - 1;
            end if;
         end if;
      end process;

      cnt_fifo_dis_up   <= DISCARD_VLD;
      cnt_fifo_dis_dw   <= fifo_discard_rd;

   end generate;

   gen_no_debug_counters:
   if DEBUG_COUNTERS = false generate
      cnt_fifo_dis   <= (others => '1');
      cnt_fifo_data  <= (others => '1');
   end generate;




end architecture;
