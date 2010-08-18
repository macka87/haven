-- obuf_emac.vhd: Output buffer for EMAC interface - full architecture
--
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

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_emac is

   -- fl - buf signals
   signal dfifo_data   : std_logic_vector(DATA_PATHS*9-1 downto 0);
   signal dfifo_wr     : std_logic;
   signal dfifo_full   : std_logic;

   signal sfifo_data   : std_logic_vector(1 downto 0);
   signal sfifo_wr     : std_logic;
   signal sfifo_full   : std_logic;

   -- buf - tx signals
   signal buf_d           : std_logic_vector(7 downto 0);
   signal buf_dvld        : std_logic;
   signal buf_underrun    : std_logic;
   signal buf_next        : std_logic;
   signal buf_collision   : std_logic;
   signal buf_retransmit  : std_logic;
   signal buf_stats       : std_logic_vector(31 downto 0);
   signal buf_stats_vld   : std_logic;

   -- adc
   signal buf_adc_clk         : std_logic;
   signal buf_adc_do          : std_logic_vector(31 downto 0);
   signal buf_adc_drdy        : std_logic;

begin
   
   OBUF_GMII_FL_U: entity work.obuf_gmii_fl
   generic map(
      DATA_PATHS => DATA_PATHS,
      CTRL_CMD   => CTRL_CMD
   )
   port map(
      RESET       => RESET,
      CLK         => WRCLK,

      -- FrameLink input interface
      DATA       => DATA,
      DREM       => DREM,
      SRC_RDY_N  => SRC_RDY_N,
      SOF_N      => SOF_N,
      SOP_N      => SOP_N,
      EOF_N      => EOF_N,
      EOP_N      => EOP_N,
      DST_RDY_N  => DST_RDY_N,

      -- obuf_emac_buf interface
      DFIFO_DO     => dfifo_data,
      DFIFO_WR     => dfifo_wr,
      DFIFO_FULL   => dfifo_full,

      SFIFO_DO     => sfifo_data,
      SFIFO_WR     => sfifo_wr,
      SFIFO_FULL   => sfifo_full
   );

   -- ----------------------------------------------------------------------------

   OBUF_EMAC_BUF_U : entity work.obuf_emac_buf
   generic map (
      DATA_PATHS   => DATA_PATHS,

      DFIFO_SIZE   => DFIFO_SIZE,
      SFIFO_SIZE   => SFIFO_SIZE,
      CTRL_CMD     => CTRL_CMD
   )
   port map (
      RESET        => RESET,

      -- obuf_emac_cmd interface
      WR_CLK       => WRCLK,

      DFIFO_DI     => dfifo_data,
      DFIFO_WR     => dfifo_wr,
      DFIFO_FULL   => dfifo_full,
   
      SFIFO_DI     => sfifo_data,
      SFIFO_WR     => sfifo_wr,
      SFIFO_FULL   => sfifo_full,
	  
      -- obuf_emac_tx interface
      TX_CLK         => EMAC_CLK,
      TX_D           => buf_d,
      TX_DVLD        => buf_dvld,
      TX_UNDERRUN    => buf_underrun,
      TX_NEXT        => buf_next,
      TX_COLLISION   => buf_collision,
      TX_RETRANSMIT  => buf_retransmit,
      TX_STATS       => buf_stats,
      TX_STATS_VLD   => buf_stats_vld,

      -- Address decoder interface
      ADC_CLK      => buf_adc_clk,
      ADC_RD       => ADC_RD,
      ADC_WR       => ADC_WR,
      ADC_ADDR     => ADC_ADDR(3 downto 0),
      ADC_DI       => ADC_DI,
      ADC_DO       => buf_adc_do,
      ADC_DRDY     => buf_adc_drdy
   );

   -- ----------------------------------------------------------------------------

   OBUF_EMAC_TX_U : entity work.obuf_emac_tx
   generic map(
      -- EMAC#_USECLKEN generic
      USECLKEN       => USECLKEN
   )
   port map(
      -- Asynchronous reset
      RESET          => RESET,
      CLK            => EMAC_CLK,
      CE             => EMAC_CE,

      -- EMAC TX record
      TX_EMAC_D            => TX_EMAC_D,
      TX_EMAC_DVLD         => TX_EMAC_DVLD,
      TX_EMAC_ACK          => TX_EMAC_ACK,
      TX_EMAC_FIRSTBYTE    => TX_EMAC_FIRSTBYTE,
      TX_EMAC_UNDERRUN     => TX_EMAC_UNDERRUN,
      TX_EMAC_COLLISION    => TX_EMAC_COLLISION,
      TX_EMAC_RETRANSMIT   => TX_EMAC_RETRANSMIT,
      TX_EMAC_IFGDELAY     => TX_EMAC_IFGDELAY,
      TX_EMAC_STATS        => TX_EMAC_STATS,
      TX_EMAC_STATSVLD     => TX_EMAC_STATSVLD,
      TX_EMAC_STATSBYTEVLD => TX_EMAC_STATSBYTEVLD,
      TX_EMAC_SPEEDIS10100 => TX_EMAC_SPEEDIS10100,

      -- Signals from/to buffer
      RX_D           => buf_d,
      RX_DVLD        => buf_dvld,
      RX_UNDERRUN    => buf_underrun,
      RX_NEXT        => buf_next,
      RX_COLLISION   => buf_collision,
      RX_RETRANSMIT  => buf_retransmit,
      RX_STATS       => buf_stats,
      RX_STATS_VLD   => buf_stats_vld
   );

   -- ADDRESS DECODER ---------------------------------------------------------
   ADC_DO   <= buf_adc_do   when (ADC_ADDR(5 downto 4)="00") else (others=>'0');
   ADC_DRDY <= buf_adc_drdy when (ADC_ADDR(5 downto 4)="00") else '0';
   ADC_CLK  <= buf_adc_clk;

end architecture full;

