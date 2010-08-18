--
-- obuf_gmii.vhd: Output buffer for gmii interface - full architecture
--
-- Copyright (C) 2005 CESNET
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
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of obuf_gmii is

   -- fl - buf signals
   signal dfifo_data   : std_logic_vector(DATA_PATHS*9-1 downto 0);
   signal dfifo_wr     : std_logic;
   signal dfifo_full   : std_logic;

   signal sfifo_data   : std_logic_vector(1 downto 0);
   signal sfifo_wr     : std_logic;
   signal sfifo_full   : std_logic;

   -- buf - tx signals
   signal tx_data      : std_logic_vector(7 downto 0);
   signal tx_dv        : std_logic;
   signal tx_er        : std_logic;
   signal tx_busy      : std_logic;
   signal sgmii_dv     : std_logic;

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

      -- obuf_gmii_buf interface
      DFIFO_DO     => dfifo_data,
      DFIFO_WR     => dfifo_wr,
      DFIFO_FULL   => dfifo_full,

      SFIFO_DO     => sfifo_data,
      SFIFO_WR     => sfifo_wr,
      SFIFO_FULL   => sfifo_full
   );

   -- ----------------------------------------------------------------------------

   OBUF_GMII_BUF_U : entity work.obuf_gmii_buf
   generic map (
      --ADDR_BASE    => ADDR_BASE,
      --ADDR_WIDTH   => ADDR_WIDTH,
      
      DATA_PATHS   => DATA_PATHS,

      DFIFO_SIZE   => DFIFO_SIZE,
      SFIFO_SIZE   => SFIFO_SIZE,
      CTRL_CMD     => CTRL_CMD
   )
   port map (
      RESET        => RESET,

      -- obuf_gmii_cmd interface
      WR_CLK       => WRCLK,

      DFIFO_DI     => dfifo_data,
      DFIFO_WR     => dfifo_wr,
      DFIFO_FULL   => dfifo_full,
   
      SFIFO_DI     => sfifo_data,
      SFIFO_WR     => sfifo_wr,
      SFIFO_FULL   => sfifo_full,
	  
      -- obuf_gmii_tx interface
      TX_CLK       => REFCLK,
      TX_DO        => tx_data,
      TX_DV        => tx_dv,
      TX_ER        => tx_er,
      TX_BUSY      => tx_busy,
      SGMII_DV_P   => sgmii_dv,

      -- PHY status interface
      LINK_STATUS       => '1',
      DUPLEX_MODE       => '1',
      SPEED             => "10", -- irrelevant, speed is driven by command register
      SGMII             => '1',

      ADC_CLK      => buf_adc_clk,
      ADC_RD       => ADC_RD,
      ADC_WR       => ADC_WR,
      ADC_ADDR     => ADC_ADDR(3 downto 0),
      ADC_DI       => ADC_DI,
      ADC_DO       => buf_adc_do,
      ADC_DRDY     => buf_adc_drdy
   );

   -- ----------------------------------------------------------------------------

   OBUF_GMII_TX_U : entity work.obuf_gmii_tx
   generic map(
      INBANDFCS   => INBANDFCS,
      SKIP_FCS    => SKIP_FCS
   )
   port map(
      RESET  => RESET,
      REFCLK => REFCLK,

      -- obuf_gmii_buf interface
      DI     => tx_data,
      DI_DV  => tx_dv,
      DI_ER  => tx_er,
      BUSY   => tx_busy,
      SGMII_DV => sgmii_dv,

      -- TX gmii interface
      TXCLK  => TXCLK,
      TXD    => TXD,
      TXEN   => TXEN,
      TXER   => TXER
   );

   -- ADDRESS DECODER ---------------------------------------------------------
   ADC_DO   <= buf_adc_do   when (ADC_ADDR(5 downto 4)="00") else (others=>'0');
   ADC_DRDY <= buf_adc_drdy when (ADC_ADDR(5 downto 4)="00") else '0';
   ADC_CLK  <= buf_adc_clk;

end architecture full;

