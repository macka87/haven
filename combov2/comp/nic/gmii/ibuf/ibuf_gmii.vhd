--
-- ibuf_gmii.vhd: Input buffer for gmii interface - full architecture
--
-- Copyright (C) 2005 CESNET
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
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

use work.math_pack.all;
use work.ibuf_pkg.all;
use work.ibuf_general_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_gmii is
   signal buf_data : std_logic_vector(7 downto 0);
   signal buf_dv   : std_logic;

   -- Synchronous reset signals
   signal rx_reset : std_logic;
   signal rd_reset : std_logic;

   -- RX status signals and sample register
   signal rx_stat      : t_ibuf_rx_stat;
   signal sop_i        : std_logic;
   signal eop_i        : std_logic;

   -- Debug signals
   signal fsm_rx_state : std_logic_vector(2 downto 0);
--   signal fsm_fl_state : std_logic_vector(2 downto 0);

   -- temporary speed signal (speed driven by software yet)
   signal speed_i      : std_logic_vector(1 downto 0);
   

   -- BUF signals
   signal dfifo_data    : std_logic_vector(DATA_PATHS*8-1 downto 0);
   signal dfifo_rem     : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal dfifo_sop_n   : std_logic;
   signal dfifo_eop_n   : std_logic;
   signal dfifo_src_rdy_n  : std_logic;
   signal dfifo_dst_rdy_n  : std_logic;

   signal hfifo_data    : std_logic_vector(DATA_PATHS*8-1 downto 0);
   signal hfifo_rem     : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal hfifo_sop_n   : std_logic;
   signal hfifo_eop_n   : std_logic;
   signal hfifo_src_rdy_n  : std_logic;
   signal hfifo_dst_rdy_n  : std_logic;

   -- MAC_check signals
   signal en            : std_logic;
   signal mac_in        : std_logic_vector(47 downto 0);
   signal check         : std_logic;
   signal check_fin     : std_logic;
   signal mac_match     : std_logic;
   signal multicast     : std_logic;
   signal broadcast     : std_logic;

   -- adc ----------------------------------------------------
   signal buf_adc_clk         : std_logic;
   signal buf_adc_rd          : std_logic;
   signal buf_adc_wr          : std_logic;
   signal buf_adc_do          : std_logic_vector(31 downto 0);
   signal buf_adc_drdy        : std_logic;
   signal mac_adc_rd          : std_logic;
   signal mac_adc_wr          : std_logic;
   signal mac_adc_clk         : std_logic;
   signal mac_adc_do          : std_logic_vector(31 downto 0);
   signal mac_adc_drdy        : std_logic;

   signal reg_buf_data : std_logic_vector(7 downto 0);
   signal reg_buf_dv : std_logic;
   signal reg_rx_stat_i  : t_ibuf_rx_stat;
   signal reg_sop_i  : std_logic;
   signal reg_eop_i  : std_logic;
begin

   -- Reset generator for the input part
   rx_resetp: process(RXCLK)
   begin
      if (RXCLK'event AND RXCLK = '1') then
         if (RESET = '1') then
            rx_reset <= '1';
         else
            rx_reset <= '0';
         end if;
      end if;
   end process;

   -- Reset generator for the output part
   rd_resetp: process(RDCLK)
   begin
      if (RDCLK'event AND RDCLK = '1') then
         if (RESET = '1') then
            rd_reset <= '1';
         else
            rd_reset <= '0';
         end if;
      end if;
   end process;


   rx_u : entity work.ibuf_gmii_rx
   generic map(
      INBANDFCS   => INBANDFCS
   )
   port map(
      RESET   => rx_reset,

      -- RX gmii interface
      RXCLK   => RXCLK,
      RXD     => RXD,
      RXDV    => RXDV,
      RXER    => RXER,

      -- PHY status interface. PHY speed is driven by software yet via command register in ibuf_buf.
      LINK_STATUS       => '1',
      DUPLEX_MODE       => '1',
      SPEED             => speed_i,
      SGMII             => '1',

      -- buffer interface
      DO      => buf_data,
      DO_DV   => buf_dv,
      STAT    => rx_stat,
      SOP     => sop_i,
      EOP     => eop_i,
      FSM_STATE   => fsm_rx_state
   );

   
process(RXCLK)
begin
   if (RXCLK'event AND RXCLK = '1') then
      if (rx_reset = '1') then
         reg_buf_data <= (others => '0');
         reg_buf_dv <= '0';
         reg_rx_stat_i.GMII_ERROR <= '0';
         reg_rx_stat_i.CRC_CHECK_FAILED <= '0';
         reg_rx_stat_i.FRAME_LEN <= (others => '0');
         reg_sop_i  <= '0';
         reg_eop_i  <= '0';
      else
         reg_buf_data <= buf_data;
         reg_buf_dv <= buf_dv;
         reg_rx_stat_i  <= rx_stat;
         reg_sop_i  <= sop_i;
         reg_eop_i  <= eop_i;
      end if;
   end if;
end process;


mac_check_u: entity work.mac_check
   generic map (
      MACS  => MACS   -- Number of MACs to compare
   )
   port map(
      -- Common Input
      RESET    => rx_reset,
      CLK      => RXCLK,
      EN       => en,

      -- MAC address input
      MAC_IN   => mac_in,
      CHECK    => check,

      -- Result output
      CHECK_FIN   => check_fin,
      MAC_MATCH   => mac_match,
      MULTICAST   => multicast,
      BROADCAST   => broadcast,

      -- Address decoder interface
      ADC_CLK     => buf_adc_clk,
      ADC_RD      => mac_adc_rd,
      ADC_WR      => mac_adc_wr,
      ADC_ADDR    => ADC_ADDR(log2(MACS) downto 0),
      ADC_DI      => ADC_DI,
      ADC_DO      => mac_adc_do,
      ADC_DRDY    => mac_adc_drdy
   );

buf_u : entity work.ibuf_gmii_buf
   generic map(
      DATA_PATHS  => DATA_PATHS,
      DFIFO_SIZE  => DFIFO_SIZE,
      HFIFO_SIZE  => HFIFO_SIZE
   )
   port map(
      RESET   => rx_reset,

      -- ibuf_gmii_rx interface
      WRCLK       => RXCLK,
      DI          => reg_buf_data,
      DI_DV       => reg_buf_dv,
      RX_STAT     => reg_rx_stat_i,
      SOP         => reg_sop_i,
      EOP         => reg_eop_i,
      SPEED       => speed_i,

      -- Debug interface
      FSM_RX_STATE => fsm_rx_state,
      --FSM_FL_STATE => fsm_fl_state,

      -- PACODAG interface
      CTRL_DI        => CTRL_DI,
      CTRL_REM       => CTRL_REM,
      CTRL_SRC_RDY_N => CTRL_SRC_RDY_N,
      CTRL_SOP_N     => CTRL_SOP_N,
      CTRL_EOP_N     => CTRL_EOP_N,
      CTRL_DST_RDY_N => CTRL_DST_RDY_N,
      CTRL_SOP       => SOP,
      CTRL_RDY       => CTRL_RDY,
      CTRL_STAT      => STAT,
      CTRL_STAT_DV   => STAT_DV,

      -- MAC check interface
      EN          => en,
      MAC_IN      => mac_in,
      CHECK       => check,
      CHECK_FIN   => check_fin,
      MAC_MATCH   => mac_match,
      MULTICAST   => multicast,
      BROADCAST   => broadcast,

      -- FrameLink interface
      RDCLK       => RDCLK,

      -- Payload
      -- Data
      TX_DATA        => dfifo_data,
      -- Position of the end of the part, valid only if TX_EOP_N is set to '0'.
      TX_REM         => dfifo_rem,
      -- Start of the part, active in '0'
      TX_SOP_N       => dfifo_sop_n,
      -- End of the packet, active in '0'.
      TX_EOP_N       => dfifo_eop_n,
      -- Source is ready, active in '0'
      TX_SRC_RDY_N   => dfifo_src_rdy_n,
      -- Destination is ready, active in '0'
      TX_DST_RDY_N   => dfifo_dst_rdy_n,

      -- Packet headres/footers
      -- Part data
      TX_HDATA       => hfifo_data,
      -- Position of the end of the part, valid only if TX_HEOP_N is set to '0'.
      TX_HREM        => hfifo_rem,
      -- Start of the part, active in '0'
      TX_HSOP_N      => hfifo_sop_n,
      -- End of the packet, active in '0'.
      TX_HEOP_N      => hfifo_eop_n,
      -- Source is ready, active in '0'
      TX_HSRC_RDY_N  => hfifo_src_rdy_n,
      -- Destination is ready, active in '0'
      TX_HDST_RDY_N  => hfifo_dst_rdy_n,

      SAU_ACCEPT  => SAU_ACCEPT,
      SAU_DV      => SAU_DV,

      ADC_CLK     => buf_adc_clk,
      ADC_RD      => buf_adc_rd,
      ADC_WR      => buf_adc_wr,
      ADC_ADDR    => ADC_ADDR(3 downto 0),
      ADC_DI      => ADC_DI,
      ADC_DO      => buf_adc_do,
      ADC_DRDY    => buf_adc_drdy
   );

   fl_u: entity work.fl_composer
      generic map (
         -- Enables frame headers
         CTRL_HDR_EN       => CTRL_HDR_EN,
         -- Enables frame footers
         CTRL_FTR_EN       => CTRL_FTR_EN,
          -- FrameLink width
         FL_WIDTH_TX       => DATA_PATHS * 8,
         -- Put FL Relay to the output
         FL_RELAY          => false
      )
      port map (
         -- Common signals
         -- Clock sigal
         CLK               => RDCLK,
         -- Asynchronous reset, active in '1'
         RESET             => RESET,

         -- Input
         -- Payload
         -- Data
         RX_DATA        => dfifo_data,
         -- Position of the end of the part, valid only if RX_EOP_N is set to '0'.
         RX_REM         => dfifo_rem,
         -- Start of the part, active in '0'
         RX_SOP_N       => dfifo_sop_n,
         -- End of the packet, active in '0'.
         RX_EOP_N       => dfifo_eop_n,
         -- Source is ready, active in '0'
         RX_SRC_RDY_N   => dfifo_src_rdy_n,
         -- Destination is ready, active in '0'
         RX_DST_RDY_N   => dfifo_dst_rdy_n,

         -- Packet headres/footers
         -- Part data
         RX_HDATA       => hfifo_data,
         -- Position of the end of the part, valid only if RX_HEOP_N is set to '0'.
         RX_HREM        => hfifo_rem,
         -- Start of the part, active in '0'
         RX_HSOP_N      => hfifo_sop_n,
         -- End of the packet, active in '0'.
         RX_HEOP_N      => hfifo_eop_n,
         -- Source is ready, active in '0'
         RX_HSRC_RDY_N  => hfifo_src_rdy_n,
         -- Destination is ready, active in '0'
         RX_HDST_RDY_N  => hfifo_dst_rdy_n,

         -- Output FrameLink
         TX_DATA        => DATA,
         TX_REM         => DREM,
         TX_SOF_N       => SOF_N,
         TX_SOP_N       => SOP_N,
         TX_EOP_N       => EOP_N,
         TX_EOF_N       => EOF_N,
         TX_SRC_RDY_N   => SRC_RDY_N,
         TX_DST_RDY_N   => DST_RDY_N
      );


   -- STATUS PORT -------------------------------------------------------------
   CTRL_CLK <= RXCLK;


   -- ADDRESS DECODER ---------------------------------------------------------
   adc_p: process (ADC_ADDR, ADC_RD, ADC_WR, buf_adc_drdy, buf_adc_do, mac_adc_drdy, mac_adc_do)
   begin
      buf_adc_rd <= '0';
      buf_adc_wr <= '0';
      mac_adc_rd <= '0';
      mac_adc_wr <= '0';
      ADC_DRDY   <= '0';
      ADC_DO     <= (others => '0');

      if (ADC_ADDR(5 downto 4) = "00") then
         buf_adc_rd <= ADC_RD;
         buf_adc_wr <= ADC_WR;
         ADC_DRDY   <= buf_adc_drdy;
         ADC_DO     <= buf_adc_do;
      elsif (ADC_ADDR(5 downto 4) = "10") then
         mac_adc_rd <= ADC_RD;
         mac_adc_wr <= ADC_WR;
         ADC_DRDY   <= mac_adc_drdy;
         ADC_DO     <= mac_adc_do;
      elsif (ADC_ADDR(5 downto 4) = "11") then
         mac_adc_rd <= ADC_RD;
         mac_adc_wr <= ADC_WR;
         ADC_DRDY   <= mac_adc_drdy;
         ADC_DO     <= mac_adc_do;
      end if;
   end process;

   ADC_CLK  <= buf_adc_clk;

end architecture full;

