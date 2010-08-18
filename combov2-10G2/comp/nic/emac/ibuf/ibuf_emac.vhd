-- ibuf_gmii.vhd: Input buffer for Xilinx embedded Ethernet MAC
--                full architecture
--
-- Copyright (C) 2007 CESNET
-- Author(s): Libor Polcak <polcak_l@liberouter.org>
--            Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
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
use work.ibuf_emac_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of ibuf_emac is

   -- RX output
   signal buf_data         : std_logic_vector(7 downto 0);
   signal buf_dv           : std_logic;
   signal sop_i            : std_logic;
   signal eop_i            : std_logic;
   signal buf_frame_sent   : std_logic;
   signal buf_frame_err    : std_logic;
   signal rx_stat          : t_ibuf_emac_rx_stat;
   signal rx_stat_dv       : std_logic;
   signal rx_crc_error     : std_logic;
   signal rx_crc_err_dv    : std_logic;

   -- BUF signals
   signal dfifo_data       : std_logic_vector(DATA_PATHS*8-1 downto 0);
   signal dfifo_rem        : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal dfifo_sop_n      : std_logic;
   signal dfifo_eop_n      : std_logic;
   signal dfifo_src_rdy_n  : std_logic;
   signal dfifo_dst_rdy_n  : std_logic;

   signal hfifo_data       : std_logic_vector(DATA_PATHS*8-1 downto 0);
   signal hfifo_rem        : std_logic_vector(log2(DATA_PATHS)-1 downto 0);
   signal hfifo_sop_n      : std_logic;
   signal hfifo_eop_n      : std_logic;
   signal hfifo_src_rdy_n  : std_logic;
   signal hfifo_dst_rdy_n  : std_logic;

   -- MAC_check signals
   signal en               : std_logic;
   signal mac_in           : std_logic_vector(47 downto 0);
   signal check            : std_logic;
   signal check_fin        : std_logic;
   signal mac_match        : std_logic;
   signal multicast        : std_logic;
   signal broadcast        : std_logic;

   -- adc
   signal buf_adc_clk      : std_logic;
   signal buf_adc_rd       : std_logic;
   signal buf_adc_wr       : std_logic;
   signal buf_adc_do       : std_logic_vector(31 downto 0);
   signal buf_adc_drdy     : std_logic;
   signal mac_adc_rd       : std_logic;
   signal mac_adc_wr       : std_logic;
   signal mac_adc_clk      : std_logic;
   signal mac_adc_do       : std_logic_vector(31 downto 0);
   signal mac_adc_drdy     : std_logic;

begin

   -- -------------------------------------------------------------------------
   --                           RX part instantion
   -- -------------------------------------------------------------------------
   RXi: entity work.ibuf_emac_rx
      generic map (
	 INBANDFCS	=> INBANDFCS
      )
      port map(
         -- Input common signals
         CLK            => RXCLK,
         RESET          => RESET,
         CE             => RXCE,
   
         -- Input data
         DI             => RXD,
         DI_DV          => RXDV,
   
         -- EMAC signals that separate packets, active in '1'
         GOOD_FRAME     => RXGOODFRAME,
         BAD_FRAME      => RXBADFRAME,
   
         -- EMAC statistic data
         RX_STAT        => RXSTATS,
         RX_STAT_VLD    => RXSTATSVLD,

         -- Output data
         DO             => buf_data,
         DO_DV          => buf_dv,
   
         -- Packet control
         SOP            => sop_i,
         EOP            => eop_i,
         FRAME_SENT     => buf_frame_sent,
         FRAME_ERR      => buf_frame_err,
   
         -- Statistic data
         TX_STAT        => rx_stat,
         TX_STAT_VLD    => rx_stat_dv,
         CRC_ERROR      => rx_crc_error,
         CRC_ERROR_VLD  => rx_crc_err_dv
      );

   -- -------------------------------------------------------------------------
   --                          BUF part instantion
   -- -------------------------------------------------------------------------
   BUFi: entity work.ibuf_emac_buf
      generic map(
         DATA_PATHS  		=> DATA_PATHS,
         DFIFO_SIZE  		=> DFIFO_SIZE,
         HFIFO_SIZE  		=> HFIFO_SIZE,
         HFIFO_DISTMEMTYPE     	=> HFIFO_DISTMEMTYPE,
	 INBANDFCS		=> INBANDFCS
      )
      port map(
         RESET       		=> RESET,

         -- ibuf_emac_rx interface
         WRCLK       		=> RXCLK,
         DI          		=> buf_data,
         DI_DV       		=> buf_dv,
         SOP         		=> sop_i,
         EOP         		=> eop_i,
         FRAME_ERR   		=> buf_frame_err,
         RX_STAT     		=> rx_stat,
	 RX_STAT_DV		=> rx_stat_dv,

         -- Debug interface
         FSM_RX_STATE		=> "000",

         -- PACODAG interface
         CTRL_DI       		=> CTRL_DI,
         CTRL_REM       	=> CTRL_REM,
         CTRL_SRC_RDY_N 	=> CTRL_SRC_RDY_N,
         CTRL_SOP_N     	=> CTRL_SOP_N,
         CTRL_EOP_N     	=> CTRL_EOP_N,
         CTRL_DST_RDY_N 	=> CTRL_DST_RDY_N,
         CTRL_SOP               => SOP,
         CTRL_RDY               => CTRL_RDY,
         CTRL_STAT              => STAT,
         CTRL_STAT_DV           => STAT_DV,

         -- MAC check interface
         EN          		=> en,
         MAC_IN      		=> mac_in,
         CHECK       		=> check,
         CHECK_FIN   		=> check_fin,
         MAC_MATCH   		=> mac_match,
         MULTICAST   		=> multicast,
         BROADCAST   		=> broadcast,

         -- sampling unit interface
         SAU_ACCEPT  		=> SAU_ACCEPT,
         SAU_DV      		=> SAU_DV,
         SAU_REQ           => SAU_REQ,

         -- FL interface
         RDCLK       		=> RDCLK,

         -- Payload
         -- Data
         TX_DATA        	=> dfifo_data,
         -- Position of the end of the part, valid only if TX_EOP_N is set
			-- to '0'.
         TX_REM         	=> dfifo_rem,
         -- Start of the part, active in '0'
         TX_SOP_N       	=> dfifo_sop_n,
         -- End of the packet, active in '0'.
         TX_EOP_N       	=> dfifo_eop_n,
         -- Source is ready, active in '0'
         TX_SRC_RDY_N   	=> dfifo_src_rdy_n,
         -- Destination is ready, active in '0'
         TX_DST_RDY_N   	=> dfifo_dst_rdy_n,

         -- Packet headres/footers
         -- Part data
         TX_HDATA       	=> hfifo_data,
         -- Position of the end of the part, valid only if TX_HEOP_N is set
			-- to '0'.
         TX_HREM        	=> hfifo_rem,
         -- Start of the part, active in '0'
         TX_HSOP_N      	=> hfifo_sop_n,
         -- End of the packet, active in '0'.
         TX_HEOP_N      	=> hfifo_eop_n,
         -- Source is ready, active in '0'
         TX_HSRC_RDY_N  	=> hfifo_src_rdy_n,
         -- Destination is ready, active in '0'
         TX_HDST_RDY_N  	=> hfifo_dst_rdy_n,

         -- Address decoder interface
         ADC_CLK        	=> buf_adc_clk,
         ADC_RD         	=> buf_adc_rd,
         ADC_WR         	=> buf_adc_wr,
         ADC_ADDR       	=> ADC_ADDR(3 downto 0),
         ADC_DI         	=> ADC_DI,
         ADC_BE                 => ADC_BE,
         ADC_DO         	=> buf_adc_do,
         ADC_DRDY       	=> buf_adc_drdy
      );
      
   -- -------------------------------------------------------------------------
   --                        MAC_CHECK part instantion
   -- -------------------------------------------------------------------------
   MAC_CHECKi: entity work.mac_check
      generic map (
         MACS  => MACS   -- Number of MACs to compare
      )
      port map(
         -- Common Input
         RESET    	=> RESET,
         CLK      	=> RXCLK,
         EN       	=> en,

         -- MAC address input
         MAC_IN   	=> mac_in,
         CHECK    	=> check,

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

   -- -------------------------------------------------------------------------
   --                           FL part instantion
   -- -------------------------------------------------------------------------
   FLi: entity work.fl_composer
      generic map(
         CTRL_HDR_EN	=> CTRL_HDR_EN,	-- Enables frame headers
         CTRL_FTR_EN => CTRL_FTR_EN,	-- Enables frame footers
         FL_WIDTH_TX => DATA_PATHS*8,	-- FrameLink width
         FL_RELAY    => false				-- Put FL Relay to the output
      )
      port map(
         -- Common signals
         CLK            => RDCLK,   -- Clock sigal
         RESET          => RESET,   -- Asynchronous reset, active in '1'

         -- Input
         -- Payload
         -- Data
         RX_DATA        => dfifo_data,
         -- Position of the end of the part, valid only if RX_EOP_N is set
			-- to '0'.
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
         -- Position of the end of the part, valid only if RX_HEOP_N is set
			-- to '0'.
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
   CTRL_CLK    <= RXCLK;
   CTRL_RESET  <= RESET;

   -- ADDRESS DECODER ---------------------------------------------------------
   adc_p: process (ADC_ADDR, ADC_RD, ADC_WR, buf_adc_drdy, buf_adc_do,
						 mac_adc_drdy, mac_adc_do)
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
