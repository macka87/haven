--
-- obuf_xgmii.vhd: XGMII Output Buffer
-- Copyright (C) 2008 CESNET
-- Author(s): Polcak Libor <polcak_l@liberouter.org>
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
-- TODO: use appropriate reset for every clock domain
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use work.math_pack.all;
use work.xgmii_obuf_pkg.all;
use work.fifo_pkg.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture obuf_xgmii_sdr_norec_arch of obuf_xgmii_sdr_norec is

   -- internal signals
   signal reset_int        : std_logic;

   -- buf input data
   signal buf_data         : std_logic_vector(FL_WIDTH_RX-1 downto 0);
   signal buf_sop_n        : std_logic;
   signal buf_eop_n        : std_logic;
   signal buf_eop_pos      : std_logic_vector(log2(FL_WIDTH_RX/8)-1 downto 0);
   signal buf_wr           : std_logic;
   signal buf_mark         : std_logic;
   signal buf_dfifo_full   : std_logic;
   signal buf_dfifo_ovf    : std_logic;
   signal buf_hdata        : std_logic_vector(C_FTR_MAX_BIT downto 0);
   signal buf_hfifo_wr     : std_logic;
   signal buf_hfifo_full   : std_logic;

   -- process input signals
   signal proc_data              : std_logic_vector(63 downto 0);
   signal proc_sop               : std_logic;
   signal proc_eop               : std_logic;
   signal proc_eop_pos           : std_logic_vector(2 downto 0);
   signal proc_dv                : std_logic;
   signal proc_src_mac_rplc      : std_logic;
   signal proc_next_src_mac_rplc : std_logic;
   signal proc_rx_dst_rdy        : std_logic;
   signal proc_mac_addr          : std_logic_vector(47 downto 0);
   
   -- process output signal
   signal proc_tx_crc_dv         : std_logic;
   signal proc_tx_crc            : std_logic_vector(31 downto 0);

   -- xgmii_enc input signals
   signal xgmii_enc_data         : std_logic_vector(63 downto 0);
   signal xgmii_enc_sop          : std_logic;
   signal xgmii_enc_eop          : std_logic;
   signal xgmii_enc_eop_pos      : std_logic_vector(2 downto 0);
   signal xgmii_enc_dv           : std_logic;
   signal xgmii_enc_data_read    : std_logic;
   signal xgmii_enc_crc          : std_logic_vector(31 downto 0);


   signal reg_outgoing_pckt      : std_logic;

begin


   -- -----------------------------------------------------------------
   --                           FL Part
   -- -----------------------------------------------------------------

   -- Fl instantion
   FLi: entity work.obuf_xgmii_fl
      generic map(
         -- Frames contain control part
         CTRL_CMD          => CTRL_CMD,
         -- FrameLink width
         DATA_WIDTH        => FL_WIDTH_RX
      )
      port map(
         -- Clock signal
         CLK               => FL_CLK,
         -- Synchronous reset
         RESET             => RESET_FL,

         -- Input FrameLink interface
         RX_DATA           => RX_DATA,
         RX_REM            => RX_REM,
         RX_SOF_N          => RX_SOF_N,
         RX_SOP_N          => RX_SOP_N,
         RX_EOP_N          => RX_EOP_N,
         RX_EOF_N          => RX_EOF_N,
         RX_SRC_RDY_N      => RX_SRC_RDY_N,
         RX_DST_RDY_N      => RX_DST_RDY_N,

         -- Output DFIFO interface
         TX_DATA           => buf_data,
         TX_SOP_N          => buf_sop_n,
         TX_EOP_N          => buf_eop_n,
         TX_EOP_POS        => buf_eop_pos,
         TX_WR             => buf_wr,
         TX_MARK           => buf_mark,
         TX_DFIFO_FULL     => buf_dfifo_full,
         TX_DFIFO_OVF      => buf_dfifo_ovf,

         -- Output HFIFO interface
         TX_HDATA          => buf_hdata,
         TX_HFIFO_WR       => buf_hfifo_wr,
         TX_HFIFO_FULL     => buf_hfifo_full
      );


   -- -----------------------------------------------------------------
   --                           Buf Part
   -- -----------------------------------------------------------------

   -- Buf instantion
   BUFi: entity work.obuf_xgmii_buf
      generic map(
         -- FrameLink width
         DATA_WIDTH        => FL_WIDTH_RX,
         -- DFIFO item count (DATA_WIDTH wide)
         DFIFO_SIZE        => DFIFO_SIZE,
         -- HFIFO item count (1-bit wide)
         HFIFO_SIZE        => HFIFO_SIZE,
         -- Type of memory used by HFIFO
         HFIFO_MEMTYPE     => HFIFO_MEMTYPE
      )

      port map(
         -- FrameLink Clock signal
         FL_CLK            => FL_CLK,
         -- FrameLink synchronous reset
         RESET_FL          => RESET_FL,
         -- Output XGMII Clock signal
         XGMII_CLK         => CLK_INT,
         -- XGMII synchronous reset
         RESET_XGMII       => reset_int,

         -- DFIFO input interface
         RX_DATA           => buf_data,
         RX_SOP_N          => buf_sop_n,
         RX_EOP_N          => buf_eop_n,
         RX_EOP_POS        => buf_eop_pos,
         RX_WR             => buf_wr,
         RX_MARK           => buf_mark,
         RX_DFIFO_FULL     => buf_dfifo_full,
         RX_DFIFO_OVF      => buf_dfifo_ovf,
         -- HFIFO input interface
         RX_HDATA          => buf_hdata,
         RX_HFIFO_WR       => buf_hfifo_wr,
         RX_HFIFO_FULL     => buf_hfifo_full,
         -- Process interface
         TX_DATA           => proc_data,
         TX_SOP            => proc_sop,
         TX_EOP            => proc_eop,
         TX_EOP_POS        => proc_eop_pos,
         TX_DV             => proc_dv,
         -- '1' Replace source MAC address, '0' keep the one present in frame
         SRC_MAC_RPLC      => proc_src_mac_rplc,
         -- Send next SRC_MAC_RPLC, active in '1'
         NEXT_SRC_MAC_RPLC => proc_next_src_mac_rplc,
         -- Destination is ready, active in '1'
         TX_DST_RDY        => proc_rx_dst_rdy,
         -- MAC address register (MSB is byte 47 downto 40)
         -- http://en.wikipedia.org/wiki/MAC_Address
         REG_MAC_ADDR      => proc_mac_addr,

         -- OBUF MI32 interface
         MI_DWR      	   => MI_DWR,
         MI_ADDR     	   => MI_ADDR,
         MI_RD       	   => MI_RD,
         MI_WR       	   => MI_WR,
         MI_BE       	   => MI_BE,
         MI_DRD      	   => MI_DRD,
         MI_ARDY     	   => MI_ARDY,
         MI_DRDY     	   => MI_DRDY,
         MI_CLK            => MI_CLK,
         -- MI synchronous reset
         RESET_MI          => RESET_MI
      );


   -- -----------------------------------------------------------------
   --                         Process Part
   -- -----------------------------------------------------------------

   -- Process instantion
   PROCESSi: entity work.obuf_xgmii_process
      port map(
         -- Clock signal
         CLK               => CLK_INT,
         -- Synchronous reset
         RESET             => reset_int,

         -- Process inputs
         RX_DATA           => proc_data,
         RX_SOP            => proc_sop,
         RX_EOP            => proc_eop,
         RX_EOP_POS        => proc_eop_pos,
         RX_DV             => proc_dv,

         -- Reading requests from FIFOs by XGMII_ENC
         TX_DATA_READ      => xgmii_enc_data_read,

         -- Process outputs
         TX_DATA           => xgmii_enc_data,
         TX_SOP            => xgmii_enc_sop,
         TX_EOP            => xgmii_enc_eop,
         TX_EOP_POS        => xgmii_enc_eop_pos,
         TX_DV             => xgmii_enc_dv,
         TX_CRC            => proc_tx_crc,
         TX_CRC_DV         => proc_tx_crc_dv,

         -- '1' Replace source MAC address, '0' keep the one present in frame
         SRC_MAC_RPLC      => proc_src_mac_rplc,

         -- new source MAC address register (in case of it's  replace)
         REG_MAC_ADDR      => proc_mac_addr,

         -- Send next SRC_MAC_RPLC, active in '1'
         NEXT_SRC_MAC_RPLC => proc_next_src_mac_rplc,

         -- Process part of OBUF is ready for processing data, active in '1'
         RX_DST_RDY        => proc_rx_dst_rdy
      );

   reg_xgmii_enc_crcp: process(CLK_INT)
   begin
      if (CLK_INT'event and CLK_INT = '1') then
         if proc_tx_crc_dv = '1' then
            xgmii_enc_crc <= proc_tx_crc;
         end if;
      end if;
   end process;

   XGMII_ENCi: entity work.xgmii_obuf_xgmii_enc
      port map(
         -- Clock signal
         CLK               => CLK_INT,
         -- Synchronous reset
         RESET             => reset_int,
         ----- XGMII_enc inputs -----
         -- data
         RX_DATA           => xgmii_enc_data,
         -- data control signals
         RX_SOP            => xgmii_enc_sop,
         RX_EOP            => xgmii_enc_eop,
         RX_EOP_POS        => xgmii_enc_eop_pos,
         RX_DV             => xgmii_enc_dv,
         -- CRC
         RX_CRC            => xgmii_enc_crc,
         ----- XGMII_enc outputs -----
         TX_DATA           => XGMII_SDR_TXD,
         TX_CMD            => XGMII_SDR_TXC,
         -- reading requsts to Process part
         RX_DATA_READ      => xgmii_enc_data_read
      );

   reg_outgoing_pcktp: process(reset_int, CLK_INT)
   begin
      if (CLK_INT'event and CLK_INT = '1') then
         if (reset_int = '1') then
            reg_outgoing_pckt <= '0';
         elsif (proc_eop = '1' and proc_dv = '1') then
            reg_outgoing_pckt <= '0';
         elsif (proc_sop = '1' and proc_dv = '1') then
            reg_outgoing_pckt <= '1';
         end if;
      end if;
   end process;

   OUTGOING_PCKT <= reg_outgoing_pckt;

   -- FIXME: use appropriate reset for every clock domain
   reset_int <= RESET_XGMII;

end architecture;
-- ----------------------------------------------------------------------------
